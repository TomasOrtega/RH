import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitFactorIdem

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

section Quad

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `hli : LinearIndependent F ![(1 : E), a]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Distinguish the cases in `ht : t = 0`.

Substitute `ht` using the available equality. Simplify using `only [map_zero, zero_mul, add_zero] at hst`. Conclude with `⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩`. It suffices to derive a contradiction. Apply `ha` to reduce the goal to its premises.

Establish `ht' : algebraMap F E t ≠ 0` using `(map_ne_zero _).2 ht`. Use `⟨-(s / t), ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, map_div₀]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-1 : E) * hst`.

Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`. Use `⟨b.repr x 0, b.repr x 1, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr x]`. Simplify using `[Fin.sum_univ_two, b, Algebra.algebraMap_eq_smul_one]`.
-/
theorem exists_coord (h2 : Module.finrank F E = 2) {a : E}
    (ha : a ∉ Set.range (algebraMap F E)) (x : E) :
    ∃ u v : F, x = algebraMap F E u + v • a := by
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [map_zero, zero_mul, add_zero] at hst
      exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩
    · exfalso
      apply ha
      have ht' : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      refine ⟨-(s / t), ?_⟩
      rw [map_neg, map_div₀]
      field_simp
      linear_combination (-1 : E) * hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  simp [Fin.sum_univ_two, b, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Assume the negation of the conclusion as `hx'`. Take `⟨e, he⟩` from `hq.ne_id`. Take `⟨u, v, rfl⟩` from `exists_coord hq.finrank_eq hx' e`. Apply `he` to reduce the goal to its premises. Rewrite using `[map_add, AlgHom.commutes, map_smul, hx]`.
-/
theorem fixed_mem {σ : E →ₐ[F] E} (hq : IsQuadInvol F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  by_contra hx'
  obtain ⟨e, he⟩ := hq.ne_id
  obtain ⟨u, v, rfl⟩ := exists_coord hq.finrank_eq hx' e
  apply he
  rw [map_add, AlgHom.commutes, map_smul, hx]

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Apply `hK` to reduce the goal to its premises. Use `haveI : Nontrivial (K ⊗[F] E) := (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := K) (B := E) (algebraMap F E).injective).nontrivial`. Set `A : K ⊗[F] E` to `(1 : K) ⊗ₜ a`.

Set `ι` to `algebraMap K (K ⊗[F] E)`. Establish `hι : ∀ c : F, ι (algebraMap F K c) = (1 : K) ⊗ₜ algebraMap F E c`. Introduce `c`. Simplify using `[ι, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Rewrite using `[Algebra.TensorProduct.one_def]`.

Establish `hA : A * A = ι (algebraMap F K t) * A - ι (algebraMap F K s)`. Simplify using `only [hι, A, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sub, hts]`. Establish `hspan : ∀ x : K ⊗[F] E, ∃ u v : K, x = ι u + ι v * A`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul k e`. Take `⟨u, v, rfl⟩` from `exists_coord h2 ha e`. Use `⟨u • k, v • k, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]`.

Simplify using `[ι, A, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add x y hx hy`. Take `⟨u, v, rfl⟩` from `hx`. Take `⟨u', v', rfl⟩` from `hy`. Conclude with `⟨u + u', v + v', by simp only [map_add]; ring⟩`.

Use `⟨exists_pair_ne _, fun x y => mul_comm x y, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨u, v, rfl⟩` from `hspan x`. Use `set T := algebraMap F K t`. Use `set S := algebraMap F K s`.

Use `set N := u * u + T * u * v + S * v * v with hNdef`. Establish `hN : N ≠ 0`. Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Establish `hu : u ≠ 0` using `by rintro rfl; simp at hx`.

Simplify `hu` using `[N]`. Introduce `h0`. Apply `hno (-u / v)` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Take the linear combination `h0`.

Use `⟨ι (N⁻¹ * (u + T * v)) - ι (N⁻¹ * v) * A, ?_⟩` and prove the remaining obligations. Establish `hinv : (ι u * ι u + ι T * ι u * ι v + ι S * ι v * ι v) * ι N⁻¹ = 1`. Rewrite using `[show ι u * ι u + ι T * ι u * ι v + ι S * ι v * ι v = ι N by simp [N]]`. Rewrite using `[← map_mul, mul_inv_cancel₀ hN, map_one]`. Simplify using `only [map_mul, map_add]`.

Take the linear combination `(-(ι N⁻¹ * ι v * ι v)) * hA + hinv`.
-/
theorem exists_root (K : Type) [Field K] [Algebra F K] (h2 : Module.finrank F E = 2) {a : E}
    (ha : a ∉ Set.range (algebraMap F E)) (t s : F)
    (hts : a * a = algebraMap F E t * a - algebraMap F E s) (hK : ¬ IsField (K ⊗[F] E)) :
    ∃ β : K, β * β - algebraMap F K t * β + algebraMap F K s = 0 := by
  by_contra hno
  push_neg at hno
  apply hK
  haveI : Nontrivial (K ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := K) (B := E)
      (algebraMap F E).injective).nontrivial
  let A : K ⊗[F] E := (1 : K) ⊗ₜ a
  let ι := algebraMap K (K ⊗[F] E)
  have hι : ∀ c : F, ι (algebraMap F K c) = (1 : K) ⊗ₜ algebraMap F E c := by
    intro c
    simp [ι, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
    rw [Algebra.TensorProduct.one_def]
  have hA : A * A = ι (algebraMap F K t) * A - ι (algebraMap F K s) := by
    simp only [hι, A, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sub, hts]
  have hspan : ∀ x : K ⊗[F] E, ∃ u v : K, x = ι u + ι v * A := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul k e =>
      obtain ⟨u, v, rfl⟩ := exists_coord h2 ha e
      refine ⟨u • k, v • k, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
        ← TensorProduct.smul_tmul]
      simp [ι, A, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      exact ⟨u + u', v + v', by simp only [map_add]; ring⟩
  refine ⟨exists_pair_ne _, fun x y => mul_comm x y, ?_⟩
  intro x hx
  obtain ⟨u, v, rfl⟩ := hspan x
  set T := algebraMap F K t
  set S := algebraMap F K s
  set N := u * u + T * u * v + S * v * v with hNdef
  have hN : N ≠ 0 := by
    by_cases hv : v = 0
    · subst hv
      have hu : u ≠ 0 := by rintro rfl; simp at hx
      simpa [N] using hu
    · intro h0
      apply hno (-u / v)
      field_simp
      linear_combination h0
  refine ⟨ι (N⁻¹ * (u + T * v)) - ι (N⁻¹ * v) * A, ?_⟩
  have hinv : (ι u * ι u + ι T * ι u * ι v + ι S * ι v * ι v) * ι N⁻¹ = 1 := by
    rw [show ι u * ι u + ι T * ι u * ι v + ι S * ι v * ι v = ι N by simp [N]]
    rw [← map_mul, mul_inv_cancel₀ hN, map_one]
  simp only [map_mul, map_add]
  linear_combination (-(ι N⁻¹ * ι v * ι v)) * hA + hinv

end Quad

section Mat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_sub (σ : E →+* E) (X Y : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT σ (X - Y) = Formalism.UG.cT σ X - Formalism.UG.cT σ Y := by
  ext i j; simp [Formalism.UG.cT]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Formalism.UG.cT, Matrix.algebraMap_matrix_apply]`. Simplify using `[Formalism.UG.cT, Matrix.algebraMap_matrix_apply, h, Ne.symm h]`.
-/
theorem cT_scalar (σ : E →+* E) (a : E) :
    Formalism.UG.cT σ (algebraMap E (Matrix (Fin n) (Fin n) E) a) =
      algebraMap E (Matrix (Fin n) (Fin n) E) (σ a) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT, Matrix.algebraMap_matrix_apply]
  · simp [Formalism.UG.cT, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

/- English proof (translation)
Rewrite using `[Formalism.UG.cT_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY, Matrix.mul_assoc]`.
-/
theorem adj_mul {σ : E →+* E} {J X X' Y Y' : Matrix (Fin n) (Fin n) E}
    (hX : Formalism.UG.cT σ X * J = J * X') (hY : Formalism.UG.cT σ Y * J = J * Y') :
    Formalism.UG.cT σ (X * Y) * J = J * (Y' * X') := by
  rw [Formalism.UG.cT_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[cT_sub, Matrix.sub_mul, hX, hY, Matrix.mul_sub]`.
-/
theorem adj_sub {σ : E →+* E} {J X X' Y Y' : Matrix (Fin n) (Fin n) E}
    (hX : Formalism.UG.cT σ X * J = J * X') (hY : Formalism.UG.cT σ Y * J = J * Y') :
    Formalism.UG.cT σ (X - Y) * J = J * (X' - Y') := by
  rw [cT_sub, Matrix.sub_mul, hX, hY, Matrix.mul_sub]

/- English proof (translation)
Rewrite using `[cT_scalar, Algebra.commutes]`.
-/
theorem adj_scalar (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) :
    Formalism.UG.cT σ (algebraMap E (Matrix (Fin n) (Fin n) E) a) * J =
      J * algebraMap E (Matrix (Fin n) (Fin n) E) (σ a) := by
  rw [cT_scalar, Algebra.commutes]

/- English proof (translation)
Use `set AL := algebraMap E (genAlg γm) a`. Use `set BL := algebraMap E (genAlg γm) (σ a)`. Establish `RT : AL + BL = algebraMap F (genAlg γm) t`. Rewrite using `[IsScalarTower.algebraMap_apply F E (genAlg γm), hT, map_add]`. Establish `RS : AL * BL = algebraMap F (genAlg γm) s`.

Rewrite using `[IsScalarTower.algebraMap_apply F E (genAlg γm), hS, map_mul]`. Establish `RA : AL * AL = algebraMap F (genAlg γm) t * AL - algebraMap F (genAlg γm) s`. Rewrite using `[← RT, ← RS]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion.

Establish `h1 : (pp * AL - bb') * (pp * AL - bb') = (bb - bb') * (pp * AL - bb')`. Take the linear combination `pp * pp * RA - algebraMap F (genAlg γm) s * R1 - pp * AL * R3 + R4`. Rewrite using `[hε]`. Take the linear combination `dd * dd * h1 + dd * (pp * AL - bb') * R5 + dd * AL * R1 - dd * R2`. Establish `hA' : Formalism.UG.cT (σ : E →+* E) ((AL : genAlg γm) : Matrix (Fin n) (Fin n) E) * J = J * ((BL : genAlg γm) : Matrix (Fin n) (Fin n) E)`.

Simplify using `only [AL, BL, Subalgebra.coe_algebraMap]`. Conclude with `adj_scalar _ J a`. Establish `hεm : Formalism.UG.cT (σ : E →+* E) (εL : Matrix (Fin n) (Fin n) E) * J = J * (((BL * pp - bb') * dd : genAlg γm) : Matrix (Fin n) (Fin n) E)`. Rewrite using `[hε]`. Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_sub]`.

Conclude with `adj_mul hd (adj_sub (adj_mul hp hA') hb')`. Establish `hY : (BL * pp - bb') * dd * εL = 0`. Rewrite using `[hε]`. Take the linear combination `dd * dd * (pp * pp * RS - pp * bb' * RT + algebraMap F (genAlg γm) s * R1 + bb' * R3 - R4)`. Rewrite using `[hεm, Matrix.mul_assoc, ← Subalgebra.coe_mul, hY]`.

Simplify using the standard rewrite rules.
-/
theorem piece (σ : E →ₐ[F] E) (J γm : Matrix (Fin n) (Fin n) E) (t s : F)
    (pp bb bb' dd : genAlg γm)
    (hp : Formalism.UG.cT (σ : E →+* E) (pp : Matrix (Fin n) (Fin n) E) * J = J * pp)
    (hb' : Formalism.UG.cT (σ : E →+* E) (bb' : Matrix (Fin n) (Fin n) E) * J = J * bb')
    (hd : Formalism.UG.cT (σ : E →+* E) (dd : Matrix (Fin n) (Fin n) E) * J = J * dd)
    (R1 : pp * pp = pp) (R2 : pp * bb' = bb') (R3 : bb + bb' = algebraMap F _ t * pp)
    (R4 : bb * bb' = algebraMap F _ s * pp) (R5 : dd * (bb - bb') = pp)
    (a : E) (hT : algebraMap F E t = a + σ a) (hS : algebraMap F E s = a * σ a)
    (εL : genAlg γm) (hε : εL = dd * (pp * algebraMap E (genAlg γm) a - bb')) :
    εL * εL = εL ∧
      Formalism.UG.cT (σ : E →+* E) (εL : Matrix (Fin n) (Fin n) E) * J * (εL : Matrix (Fin n) (Fin n) E) = 0 := by
  set AL := algebraMap E (genAlg γm) a
  set BL := algebraMap E (genAlg γm) (σ a)
  have RT : AL + BL = algebraMap F (genAlg γm) t := by
    rw [IsScalarTower.algebraMap_apply F E (genAlg γm), hT, map_add]
  have RS : AL * BL = algebraMap F (genAlg γm) s := by
    rw [IsScalarTower.algebraMap_apply F E (genAlg γm), hS, map_mul]
  have RA : AL * AL = algebraMap F (genAlg γm) t * AL - algebraMap F (genAlg γm) s := by
    rw [← RT, ← RS]; ring
  constructor
  · have h1 : (pp * AL - bb') * (pp * AL - bb') = (bb - bb') * (pp * AL - bb') := by
      linear_combination pp * pp * RA - algebraMap F (genAlg γm) s * R1 - pp * AL * R3 + R4
    rw [hε]
    linear_combination dd * dd * h1 + dd * (pp * AL - bb') * R5 + dd * AL * R1 - dd * R2
  · have hA' : Formalism.UG.cT (σ : E →+* E) ((AL : genAlg γm) : Matrix (Fin n) (Fin n) E) * J =
        J * ((BL : genAlg γm) : Matrix (Fin n) (Fin n) E) := by
      simp only [AL, BL, Subalgebra.coe_algebraMap]
      exact adj_scalar _ J a
    have hεm : Formalism.UG.cT (σ : E →+* E) (εL : Matrix (Fin n) (Fin n) E) * J =
        J * (((BL * pp - bb') * dd : genAlg γm) : Matrix (Fin n) (Fin n) E) := by
      rw [hε]
      simp only [Subalgebra.coe_mul, Subalgebra.coe_sub]
      exact adj_mul hd (adj_sub (adj_mul hp hA') hb')
    have hY : (BL * pp - bb') * dd * εL = 0 := by
      rw [hε]
      linear_combination dd * dd * (pp * pp * RS - pp * bb' * RT +
        algebraMap F (genAlg γm) s * R1 + bb' * R3 - R4)
    rw [hεm, Matrix.mul_assoc, ← Subalgebra.coe_mul, hY]
    simp

end Mat

/- English proof (translation)
Introduce `F E _ _ _ _ n σ J γ hR hA hP k K _ _ he i hi`. Take `⟨e⟩` from `he`. Take `⟨α, hα⟩` from `hR.quad.ne_id`. Take `⟨t, ht⟩` from `fixed_mem hR.quad (x := α + σ α) (by rw [map_add, hR.quad.invol, add_comm])`. Take `⟨s, hs⟩` from `fixed_mem hR.quad (x := α * σ α) (by rw [map_mul, hR.quad.invol, mul_comm])`.

Establish `hαF : α ∉ Set.range (algebraMap F E)`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `hα (σ.commutes c)`. Establish `hαsq : α * α = algebraMap F E t * α - algebraMap F E s` using `by rw [ht, hs]; ring`. Take `⟨β, hβ⟩` from `exists_root (K i) hR.quad.finrank_eq hαF t s hαsq hi`.

Establish `hdisc : β - (algebraMap F (K i) t - β) ≠ 0`. Establish `hE : algebraMap F E (t * t - 4 * s) ≠ 0`. Rewrite using `[map_sub, map_mul, map_mul, ht, hs, map_ofNat]`. Introduce `h`. Apply `hα` to reduce the goal to its premises.

Establish `h' : (α - σ α) * (α - σ α) = 0` using `by linear_combination h`. Conclude with `(sub_eq_zero.1 (mul_self_eq_zero.1 h')).symm`. Establish `hK : algebraMap F (K i) (t * t - 4 * s) ≠ 0` using `(map_ne_zero _).2 (fun h0 => hE (by rw [h0, map_zero]))`. Introduce `h0`. Apply `hK` to reduce the goal to its premises.

Rewrite using `[map_sub, map_mul, map_mul, map_ofNat]`. Establish `h' : (β - (algebraMap F (K i) t - β)) * (β - (algebraMap F (K i) t - β)) = 0`. Rewrite using `[h0, mul_zero]`. Take the linear combination `h' - 4 * hβ`. Use `set T' := algebraMap F (K i) t with hT'`.

Set `y : ∀ j, K j` to `Pi.single i 1`. Set `w : ∀ j, K j` to `Pi.single i β`. Set `x : ∀ j, K j` to `Pi.single i (T' - β)`. Set `z : ∀ j, K j` to `Pi.single i (β - (T' - β))⁻¹`. Establish `Q1 : y * y = y`.

Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[y]`. Simplify using `[y, Pi.single_apply, h]`.

Establish `Q2 : y * x = x`. Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[y, x]`.

Simplify using `[y, x, Pi.single_apply, h]`. Establish `Q3 : w + x = algebraMap F _ t * y`. Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `[y, w, x, Pi.algebraMap_apply, T']`. Simplify using `[y, w, x, Pi.single_apply, h]`. Establish `Q4 : w * x = algebraMap F _ s * y`. Use extensionality with `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `[y, w, x, Pi.algebraMap_apply, T']`. Take the linear combination `-hβ`. Simplify using `[y, w, x, Pi.single_apply, h]`. Establish `Q5 : z * (w - x) = y`.

Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[y, w, x, z, inv_mul_cancel₀ hdisc]`. Simplify using `[y, w, x, z, Pi.single_apply, h]`.

Set `φ : (∀ j, K j) →ₐ[F] genAlg (γ : Matrix (Fin n) (Fin n) E)` to `(plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)).val.comp (e.symm : (∀ j, K j) →ₐ[F] plusAlg σ J (γ : Matrix (Fin n) (Fin n) E))`. Establish `hmem : ∀ v, Formalism.UG.cT (σ : E →+* E) ((φ v : genAlg (γ : Matrix (Fin n) (Fin n) E)) : Matrix (Fin n) (Fin n) E) * J = J * ((φ v : genAlg (γ : Matrix (Fin n) (Fin n) E)) : Matrix (Fin n) (Fin n) E)` using `fun v => (e.symm v).2`. Establish `R1 : φ y * φ y = φ y` using `by rw [← map_mul, Q1]`. Establish `R2 : φ y * φ x = φ x` using `by rw [← map_mul, Q2]`. Establish `R3 : φ w + φ x = algebraMap F _ t * φ y` using `by rw [← map_add, Q3, map_mul, AlgHom.commutes]`.

Establish `R4 : φ w * φ x = algebraMap F _ s * φ y` using `by rw [← map_mul, Q4, map_mul, AlgHom.commutes]`. Establish `R5 : φ z * (φ w - φ x) = φ y` using `by rw [← map_sub, ← map_mul, Q5]`. Establish `P1` using `piece σ J _ t s (φ y) (φ w) (φ x) (φ z) (hmem y) (hmem x) (hmem z) R1 R2 R3 R4 R5 α ht hs _ rfl`. Establish `P2` using `piece σ J _ t s (φ y) (φ w) (φ x) (φ z) (hmem y) (hmem x) (hmem z) R1 R2 R3 R4 R5 (σ α) (by rw [hR.quad.invol, ht, add_comm]) (by rw [hR.quad.invol, hs, mul_comm]) _ rfl`. Establish `RT : algebraMap E (genAlg (γ : Matrix (Fin n) (Fin n) E)) α + algebraMap E (genAlg (γ : Matrix (Fin n) (Fin n) E)) (σ α) = algebraMap F _ t`.

Rewrite using `[IsScalarTower.algebraMap_apply F E (genAlg (γ : Matrix (Fin n) (Fin n) E)), ht, map_add]`. Establish `hsum : φ z * (φ y * algebraMap E _ α - φ x) + φ z * (φ y * algebraMap E _ (σ α) - φ x) = φ y`. Take the linear combination `R5 + φ z * φ y * RT - φ z * R3`. Establish `hy0 : ((φ y : genAlg (γ : Matrix (Fin n) (Fin n) E)) : Matrix (Fin n) (Fin n) E) ≠ 0`. Introduce `h0`.

Establish `h1 : φ y = 0` using `Subtype.ext h0`. Establish `h2 : y = 0`. Establish `h3 : e.symm y = 0` using `Subtype.ext h1`. Simplify using `using congrArg e h3`. Establish `h4` using `congrFun h2 i`.

Simplify using `[y] at h4`. Distinguish the cases in `h1 : (((φ z * (φ y * algebraMap E _ α - φ x) : genAlg (γ : Matrix (Fin n) (Fin n) E))) : Matrix (Fin n) (Fin n) E) = 0`. Use `⟨_, (φ z * (φ y * algebraMap E _ (σ α) - φ x)).2, congrArg Subtype.val P2.1, ?_, P2.2⟩` and prove the remaining obligations. Introduce `h2`. Apply `hy0` to reduce the goal to its premises.

Rewrite using `[← hsum, Subalgebra.coe_add, h1, h2, add_zero]`. Conclude with `⟨_, (φ z * (φ y * algebraMap E _ α - φ x)).2, congrArg Subtype.val P1.1, h1, P1.2⟩`.
-/
theorem exists_isotropic_idempotent : ∀ {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClausePlus σ J γ → ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)], Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) → ∀ i, ¬ IsField (K i ⊗[F] E) → ∃ ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix (Fin n) (Fin n) E), ε * ε = ε ∧ ε ≠ 0 ∧ Formalism.UG.cT (σ : E →+* E) ε * J * ε = 0 := by
  intro F E _ _ _ _ n σ J γ hR hA hP k K _ _ he i hi
  classical
  obtain ⟨e⟩ := he
  obtain ⟨α, hα⟩ := hR.quad.ne_id
  obtain ⟨t, ht⟩ := fixed_mem hR.quad (x := α + σ α) (by rw [map_add, hR.quad.invol, add_comm])
  obtain ⟨s, hs⟩ := fixed_mem hR.quad (x := α * σ α) (by rw [map_mul, hR.quad.invol, mul_comm])
  have hαF : α ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, rfl⟩; exact hα (σ.commutes c)
  have hαsq : α * α = algebraMap F E t * α - algebraMap F E s := by rw [ht, hs]; ring
  obtain ⟨β, hβ⟩ := exists_root (K i) hR.quad.finrank_eq hαF t s hαsq hi
  have hdisc : β - (algebraMap F (K i) t - β) ≠ 0 := by
    have hE : algebraMap F E (t * t - 4 * s) ≠ 0 := by
      rw [map_sub, map_mul, map_mul, ht, hs, map_ofNat]
      intro h; apply hα
      have h' : (α - σ α) * (α - σ α) = 0 := by linear_combination h
      exact (sub_eq_zero.1 (mul_self_eq_zero.1 h')).symm
    have hK : algebraMap F (K i) (t * t - 4 * s) ≠ 0 :=
      (map_ne_zero _).2 (fun h0 => hE (by rw [h0, map_zero]))
    intro h0; apply hK
    rw [map_sub, map_mul, map_mul, map_ofNat]
    have h' : (β - (algebraMap F (K i) t - β)) * (β - (algebraMap F (K i) t - β)) = 0 := by
      rw [h0, mul_zero]
    linear_combination h' - 4 * hβ
  set T' := algebraMap F (K i) t with hT'
  let y : ∀ j, K j := Pi.single i 1
  let w : ∀ j, K j := Pi.single i β
  let x : ∀ j, K j := Pi.single i (T' - β)
  let z : ∀ j, K j := Pi.single i (β - (T' - β))⁻¹
  have Q1 : y * y = y := by
    ext j; by_cases h : j = i
    · subst h; simp [y]
    · simp [y, Pi.single_apply, h]
  have Q2 : y * x = x := by
    ext j; by_cases h : j = i
    · subst h; simp [y, x]
    · simp [y, x, Pi.single_apply, h]
  have Q3 : w + x = algebraMap F _ t * y := by
    ext j; by_cases h : j = i
    · subst h; simp [y, w, x, Pi.algebraMap_apply, T']
    · simp [y, w, x, Pi.single_apply, h]
  have Q4 : w * x = algebraMap F _ s * y := by
    ext j; by_cases h : j = i
    · subst h; simp [y, w, x, Pi.algebraMap_apply, T']
      linear_combination -hβ
    · simp [y, w, x, Pi.single_apply, h]
  have Q5 : z * (w - x) = y := by
    ext j; by_cases h : j = i
    · subst h; simp [y, w, x, z, inv_mul_cancel₀ hdisc]
    · simp [y, w, x, z, Pi.single_apply, h]
  let φ : (∀ j, K j) →ₐ[F] genAlg (γ : Matrix (Fin n) (Fin n) E) :=
    (plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)).val.comp
      (e.symm : (∀ j, K j) →ₐ[F] plusAlg σ J (γ : Matrix (Fin n) (Fin n) E))
  have hmem : ∀ v, Formalism.UG.cT (σ : E →+* E) ((φ v : genAlg (γ : Matrix (Fin n) (Fin n) E)) :
      Matrix (Fin n) (Fin n) E) * J = J * ((φ v : genAlg (γ : Matrix (Fin n) (Fin n) E)) :
      Matrix (Fin n) (Fin n) E) := fun v => (e.symm v).2
  have R1 : φ y * φ y = φ y := by rw [← map_mul, Q1]
  have R2 : φ y * φ x = φ x := by rw [← map_mul, Q2]
  have R3 : φ w + φ x = algebraMap F _ t * φ y := by rw [← map_add, Q3, map_mul, AlgHom.commutes]
  have R4 : φ w * φ x = algebraMap F _ s * φ y := by rw [← map_mul, Q4, map_mul, AlgHom.commutes]
  have R5 : φ z * (φ w - φ x) = φ y := by rw [← map_sub, ← map_mul, Q5]
  have P1 := piece σ J _ t s (φ y) (φ w) (φ x) (φ z) (hmem y) (hmem x) (hmem z) R1 R2 R3 R4 R5
    α ht hs _ rfl
  have P2 := piece σ J _ t s (φ y) (φ w) (φ x) (φ z) (hmem y) (hmem x) (hmem z) R1 R2 R3 R4 R5
    (σ α) (by rw [hR.quad.invol, ht, add_comm]) (by rw [hR.quad.invol, hs, mul_comm]) _ rfl
  have RT : algebraMap E (genAlg (γ : Matrix (Fin n) (Fin n) E)) α +
      algebraMap E (genAlg (γ : Matrix (Fin n) (Fin n) E)) (σ α) = algebraMap F _ t := by
    rw [IsScalarTower.algebraMap_apply F E (genAlg (γ : Matrix (Fin n) (Fin n) E)), ht, map_add]
  have hsum : φ z * (φ y * algebraMap E _ α - φ x) + φ z * (φ y * algebraMap E _ (σ α) - φ x)
      = φ y := by
    linear_combination R5 + φ z * φ y * RT - φ z * R3
  have hy0 : ((φ y : genAlg (γ : Matrix (Fin n) (Fin n) E)) : Matrix (Fin n) (Fin n) E) ≠ 0 := by
    intro h0
    have h1 : φ y = 0 := Subtype.ext h0
    have h2 : y = 0 := by
      have h3 : e.symm y = 0 := Subtype.ext h1
      simpa using congrArg e h3
    have h4 := congrFun h2 i
    simp [y] at h4
  by_cases h1 : (((φ z * (φ y * algebraMap E _ α - φ x) :
      genAlg (γ : Matrix (Fin n) (Fin n) E))) : Matrix (Fin n) (Fin n) E) = 0
  · refine ⟨_, (φ z * (φ y * algebraMap E _ (σ α) - φ x)).2, congrArg Subtype.val P2.1, ?_, P2.2⟩
    intro h2; apply hy0
    rw [← hsum, Subalgebra.coe_add, h1, h2, add_zero]
  · exact ⟨_, (φ z * (φ y * algebraMap E _ α - φ x)).2, congrArg Subtype.val P1.1, h1, P1.2⟩

end GlobalTheory.SplitFactorIdem
