import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledMatrixMemRationalLatticeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatOpen

open GlobalTheory.LatVac Topology

/- English proof (translation)
Set `H : AddSubgroup G` to `{ carrier := {x : G | ∃ l ∈ L, φ (x - N • l) = 0} zero_mem' := ⟨0, L.zero_mem, by simp⟩ add_mem' := by`. Introduce and unpack `x y ⟨l, hl, e⟩ ⟨l', hl', e'⟩`. Use `⟨l + l', L.add_mem hl hl', ?_⟩` and prove the remaining obligations. Rewrite using `[show x + y - N • (l + l') = (x - N • l) + (y - N • l') by rw [nsmul_add]; abel, map_add, e, e', add_zero]`. Use the proof step `neg_mem' := by`.

Introduce and unpack `x ⟨l, hl, e⟩`. Use `⟨-l, L.neg_mem hl, ?_⟩` and prove the remaining obligations. Rewrite using `[show -x - N • (-l) = -(x - N • l) by rw [neg_nsmul]; abel, map_neg, e, neg_zero] }`. Conclude with `H.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU h)`.
-/
theorem isOpen_of_nhds {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddCommGroup G'] (φ : G →+ G') (L : AddSubgroup G) (N : ℕ) (U : Set G) (hU : U ∈ 𝓝 0)
    (h : ∀ x ∈ U, ∃ l ∈ L, φ (x - N • l) = 0) : IsOpen {x : G | ∃ l ∈ L, φ (x - N • l) = 0} := by
  let H : AddSubgroup G :=
    { carrier := {x : G | ∃ l ∈ L, φ (x - N • l) = 0}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨l, hl, e⟩ ⟨l', hl', e'⟩
        refine ⟨l + l', L.add_mem hl hl', ?_⟩
        rw [show x + y - N • (l + l') = (x - N • l) + (y - N • l') by rw [nsmul_add]; abel, map_add, e, e', add_zero]
      neg_mem' := by
        rintro x ⟨l, hl, e⟩
        refine ⟨-l, L.neg_mem hl, ?_⟩
        rw [show -x - N • (-l) = -(x - N • l) by rw [neg_nsmul]; abel, map_neg, e, neg_zero] }
  exact H.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU h)

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => Valued.isOpen_valuationSubring _`.
-/
theorem isOpen_intAf (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

/- English proof (translation)
Introduce `v` and use `zero_mem (v.adicCompletionIntegers F)`.
-/
theorem zero_mem_intAf (F : Type) [Field F] [NumberField F] : (0 : Af F) ∈ intAf F :=
  fun v => zero_mem (v.adicCompletionIntegers F)

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]`. Rewrite using `[show ∀ y, finPart D y = (finPart D).toAddMonoidHom y from fun _ => rfl, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show finPart D _ = _`. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Both sides reduce to the same expression.
-/
theorem finPart_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι D.host.F D.host.E) (z : AE D) :
    finPart D z = ∑ k, sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).coord k z) ⊗ₜ[D.host.F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]
  rw [show ∀ y, finPart D y = (finPart D).toAddMonoidHom y from fun _ => rfl, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show finPart D _ = _
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `hM' : (M : F) ≠ 0` using `Nat.cast_ne_zero.2 hM.ne'`. Rewrite using `[← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, smul_smul, Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hN' hM'), one_smul]`.
-/
theorem nsmul_tmul_cancel {F A E : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [AddCommGroup E] [Module F E]
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (a : A) (e : E) :
    N • ((algebraMap F A ((N * M : ℕ) : F)⁻¹ * a) ⊗ₜ[F] (M • e)) = a ⊗ₜ[F] e := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, smul_smul, Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hN' hM'), one_smul]

/- English proof (translation)
Introduce `D S T ΛS ΛT hS hT N hN`. Set `b` to `Module.finBasis D.host.F D.host.E`. Set `B` to `Algebra.TensorProduct.basis (AF D.host.F) b`. Use `choose M hM hMl using fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) => GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT hS.1 hT.1 (Matrix.single p.1 p.2.1 (b p.2.2))`. Set `f : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F` to `fun p x => algebraMap D.host.F (Af D.host.F) ((N * M p : ℕ) : D.host.F)⁻¹ * sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1))`.

Establish `hf : ∀ p, Continuous (f p)` using `fun p => by`. Establish `h1 : Continuous (B.coord p.2.2)` using `IsModuleTopology.continuous_of_linearMap _`. Establish `h2 : Continuous (sndA D.host.F)` using `continuous_snd`. Conclude with `continuous_const.mul (h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))`. Establish `hf0 : ∀ p, f p 0 = 0` using `fun p => by show _ * sndA D.host.F (B.coord p.2.2 0) = 0`.

Rewrite using `[LinearMap.map_zero, map_zero, mul_zero]`. Set `φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)` to `(finPart D).toAddMonoidHom.mapMatrix`. Use `isOpen_of_nhds φ _ N (⋂ p, f p ⁻¹' intAf D.host.F) ?_ ?_` and prove the remaining obligations. Use `Filter.iInter_mem.2 fun p => ((isOpen_intAf _).preimage (hf p)).mem_nhds ?_ show f p 0 ∈ intAf D.host.F` and prove the remaining obligations. Rewrite using `[hf0]`.

Conclude with `zero_mem_intAf _`. Introduce `x hx`. Use `⟨∑ p, finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)), AddSubgroup.sum_mem _ fun p _ => finTens_mem_latO (Set.mem_iInter.1 hx p) (hMl p), ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.map_sub, AddMonoidHom.map_nsmul, sub_eq_zero, map_sum, ← Finset.sum_nsmul]`. Use extensionality with `i j`.

Rewrite using `[Matrix.sum_apply]`. Establish `e : ∀ p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E), (N • φ (finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)))) i j = sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1)) ⊗ₜ[D.host.F] (Matrix.single p.1 p.2.1 (b p.2.2) i j)` using `fun p => nsmul_tmul_cancel hN (hM p) _ _`. Rewrite using `[Finset.sum_congr rfl fun p _ => e p, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_prod_type, Finset.sum_eq_single j]`. Simplify using `only [Matrix.single_apply_same]`. Conclude with `finPart_eq_sum b (x i j)`.

Introduce `j' _ hj`. Conclude with `Finset.sum_eq_zero fun k _ => by`. Rewrite using `[Matrix.single_apply_of_col_ne _ _ hj, TensorProduct.tmul_zero]`. Simplify using the standard rewrite rules. Introduce `i' _ hi`.

Conclude with `Finset.sum_eq_zero fun k _ => by`. Rewrite using `[Matrix.single_apply_of_row_ne hi, TensorProduct.tmul_zero]`. Simplify using the standard rewrite rules.
-/
theorem isOpen_nsmul_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  intro D S T ΛS ΛT hS hT N hN
  classical
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  choose M hM hMl using fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) =>
    GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT hS.1 hT.1 (Matrix.single p.1 p.2.1 (b p.2.2))
  let f : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F := fun p x =>
    algebraMap D.host.F (Af D.host.F) ((N * M p : ℕ) : D.host.F)⁻¹ * sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1))
  have hf : ∀ p, Continuous (f p) := fun p => by
    have h1 : Continuous (B.coord p.2.2) := IsModuleTopology.continuous_of_linearMap _
    have h2 : Continuous (sndA D.host.F) := continuous_snd
    exact continuous_const.mul (h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))
  have hf0 : ∀ p, f p 0 = 0 := fun p => by
    show _ * sndA D.host.F (B.coord p.2.2 0) = 0
    rw [LinearMap.map_zero, map_zero, mul_zero]
  let φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finPart D).toAddMonoidHom.mapMatrix
  refine isOpen_of_nhds φ _ N (⋂ p, f p ⁻¹' intAf D.host.F) ?_ ?_
  · refine Filter.iInter_mem.2 fun p => ((isOpen_intAf _).preimage (hf p)).mem_nhds ?_
    show f p 0 ∈ intAf D.host.F
    rw [hf0]; exact zero_mem_intAf _
  · intro x hx
    refine ⟨∑ p, finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)),
      AddSubgroup.sum_mem _ fun p _ => finTens_mem_latO (Set.mem_iInter.1 hx p) (hMl p), ?_⟩
    rw [AddMonoidHom.map_sub, AddMonoidHom.map_nsmul, sub_eq_zero, map_sum, ← Finset.sum_nsmul]
    ext i j
    rw [Matrix.sum_apply]
    have e : ∀ p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E),
        (N • φ (finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)))) i j =
        sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1)) ⊗ₜ[D.host.F] (Matrix.single p.1 p.2.1 (b p.2.2) i j) :=
      fun p => nsmul_tmul_cancel hN (hM p) _ _
    rw [Finset.sum_congr rfl fun p _ => e p, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_prod_type,
      Finset.sum_eq_single j]
    · simp only [Matrix.single_apply_same]
      exact finPart_eq_sum b (x i j)
    · intro j' _ hj
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_col_ne _ _ hj, TensorProduct.tmul_zero]
    · simp
    · intro i' _ hi
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_row_ne hi, TensorProduct.tmul_zero]
    · simp

end GlobalTheory.LatOpen

end
