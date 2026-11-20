import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.MovedLat

open Formalism.UG

/- English proof (translation)
Rewrite using `[map_inv]`. Conclude with `htOf_inv _ _`.
-/
theorem htFin_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) :
    htFin F v (bc (compFin F E v) g⁻¹) = htFin F v (bc (compFin F E v) g) := by
  rw [map_inv]; exact htOf_inv _ _

/- English proof (translation)
The claim follows from `le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)`.
-/
theorem finprod_htFin_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) :
    ∏ᶠ v, htFin F v (bc (compFin F E v) g) ≤ heightGL F g :=
  le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)

end GlobalTheory.MovedLat

open Formalism.UG

/- English proof (translation)
Introduce `F E _ _ _ _ _ n d κ _ _ e N hN`. Set `f1 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F)` to `fun j => (LinearMap.proj j).comp ((LinearMap.fst (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)`. Set `f2 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F)` to `fun j => (LinearMap.proj j).comp ((LinearMap.snd (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)`. Use `choose K1 hK1f hK1 hK1b using fun j => GlobalTheory.LinFormBound.main (f1 j)`. Use `choose K2 hK2f hK2 hK2b using fun j => GlobalTheory.LinFormBound.main (f2 j)`.

Set `Y : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E)` to `fun i => e.symm (0, Pi.single i 1)`. Use `choose Kx hKxf hKx hKxb using fun i => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y i)`. Set `Kc : HeightOneSpectrum (𝓞 F) → ℝ≥0` to `fun v => (∏ j, K1 j v * K2 j v) * ∏ i, Kx i v`. Establish `hKc1 : ∀ v, 1 ≤ Kc v` using `fun v => one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v)) (Finset.one_le_prod' fun i _ => hKx i v)`. Establish `hKcf : (Function.mulSupport Kc).Finite`.

Use `((Set.finite_iUnion fun j => (hK1f j).union (hK2f j)).union (Set.finite_iUnion hKxf)).subset ?_` and prove the remaining obligations. Use `(Function.mulSupport_mul _ _).trans (Set.union_subset_union ?_ ?_)` and prove the remaining obligations. Use `(Finset.mulSupport_prod _ _).trans ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_iUnion] at hv ⊢`.

Take `⟨j, -, hj⟩` from `hv`. Conclude with `⟨j, Function.mulSupport_mul _ _ hj⟩`. Use `(Finset.mulSupport_prod _ _).trans ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_iUnion] at hv ⊢`.

Take `⟨i, -, hi⟩` from `hv`. Conclude with `⟨i, hi⟩`. Establish `hP1 : ∀ v, ∏ j, K1 j v * K2 j v ≤ Kc v` using `fun v => le_mul_of_one_le_right' (Finset.one_le_prod' fun i _ => hKx i v)`. Establish `hP2 : ∀ v, ∏ i, Kx i v ≤ Kc v` using `fun v => le_mul_of_one_le_left' (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))`. Establish `hK1c : ∀ v i j, K1 j v * Kx i v ≤ Kc v` using `fun v i j => by`.

Use `le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v)) (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))` and prove the remaining obligations. Conclude with `mul_le_mul' (le_mul_of_one_le_right' (hK2 j v)) le_rfl`. Establish `hK2c : ∀ v i j, K2 j v * Kx i v ≤ Kc v` using `fun v i j => by`. Use `le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v)) (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))` and prove the remaining obligations. Conclude with `mul_le_mul' (le_mul_of_one_le_left' (hK1 j v)) le_rfl`.

Set `C0 : ℝ≥0` to `∏ᶠ v, Kc v`. Use `⟨N * C0, 1, fun g h => ?_⟩` and prove the remaining obligations. Set `Hg : HeightOneSpectrum (𝓞 F) → ℝ≥0` to `fun v => htFin F v (bc (compFin F E v) g)`. Set `Hh : HeightOneSpectrum (𝓞 F) → ℝ≥0` to `fun v => htFin F v (bc (compFin F E v) h)`. Establish `hgf : (Function.mulSupport Hg).Finite` using `finite_mulSupport_htFin F g`.

Establish `hhf : (Function.mulSupport Hh).Finite` using `finite_mulSupport_htFin F h`. Set `Z : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E)` to `fun i => ((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i * (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ`. Establish `hsup : ∀ i v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Z i p.1 p.2))) ≤ Kx i v * (Hg v * Hh v)` using `fun i v => by`. Use `Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g⁻¹ (Y i) h⁻¹ v p.1 p.2).trans ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.MovedLat.htFin_bc_inv, GlobalTheory.MovedLat.htFin_bc_inv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hloc1 : ∀ i j v, ‖evFin F v ((e (Z i)).1 j)‖₊ ≤ Kc v * (Hg v * Hh v)` using `fun i j v => by`. Use `hK1b j (Z i) v` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hloc2 : ∀ i j v, ‖evFin F v ((e (Z i)).2 j)‖₊ ≤ Kc v * (Hg v * Hh v)` using `fun i j v => by`.

Use `hK2b j (Z i) v` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Set `H : HeightOneSpectrum (𝓞 F) → ℝ≥0` to `fun v => Kc v * (Hg v * Hh v)`. Establish `hH1 : ∀ v, 1 ≤ H v` using `fun v => one_le_mul_of_one_le_of_one_le (hKc1 v) (one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))`. Establish `hHf : (Function.mulSupport H).Finite` using `(hKcf.union (hgf.union hhf)).subset ((Function.mulSupport_mul _ _).trans (Set.union_subset_union le_rfl (Function.mulSupport_mul _ _)))`.

Take `⟨M, hM0, hMb, hMv⟩` from `GlobalTheory.SmoothForms.denom_global H hH1 hHf`. Establish `hfin : ∀ x : AF F, (∀ v, ‖evFin F v x‖₊ ≤ H v) → GlobalTheory.FinSupp.FinDiv F N (((N * M : ℕ) : AF F) * x)`. Introduce `x hx v`. Use `⟨(M : Fv F v) * evFin F v x, Valued.toNormedField.norm_le_one_iff.1 (hMv v _ (hx v)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_natCast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨N * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun i j => ⟨hfin _ (hloc1 i j), hfin _ (hloc2 i j)⟩⟩` and prove the remaining obligations. Establish `hMH : (M : ℝ≥0) ≤ C0 * (heightGL F g * heightGL F h)`. Use `hMb.trans (le_of_eq_of_le (finprod_mul_distrib hKcf ((hgf.union hhf).subset (Function.mulSupport_mul _ _))) ?_)` and prove the remaining obligations.

Use `mul_le_mul' le_rfl ?_` and prove the remaining obligations. Rewrite using `[finprod_mul_distrib hgf hhf]`. Conclude with `mul_le_mul' (GlobalTheory.MovedLat.finprod_htFin_le g) (GlobalTheory.MovedLat.finprod_htFin_le h)`. Use `NNReal.coe_le_coe.2 hMH` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Rewrite using `[pow_one, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left this (by positivity)`.
-/
theorem GlobalTheory.MovedLat.exists_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  intro F E _ _ _ _ _ n d κ _ _ e N hN
  classical
  let f1 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.fst (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  let f2 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.snd (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  choose K1 hK1f hK1 hK1b using fun j => GlobalTheory.LinFormBound.main (f1 j)
  choose K2 hK2f hK2 hK2b using fun j => GlobalTheory.LinFormBound.main (f2 j)
  let Y : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i => e.symm (0, Pi.single i 1)
  choose Kx hKxf hKx hKxb using fun i => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y i)
  let Kc : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ j, K1 j v * K2 j v) * ∏ i, Kx i v
  have hKc1 : ∀ v, 1 ≤ Kc v := fun v =>
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.one_le_prod' fun i _ => hKx i v)
  have hKcf : (Function.mulSupport Kc).Finite := by
    refine ((Set.finite_iUnion fun j => (hK1f j).union (hK2f j)).union (Set.finite_iUnion hKxf)).subset ?_
    refine (Function.mulSupport_mul _ _).trans (Set.union_subset_union ?_ ?_)
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨j, -, hj⟩ := hv
      exact ⟨j, Function.mulSupport_mul _ _ hj⟩
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨i, -, hi⟩ := hv
      exact ⟨i, hi⟩
  have hP1 : ∀ v, ∏ j, K1 j v * K2 j v ≤ Kc v := fun v =>
    le_mul_of_one_le_right' (Finset.one_le_prod' fun i _ => hKx i v)
  have hP2 : ∀ v, ∏ i, Kx i v ≤ Kc v := fun v =>
    le_mul_of_one_le_left' (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
  have hK1c : ∀ v i j, K1 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_right' (hK2 j v)) le_rfl
  have hK2c : ∀ v i j, K2 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_left' (hK1 j v)) le_rfl
  let C0 : ℝ≥0 := ∏ᶠ v, Kc v
  refine ⟨N * C0, 1, fun g h => ?_⟩
  let Hg : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) g)
  let Hh : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) h)
  have hgf : (Function.mulSupport Hg).Finite := finite_mulSupport_htFin F g
  have hhf : (Function.mulSupport Hh).Finite := finite_mulSupport_htFin F h
  let Z : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i =>
    ((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
      (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ
  have hsup : ∀ i v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Z i p.1 p.2))) ≤
      Kx i v * (Hg v * Hh v) := fun i v => by
    refine Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g⁻¹ (Y i) h⁻¹ v p.1 p.2).trans ?_
    rw [GlobalTheory.MovedLat.htFin_bc_inv, GlobalTheory.MovedLat.htFin_bc_inv]
    calc _ ≤ Hg v * Kx i v * Hh v := mul_le_mul' (mul_le_mul' le_rfl (hKxb i v)) le_rfl
      _ = Kx i v * (Hg v * Hh v) := by ring
  have hloc1 : ∀ i j v, ‖evFin F v ((e (Z i)).1 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK1b j (Z i) v
    calc _ ≤ K1 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K1 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK1c v i j) le_rfl
  have hloc2 : ∀ i j v, ‖evFin F v ((e (Z i)).2 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK2b j (Z i) v
    calc _ ≤ K2 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K2 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK2c v i j) le_rfl
  let H : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => Kc v * (Hg v * Hh v)
  have hH1 : ∀ v, 1 ≤ H v := fun v =>
    one_le_mul_of_one_le_of_one_le (hKc1 v) (one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))
  have hHf : (Function.mulSupport H).Finite :=
    (hKcf.union (hgf.union hhf)).subset ((Function.mulSupport_mul _ _).trans
      (Set.union_subset_union le_rfl (Function.mulSupport_mul _ _)))
  obtain ⟨M, hM0, hMb, hMv⟩ := GlobalTheory.SmoothForms.denom_global H hH1 hHf
  have hfin : ∀ x : AF F, (∀ v, ‖evFin F v x‖₊ ≤ H v) → GlobalTheory.FinSupp.FinDiv F N (((N * M : ℕ) : AF F) * x) := by
    intro x hx v
    refine ⟨(M : Fv F v) * evFin F v x, Valued.toNormedField.norm_le_one_iff.1 (hMv v _ (hx v)), ?_⟩
    rw [map_mul, map_natCast]
    push_cast
    ring
  refine ⟨N * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun i j => ⟨hfin _ (hloc1 i j), hfin _ (hloc2 i j)⟩⟩
  have hMH : (M : ℝ≥0) ≤ C0 * (heightGL F g * heightGL F h) := by
    refine hMb.trans (le_of_eq_of_le (finprod_mul_distrib hKcf ((hgf.union hhf).subset (Function.mulSupport_mul _ _))) ?_)
    refine mul_le_mul' le_rfl ?_
    rw [finprod_mul_distrib hgf hhf]
    exact mul_le_mul' (GlobalTheory.MovedLat.finprod_htFin_le g) (GlobalTheory.MovedLat.finprod_htFin_le h)
  have := NNReal.coe_le_coe.2 hMH
  push_cast at this ⊢
  rw [pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left this (by positivity)
