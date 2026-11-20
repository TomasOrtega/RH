import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobFrame
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/- English proof (translation)
Rewrite using `[h, TensorProduct.tmul_add]`. Use `congr 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one (A := A) u, smul_smul, ← Algebra.smul_def, TensorProduct.smul_tmul]`. Establish `hd' : (d : E) * a = (d : F) • a` using `by rw [Algebra.smul_def, map_natCast]`. Rewrite using `[TensorProduct.tmul_smul, hd', ← TensorProduct.smul_tmul', ← Nat.cast_smul_eq_nsmul F, smul_smul, Nat.cast_mul]`.
-/
theorem GlobalTheory.RatHalfDense.tmul_split {F E A : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    (a : E) (α ι : A) (u : F) (N d : ℕ)
    (h : α = ((N * d : ℕ) : F) • algebraMap F A u + ((N * d : ℕ) : F) • ι) :
    a ⊗ₜ[F] α = (algebraMap F E (((N * d : ℕ) : F) * u) * a) ⊗ₜ[F] (1 : A) + N • (((d : E) * a) ⊗ₜ[F] ι) := by
  rw [h, TensorProduct.tmul_add]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one (A := A) u, smul_smul, ← Algebra.smul_def, TensorProduct.smul_tmul]
  · have hd' : (d : E) * a = (d : F) • a := by rw [Algebra.smul_def, map_natCast]
    rw [TensorProduct.tmul_smul, hd', ← TensorProduct.smul_tmul', ← Nat.cast_smul_eq_nsmul F, smul_smul, Nat.cast_mul]

namespace GlobalTheory.RatHalfDense

variable {D : D7}

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, GlobalTheory.LocM.Unim.mem_stdLat, intVec, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h k`. Take `⟨c, hc⟩` from `h k`.

Rewrite using `[← hc]`. Conclude with `c.isIntegral_coe`. Introduce `h k`. Conclude with `⟨⟨x k, h k⟩, rfl⟩`.
-/
theorem coe_stdLat (n : ℕ) :
    ((Formalism.L2.Pj.stdLat D.host.E n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, GlobalTheory.LocM.Unim.mem_stdLat, intVec, Set.mem_setOf_eq]
  constructor
  · intro h k
    obtain ⟨c, hc⟩ := h k
    rw [← hc]
    exact c.isIntegral_coe
  · intro h k
    exact ⟨⟨x k, h k⟩, rfl⟩

/- English proof (translation)
Take `⟨K, hK, h⟩` from `GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) (GlobalTheory.LocM.Unim.isLattice_stdLat (E := D.host.E) S.rank) (GlobalTheory.LocM.Unim.isLattice_stdLat (E := D.host.E) T.rank)`. Use `⟨K, hK, fun t h1 h2 => ?_⟩` and prove the remaining obligations. Use `h t h1 h2` as an intermediate fact. Rewrite `this` using `[coe_stdLat, coe_stdLat]`. Conclude with `this`.
-/
theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.LocM.Unim.isLattice_stdLat (E := D.host.E) S.rank) (GlobalTheory.LocM.Unim.isLattice_stdLat (E := D.host.E) T.rank)
  refine ⟨K, hK, fun t h1 h2 => ?_⟩
  have := h t h1 h2
  rw [coe_stdLat, coe_stdLat] at this
  exact this

/- English proof (translation)
Rewrite `he` using `[Formalism.IndefR.Eqv.infPart_eq_zero_iff_smul]`. Rewrite `hz` using `[Formalism.IndefR.Eqv.finPart_eq_zero_iff_smul]`. Rewrite using `[← he, ← hz, smul_mul_smul_comm]`. Establish `: Formalism.IndefR.Eqv.eFin D * Formalism.IndefR.Eqv.eInf D = 0`. Simplify using `only [Formalism.IndefR.Eqv.eFin, Formalism.IndefR.Eqv.eInf, pairA]`.

Conclude with `Prod.ext (show (0 : Ainf D.host.F) * 1 = 0 from zero_mul _) (show (1 : Af D.host.F) * 0 = 0 from mul_zero _)`. Rewrite using `[this, zero_smul]`.
-/
theorem mul_eq_zero_of_parts {e z : AE D} (he : infPart D e = 0) (hz : finPart D z = 0) : e * z = 0 := by
  rw [Formalism.IndefR.Eqv.infPart_eq_zero_iff_smul] at he
  rw [Formalism.IndefR.Eqv.finPart_eq_zero_iff_smul] at hz
  rw [← he, ← hz, smul_mul_smul_comm]
  have : Formalism.IndefR.Eqv.eFin D * Formalism.IndefR.Eqv.eInf D = 0 := by
    simp only [Formalism.IndefR.Eqv.eFin, Formalism.IndefR.Eqv.eInf, pairA]
    exact Prod.ext (show (0 : Ainf D.host.F) * 1 = 0 from zero_mul _) (show (1 : Af D.host.F) * 0 = 0 from mul_zero _)
  rw [this, zero_smul]

/- English proof (translation)
Establish `hz : IsAlgebraic ℤ z` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)`. Take `⟨y, hy, h⟩` from `hz.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[zsmul_eq_mul]`. Rewrite using `[← Int.cast_natCast]`.

Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite using `[← e]`. Conclude with `h`. Establish `e' : ((y.natAbs : ℕ) : ℤ) = -y` using `by omega`. Rewrite using `[e', Int.cast_neg, neg_mul]`.

Conclude with `h.neg`.
-/
theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, zero_mem _, by simp⟩`. Consider the case `tmul a α`. Take `⟨d, hd, hda⟩` from `exists_nat_mul_isIntegral a`. Establish `hc : ((N * d : ℕ) : D.host.F) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.mul_pos hN hd).ne'`.

Take `⟨u, hu⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele (R := NumberField.RingOfIntegers D.host.F) (K := D.host.F) (((N * d : ℕ) : D.host.F)⁻¹ • α)`. Establish `hα : α = ((N * d : ℕ) : D.host.F) • algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u + ((N * d : ℕ) : D.host.F) • (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u)`. Rewrite using `[smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]`. Use `⟨algebraMap D.host.F D.host.E (((N * d : ℕ) : D.host.F) * u) * a, ((d : D.host.E) * a) ⊗ₜ (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ((d : D.host.E) * a) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `Subring.subset_closure (Or.inl ⟨⟨(d : D.host.E) * a, ⟨⟨(d : D.host.E) * a, hda⟩, rfl⟩⟩, rfl⟩)`.

Establish `h2 : (1 : D.host.E) ⊗ₜ[D.host.F] (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩)`. Use `mul_mem h1 h2` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Then use the resulting hypothesis. Conclude with `tmul_split a α _ u N d hα`. Consider the case `add x y hx hy`.

Take `⟨γ₁, w₁, hw₁, h₁⟩` from `hx`. Take `⟨γ₂, w₂, hw₂, h₂⟩` from `hy`. Use `⟨γ₁ + γ₂, w₁ + w₂, add_mem hw₁ hw₂, ?_⟩` and prove the remaining obligations. Rewrite using `[h₁, h₂, map_add, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_rat_add_nsmul (z : EAf D) (N : ℕ) (hN : 0 < N) :
    ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, z = eToEAf D γ + N • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a α =>
    obtain ⟨d, hd, hda⟩ := exists_nat_mul_isIntegral a
    have hc : ((N * d : ℕ) : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos hN hd).ne'
    obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele
      (R := NumberField.RingOfIntegers D.host.F) (K := D.host.F) (((N * d : ℕ) : D.host.F)⁻¹ • α)
    have hα : α = ((N * d : ℕ) : D.host.F) • algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u
        + ((N * d : ℕ) : D.host.F) • (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
    refine ⟨algebraMap D.host.F D.host.E (((N * d : ℕ) : D.host.F) * u) * a,
      ((d : D.host.E) * a) ⊗ₜ (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u), ?_, ?_⟩
    · have h1 : ((d : D.host.E) * a) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨(d : D.host.E) * a, ⟨⟨(d : D.host.E) * a, hda⟩, rfl⟩⟩, rfl⟩)
      have h2 : (1 : D.host.E) ⊗ₜ[D.host.F] (((N * d : ℕ) : D.host.F)⁻¹ • α
          - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    · exact tmul_split a α _ u N d hα
  | add x y hx hy =>
    obtain ⟨γ₁, w₁, hw₁, h₁⟩ := hx
    obtain ⟨γ₂, w₂, hw₂, h₂⟩ := hy
    refine ⟨γ₁ + γ₂, w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [h₁, h₂, map_add, smul_add]
    abel

/- English proof (translation)
Take `⟨c, hc, hlat⟩` from `exists_nsmul_mem_stdHom S T`. Establish `hap : ∀ i j, ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (t i j) = eToEAf D γ + (K * c) • w` using `fun i j => exists_rat_add_nsmul _ (K * c) (Nat.mul_pos hK hc)`. Use `choose γ w hw heq using hap`. Use `choose y hy using fun i j => GlobalTheory.LocMod.exists_toEAf_lift (w i j)`. Establish `hidem` using `GlobalTheory.PlaceDatum.idemSum_mul_self hE`.

Establish `hinf` using `GlobalTheory.PlaceDatum.infPart_idemSum hE`. Set `m : WO S T` to `Matrix.of fun i j => E₂ * y i j`. Use `⟨Matrix.of γ, c • m, hlat m ?_ ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [m, Matrix.map_apply, Matrix.of_apply, map_mul, hinf, zero_mul, Matrix.zero_apply]`.

Introduce `i j`. Simplify using `only [m, Matrix.of_apply, map_mul, hy]`. Conclude with `mul_mem (GlobalTheory.ExportSeries.toEAf_mem_intAf_of_idem hidem) (hw i j)`. Introduce `i j`. Simplify using `only [m, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]`.

Take the linear combination `((c : AE D) * y i j) * hidem`. Use extensionality with `i j`. Establish `hfin : finPart D (t i j - incA D (γ i j) - (K * c) • y i j) = 0`. Establish `h0 : toEAf D (t i j - incA D (γ i j) - (K * c) • y i j) = 0`. Rewrite using `[map_sub, map_sub, nsmul_eq_mul, map_mul, map_natCast, GlobalTheory.IdemIntegral.toEAf_incA, hy, heq i j, nsmul_eq_mul]`.

Normalize the expressions using the abelian group laws. Unfold `toEAf at h0`. Rewrite `h0` using `[RingHom.comp_apply]`. Conclude with `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h0.trans (map_zero _).symm)`. Establish `hz` using `mul_eq_zero_of_parts hinf hfin`.

Rewrite `hz` using `[mul_sub, mul_sub, sub_sub, sub_eq_zero, ht i j]`. Simplify using `only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, m, Matrix.of_apply]`. Rewrite using `[hz]`. Use `congr 1`. Simplify using `only [nsmul_eq_mul, Nat.cast_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_half_approx {S T : HSp D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {E₂ : AE D} (hE : IsIdemSum E₂ Q)
    (K : ℕ) (hK : 0 < K) (t : WO S T) (ht : IsHalf E₂ t) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ stdHom S T, IsHalf E₂ u ∧
      t = γ.map (fun a => E₂ * incA D a) + K • u := by
  obtain ⟨c, hc, hlat⟩ := exists_nsmul_mem_stdHom S T
  have hap : ∀ i j, ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      toEAf D (t i j) = eToEAf D γ + (K * c) • w := fun i j => exists_rat_add_nsmul _ (K * c) (Nat.mul_pos hK hc)
  choose γ w hw heq using hap
  choose y hy using fun i j => GlobalTheory.LocMod.exists_toEAf_lift (w i j)
  have hidem := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hE
  let m : WO S T := Matrix.of fun i j => E₂ * y i j
  refine ⟨Matrix.of γ, c • m, hlat m ?_ ?_, ?_, ?_⟩
  · ext i j
    simp only [m, Matrix.map_apply, Matrix.of_apply, map_mul, hinf, zero_mul, Matrix.zero_apply]
  · intro i j
    simp only [m, Matrix.of_apply, map_mul, hy]
    exact mul_mem (GlobalTheory.ExportSeries.toEAf_mem_intAf_of_idem hidem) (hw i j)
  · intro i j
    simp only [m, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    linear_combination ((c : AE D) * y i j) * hidem
  · ext i j
    have hfin : finPart D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
      have h0 : toEAf D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
        rw [map_sub, map_sub, nsmul_eq_mul, map_mul, map_natCast, GlobalTheory.IdemIntegral.toEAf_incA, hy, heq i j,
          nsmul_eq_mul]
        abel
      unfold toEAf at h0
      rw [RingHom.comp_apply] at h0
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h0.trans (map_zero _).symm)
    have hz := mul_eq_zero_of_parts hinf hfin
    rw [mul_sub, mul_sub, sub_sub, sub_eq_zero, ht i j] at hz
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, m, Matrix.of_apply]
    rw [hz]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

/- English proof (translation)
Introduce `D S T Q E₂ hE Φ₁ Φ₂ h₁ h₂ hrat`. Take `⟨s₁, k₁, hk₁, inv₁, -⟩` from `h₁`. Take `⟨s₂, k₂, hk₂, inv₂, -⟩` from `h₂`. Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : IsHalf E₂ t`.

Take `⟨γ, u, hu, huh, rfl⟩` from `exists_half_approx hE (k₁ * k₂) (Nat.mul_pos hk₁ hk₂) t ht`. Establish `half_smul : ∀ n : ℕ, IsHalf E₂ (n • u)` using `fun n i j => by`. Simplify using `only [Matrix.smul_apply, nsmul_eq_mul]`. Rewrite using `[mul_left_comm, huh i j]`. Establish `e1 : Φ₁ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₁ (γ.map (fun a => E₂ * incA D a))`.

Rewrite using `[mul_smul]`. Conclude with `inv₁ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _`. Establish `e2 : Φ₂ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₂ (γ.map (fun a => E₂ * incA D a))`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `inv₂ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _`.

Rewrite using `[e1, e2, hrat]`. Establish `a1 : Φ₁ t = 0`. Assume the negation of the conclusion as `h`. Conclude with `ht (s₁ t h)`. Establish `a2 : Φ₂ t = 0`.

Assume the negation of the conclusion as `h`. Conclude with `ht (s₂ t h)`. Rewrite using `[a1, a2]`.
-/
theorem eq_of_rat : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
    ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ →
    (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  intro D S T Q E₂ hE Φ₁ Φ₂ h₁ h₂ hrat
  obtain ⟨s₁, k₁, hk₁, inv₁, -⟩ := h₁
  obtain ⟨s₂, k₂, hk₂, inv₂, -⟩ := h₂
  funext t
  by_cases ht : IsHalf E₂ t
  · obtain ⟨γ, u, hu, huh, rfl⟩ := exists_half_approx hE (k₁ * k₂) (Nat.mul_pos hk₁ hk₂) t ht
    have half_smul : ∀ n : ℕ, IsHalf E₂ (n • u) := fun n i j => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, huh i j]
    have e1 : Φ₁ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₁ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_smul]
      exact inv₁ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    have e2 : Φ₂ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₂ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_comm, mul_smul]
      exact inv₂ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    rw [e1, e2, hrat]
  · have a1 : Φ₁ t = 0 := by
      by_contra h
      exact ht (s₁ t h)
    have a2 : Φ₂ t = 0 := by
      by_contra h
      exact ht (s₂ t h)
    rw [a1, a2]

end GlobalTheory.RatHalfDense
