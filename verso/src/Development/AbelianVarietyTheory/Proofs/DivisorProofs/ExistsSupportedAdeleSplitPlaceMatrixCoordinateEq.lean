import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.VacLift

/- English proof (translation)
Establish `hp : ∀ (s : E →ₐ[F] Fv F v) (z : AE F E), piW s z = splitProj s (compFin F E v z)` using `fun s z => rfl`. Establish `hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : AE F E), piW s (u • z) = evFin F v u * piW s z`. Introduce `s u z`. Rewrite using `[Algebra.smul_def, map_mul]`. Use `congr 1`.

Rewrite using `[hp]`. Express the relevant statement in the definitionally equal form `splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _`. Rewrite using `[splitProj_tmul, map_one, mul_one]`. Use `⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`.

Rewrite using `[smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]`. Rewrite using `[hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]`. Simplify using `[splitIdem]`. Rewrite using `[hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]`. Simplify using `[splitIdem]`.
-/
theorem exists_lift_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (v : Pl F) (t : E →ₐ[F] Fv F v) (a : Fv F v) :
    ∃ z : AE F E, At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ piW t z = a := by
  have hp : ∀ (s : E →ₐ[F] Fv F v) (z : AE F E), piW s z = splitProj s (compFin F E v z) := fun s z => rfl
  have hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : AE F E), piW s (u • z) = evFin F v u * piW s z := by
    intro s u z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hp]
    change splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _
    rw [splitProj_tmul, map_one, mul_one]
  refine ⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]
    simp [splitIdem]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]
    simp [splitIdem]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d h v t b c Y`. Use `choose f hf using exists_lift_scalar h v t`. Use `⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Use extensionality with `i j`.

Conclude with `(hf _).1 u hu`. Conclude with `Matrix.ext fun i j => (hf _).2.1`. Establish `e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ` using `Matrix.ext fun i j => (hf _).2.2`. Rewrite using `[e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]`.
-/
theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  intro F E _ _ _ _ _ σ n d h v t b c Y
  choose f hf using exists_lift_scalar h v t
  refine ⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (hf _).1 u hu
  · exact Matrix.ext fun i j => (hf _).2.1
  · have e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ :=
      Matrix.ext fun i j => (hf _).2.2
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

end GlobalTheory.VacLift
