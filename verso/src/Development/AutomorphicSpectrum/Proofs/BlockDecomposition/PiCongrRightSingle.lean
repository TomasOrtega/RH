import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBaseChangeEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPowerSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerPushoutSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEquivBaseChangeTensor

open TensorProduct CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OmKun

/- English proof (translation)
Use function extensionality and compare the values at `b`. Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem piCongrRight_single {K ι : Type} [CommRing K] [DecidableEq ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (f : ∀ i, X i ≃ₗ[K] Y i) (a : ι) (x : X a) :
    LinearEquiv.piCongrRight f (Pi.single a x) = Pi.single a (f a x) := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Take `⟨r, π, h1, h2, h3, h4, h5⟩` from `GlobalTheory.CompanionTheory.KaehlerPushout.kaehler_pushout_split K A B R`. Take `⟨E, hE⟩` from `GlobalTheory.CompanionTheory.TopExtSplit.exteriorPower_split R _ _ _ _ _ r π h1 h2 h3 h4 h5 c`. Use `choose bA hbA using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv A R (Ω[A⁄K]) a`. Use `choose bB hbB using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv B R (Ω[B⁄K]) a`. Use `choose t ht using fun a : Fin (c + 1) => GlobalTheory.CompanionTheory.TensorPushout.tensor_equiv_baseChange_tensor K A B R (Om K A a) (Om K B (c - a))`.

Use `⟨LinearEquiv.piCongrRight (fun a => t a ≪≫ₗ (TensorProduct.congr (bA a) (bB (c - a))).restrictScalars K) ≪≫ₗ E.restrictScalars K, ?_⟩` and prove the remaining obligations. Introduce `a g₀ g h₀ h`. Establish `hA : bA a ((1 : R) ⊗ₜ[A] form K g₀ g) = algebraMap A R g₀ • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k))`. Unfold `form`. Rewrite using `[← TensorProduct.smul_tmul, hbA, Algebra.smul_def, mul_one]`.

Establish `hB : bB (c - a) ((1 : R) ⊗ₜ[B] form K h₀ h) = algebraMap B R h₀ • exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k))`. Unfold `form`. Rewrite using `[← TensorProduct.smul_tmul, hbB, Algebra.smul_def, mul_one]`. Establish `hmain : (TensorProduct.congr (bA a) (bB (c - a))) (((1 : R) ⊗ₜ[A] form K g₀ g) ⊗ₜ[R] ((1 : R) ⊗ₜ[B] form K h₀ h)) = (algebraMap A R g₀ * algebraMap B R h₀) • (exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) ⊗ₜ[R] exteriorPower.ιMulti R (c - a) (f …`. Rewrite using `[TensorProduct.congr_tmul, hA, hB, TensorProduct.smul_tmul_smul]`.

Simplify using `only [LinearEquiv.trans_apply, piCongrRight_single, LinearEquiv.restrictScalars_apply, ht, hmain, Pi.single_smul, map_smul, hE]`. Unfold `form`. Use `congr 2`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp]`.

Generalize the expression as in `Fin.cast _ k = j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j => simp [KaehlerDifferential.mapBaseChange_tmul]`. Consider the case `right j => simp [KaehlerDifferential.mapBaseChange_tmul]`.
-/
theorem omKun_pushout (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R] (c : ℕ) :
    ∃ e : (∀ a : Fin (c + 1), TensorProduct K (Om K A a) (Om K B (c - a))) ≃ₗ[K] Om K R c,
      ∀ (a : Fin (c + 1)) (g₀ : A) (g : Fin a → A) (h₀ : B) (h : Fin (c - a) → B),
        e (Pi.single a (form K g₀ g ⊗ₜ form K h₀ h)) = form K (algebraMap A R g₀ * algebraMap B R h₀)
          (Fin.append (fun k => algebraMap A R (g k)) (fun k => algebraMap B R (h k)) ∘
            Fin.cast (by have := a.2; omega)) := by
  obtain ⟨r, π, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.KaehlerPushout.kaehler_pushout_split K A B R
  obtain ⟨E, hE⟩ := GlobalTheory.CompanionTheory.TopExtSplit.exteriorPower_split R _ _ _ _ _ r π h1 h2 h3 h4 h5 c
  choose bA hbA using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv A R (Ω[A⁄K]) a
  choose bB hbB using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv B R (Ω[B⁄K]) a
  choose t ht using fun a : Fin (c + 1) => GlobalTheory.CompanionTheory.TensorPushout.tensor_equiv_baseChange_tensor K A B R (Om K A a) (Om K B (c - a))
  refine ⟨LinearEquiv.piCongrRight (fun a => t a ≪≫ₗ
    (TensorProduct.congr (bA a) (bB (c - a))).restrictScalars K) ≪≫ₗ E.restrictScalars K, ?_⟩
  intro a g₀ g h₀ h
  have hA : bA a ((1 : R) ⊗ₜ[A] form K g₀ g) = algebraMap A R g₀ •
      exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbA, Algebra.smul_def, mul_one]
  have hB : bB (c - a) ((1 : R) ⊗ₜ[B] form K h₀ h) = algebraMap B R h₀ •
      exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbB, Algebra.smul_def, mul_one]
  have hmain : (TensorProduct.congr (bA a) (bB (c - a))) (((1 : R) ⊗ₜ[A] form K g₀ g) ⊗ₜ[R]
      ((1 : R) ⊗ₜ[B] form K h₀ h)) = (algebraMap A R g₀ * algebraMap B R h₀) •
        (exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) ⊗ₜ[R]
        exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k))) := by
    rw [TensorProduct.congr_tmul, hA, hB, TensorProduct.smul_tmul_smul]
  simp only [LinearEquiv.trans_apply, piCongrRight_single, LinearEquiv.restrictScalars_apply, ht,
    hmain, Pi.single_smul, map_smul, hE]
  unfold form
  congr 2
  funext k
  simp only [Function.comp]
  generalize Fin.cast _ k = j
  induction j using Fin.addCases with
  | left j => simp [KaehlerDifferential.mapBaseChange_tmul]
  | right j => simp [KaehlerDifferential.mapBaseChange_tmul]

/- English proof (translation)
Introduce `K A B _ _ _ _ _ c`. Set `_ : Algebra B (A ⊗[K] B)` to `Algebra.TensorProduct.rightAlgebra`. Establish `: IsScalarTower K B (A ⊗[K] B)` using `Algebra.TensorProduct.right_isScalarTower`. Take `⟨e, he⟩` from `omKun_pushout K A B (A ⊗[K] B) c`. Use `⟨e, fun a g₀ g h₀ h => ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `g₀ ⊗ₜ[K] (1 : B) * (1 : A) ⊗ₜ[K] h₀ = _`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem omKun : CrystallineSemistableComparison.Onto.OmKun := by
  intro K A B _ _ _ _ _ c
  let _ : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower K B (A ⊗[K] B) := Algebra.TensorProduct.right_isScalarTower
  obtain ⟨e, he⟩ := omKun_pushout K A B (A ⊗[K] B) c
  refine ⟨e, fun a g₀ g h₀ h => ?_⟩
  rw [he]
  congr 1
  change g₀ ⊗ₜ[K] (1 : B) * (1 : A) ⊗ₜ[K] h₀ = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.CompanionTheory.OmKun
