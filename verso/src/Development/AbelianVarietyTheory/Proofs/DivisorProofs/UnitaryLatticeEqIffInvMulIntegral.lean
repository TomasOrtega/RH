import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsLoc
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitLat

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `h (Pi.single j 1) (fun k => by` as an intermediate fact. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using `using Subring.one_mem _`. Simplify `Subring.zero_mem _) i` using `[hk]`. Simplify `this` using `[Matrix.mulVec_single]`. Introduce `h u hu i`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hu j)`.
-/
theorem mulVec_int_iff {K : UQ} {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E) :
    (∀ u : Fin n → K.E, (∀ i, u i ∈ (algebraMap K.O K.E).range) →
      ∀ i, (P *ᵥ u) i ∈ (algebraMap K.O K.E).range) ↔
    ∀ i j, P i j ∈ (algebraMap K.O K.E).range := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simpa using Subring.one_mem _
      · simpa [hk] using Subring.zero_mem _) i
    simpa [Matrix.mulVec_single] using this
  · intro h u hu i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hu j)

/- English proof (translation)
Introduce `E _ _ _ _ w _ K e _ hint n B ψ q q'`. Set `R` to `(algebraMap K.O K.E).range`. Set `M : GLw n w → Matrix (Fin n) (Fin n) K.E` to `fun g => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm`. Establish `hMmul : ∀ g h : GLw n w, M (g * h) = M g * M h` using `fun g h => by`. Simplify using `only [M, Units.val_mul]`.

Conclude with `Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))`. Establish `hM1 : M 1 = 1`. Simplify using `only [M, Units.val_one]`. Conclude with `Matrix.map_one (f := e.symm) (map_zero _) (map_one _)`. Establish `hent : ∀ g : GLw n w, (∀ i j, M g i j ∈ R) ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w`.

Introduce `g`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Use `show e.symm _ ∈ R ↔ _`. Rewrite using `[hint, RingEquiv.apply_symm_apply]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm`.

Establish `hmem : ∀ g : UL n w, ∀ y, y ∈ unitLat e B ψ g ↔ ∀ i, (M ((g : GLw n w)⁻¹) *ᵥ ψ y) i ∈ R` using `fun g y => Iff.rfl`. Establish `hlat : unitLat e B ψ q = unitLat e B ψ q' ↔ ∀ v : Fin n → K.E, ((∀ i, (M ((q : GLw n w)⁻¹) *ᵥ v) i ∈ R) ↔ ∀ i, (M ((q' : GLw n w)⁻¹) *ᵥ v) i ∈ R)`. Rewrite using `[SetLike.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`.

Use `h (ψ.symm v)` as an intermediate fact. Rewrite `this` using `[hmem, hmem, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `h y`. Rewrite using `[hmem, hmem]`. Conclude with `h (ψ y)`.

Establish `half : ∀ a b : GLw n w, (∀ v : Fin n → K.E, (∀ i, (M b⁻¹ *ᵥ v) i ∈ R) → ∀ i, (M a⁻¹ *ᵥ v) i ∈ R) ↔ ∀ i j, M (a⁻¹ * b) i j ∈ R`. Introduce `a b`. Rewrite using `[← mulVec_int_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h u hu`.

Establish `h1` using `h (M b *ᵥ u) (by`. Rewrite using `[Matrix.mulVec_mulVec, ← hMmul, inv_mul_cancel, hM1, Matrix.one_mulVec]`. Conclude with `hu)`. Rewrite `h1` using `[Matrix.mulVec_mulVec, ← hMmul]`. Then use the resulting hypothesis. Introduce `h v hv`.

Establish `h1` using `h _ hv`. Rewrite `h1` using `[Matrix.mulVec_mulVec, ← hMmul, mul_assoc, mul_inv_cancel, mul_one]`. Then use the resulting hypothesis. Establish `hKL : q⁻¹ * q' ∈ KL n w ↔ ((q : GLw n w)⁻¹ * q') ∈ Formalism.UG.GLint (Fin n) (Ov E w)`. Rewrite using `[KL, Subgroup.mem_subgroupOf]`. Both sides reduce to the same expression.

Rewrite using `[hKL, Formalism.UG.P.tjcosets_mem_K_iff, ← hent, ← hent, hlat]`. Establish `hinv : ((q : GLw n w)⁻¹ * q')⁻¹ = (q' : GLw n w)⁻¹ * q` using `by group`. Rewrite using `[hinv, ← half, ← half]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨fun v hv => (h v).2 hv, fun v hv => (h v).1 hv⟩`. Introduce `h v`. Conclude with `⟨h.2 v, h.1 v⟩`.
-/
theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  intro E _ _ _ _ w _ K e _ hint n B ψ q q'
  let R := (algebraMap K.O K.E).range
  let M : GLw n w → Matrix (Fin n) (Fin n) K.E := fun g => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm
  have hMmul : ∀ g h : GLw n w, M (g * h) = M g * M h := fun g h => by
    simp only [M, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hM1 : M 1 = 1 := by
    simp only [M, Units.val_one]
    exact Matrix.map_one (f := e.symm) (map_zero _) (map_one _)
  have hent : ∀ g : GLw n w, (∀ i j, M g i j ∈ R) ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
    intro g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    show e.symm _ ∈ R ↔ _
    rw [hint, RingEquiv.apply_symm_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hmem : ∀ g : UL n w, ∀ y, y ∈ unitLat e B ψ g ↔ ∀ i, (M ((g : GLw n w)⁻¹) *ᵥ ψ y) i ∈ R :=
    fun g y => Iff.rfl

  have hlat : unitLat e B ψ q = unitLat e B ψ q' ↔
      ∀ v : Fin n → K.E, ((∀ i, (M ((q : GLw n w)⁻¹) *ᵥ v) i ∈ R) ↔ ∀ i, (M ((q' : GLw n w)⁻¹) *ᵥ v) i ∈ R) := by
    rw [SetLike.ext_iff]
    constructor
    · intro h v
      have := h (ψ.symm v)
      rwa [hmem, hmem, LinearEquiv.apply_symm_apply] at this
    · intro h y
      rw [hmem, hmem]
      exact h (ψ y)

  have half : ∀ a b : GLw n w,
      (∀ v : Fin n → K.E, (∀ i, (M b⁻¹ *ᵥ v) i ∈ R) → ∀ i, (M a⁻¹ *ᵥ v) i ∈ R) ↔
      ∀ i j, M (a⁻¹ * b) i j ∈ R := by
    intro a b
    rw [← mulVec_int_iff]
    constructor
    · intro h u hu
      have h1 := h (M b *ᵥ u) (by
        rw [Matrix.mulVec_mulVec, ← hMmul, inv_mul_cancel, hM1, Matrix.one_mulVec]; exact hu)
      rwa [Matrix.mulVec_mulVec, ← hMmul] at h1
    · intro h v hv
      have h1 := h _ hv
      rwa [Matrix.mulVec_mulVec, ← hMmul, mul_assoc, mul_inv_cancel, mul_one] at h1
  have hKL : q⁻¹ * q' ∈ KL n w ↔
      ((q : GLw n w)⁻¹ * q') ∈ Formalism.UG.GLint (Fin n) (Ov E w) := by
    rw [KL, Subgroup.mem_subgroupOf]
    rfl
  rw [hKL, Formalism.UG.P.tjcosets_mem_K_iff, ← hent, ← hent, hlat]
  have hinv : ((q : GLw n w)⁻¹ * q')⁻¹ = (q' : GLw n w)⁻¹ * q := by group
  rw [hinv, ← half, ← half]
  constructor
  · intro h
    exact ⟨fun v hv => (h v).2 hv, fun v hv => (h v).1 hv⟩
  · intro h v
    exact ⟨h.2 v, h.1 v⟩

end GlobalTheory.InertUnitLat
