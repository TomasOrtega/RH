import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.StFam

/- English proof (translation)
Establish `one : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (V : X.Opens) (T : Thick (nlFun γ p X q κ)), St Q {V} T ↔ Q T ∧ …`. Introduce `O _ R _ I γ p X q κ Q V T`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hQ, W, hW, hT⟩`. Rewrite `hW` using `[Set.mem_singleton_iff]`.

Substitute `hW` using the available equality. Conclude with `⟨hQ, hT⟩`. Introduce and unpack `⟨hQ, hT⟩`. Conclude with `⟨hQ, V, rfl, hT⟩`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `O _ R _ I γ p X q κ Q ι U α T T' φ h h'`. Take `⟨β, hβ⟩` from `h'`. Conclude with `(one Q _ T').2 ⟨((one Q _ T').1 hβ).1, GlobalTheory.CompanionTheory.ThickPt.inU_map (U α) φ ((one Q _ T).1 h).2⟩`. Introduce `O _ R _ I γ p X q κ Q ι U`. Use function extensionality and compare the values at `T`.

Use `propext ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨α, hα⟩`. Take `⟨hQ, hT⟩` from `(one Q _ T).1 hα`. Conclude with `⟨hQ, U α, ⟨α, rfl⟩, hT⟩`. Introduce and unpack `⟨hQ, V, ⟨α, rfl⟩, hT⟩`.

Conclude with `⟨α, (one Q _ T).2 ⟨hQ, hT⟩⟩`. Introduce `O _ R _ I γ p X q κ Q ι U S hS`. Use function extensionality and compare the values at `T`. Use `propext ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Take `⟨a, ha⟩` from `hS`. Conclude with `(one Q _ T).2 ⟨((one Q _ T).1 (h a ha)).1, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).2 fun α hα => ((one Q _ T).1 (h α hα)).2⟩`. Introduce `h α hα`. Take `⟨hQ, hT⟩` from `(one Q _ T).1 h`. Conclude with `(one Q _ T).2 ⟨hQ, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).1 hT α hα⟩`.

Introduce `O _ R _ I γ p X q κ Q ι U n i`. Establish `key : ∀ T : Thick (nlFun γ p X q κ), InU (capO U i) T ↔ ∀ a, InU (U (i a)) T`. Introduce `T`. Establish `h` using `GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun a => U (i a)) (Finset.univ : Finset (Fin (n + 1))) T`. Establish `e : (⨅ a ∈ (Finset.univ : Finset (Fin (n + 1))), U (i a)) = capO U i`.

Simplify using `[capO]`. Rewrite `h` using `[e]`. Simplify using `using h`. Use function extensionality and compare the values at `T`. Use `propext ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Conclude with `(one Q _ T).2 ⟨((one Q _ T).1 (h 0)).1, (key T).2 fun a => ((one Q _ T).1 (h a)).2⟩`. Introduce `h a`. Take `⟨hQ, hT⟩` from `(one Q _ T).1 h`. Conclude with `(one Q _ T).2 ⟨hQ, (key T).1 hT a⟩`.
-/
theorem st_all :
    (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  have one : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
      {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
      (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (V : X.Opens) (T : Thick (nlFun γ p X q κ)),
      St Q {V} T ↔ Q T ∧ InU V T := by
    intro O _ R _ I γ p X q κ Q V T
    constructor
    · rintro ⟨hQ, W, hW, hT⟩
      rw [Set.mem_singleton_iff] at hW
      subst hW
      exact ⟨hQ, hT⟩
    · rintro ⟨hQ, hT⟩
      exact ⟨hQ, V, rfl, hT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O _ R _ I γ p X q κ Q ι U α T T' φ h h'
    obtain ⟨β, hβ⟩ := h'
    exact (one Q _ T').2 ⟨((one Q _ T').1 hβ).1, GlobalTheory.CompanionTheory.ThickPt.inU_map (U α) φ ((one Q _ T).1 h).2⟩
  · intro O _ R _ I γ p X q κ Q ι U
    funext T
    refine propext ⟨?_, ?_⟩
    · rintro ⟨α, hα⟩
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 hα
      exact ⟨hQ, U α, ⟨α, rfl⟩, hT⟩
    · rintro ⟨hQ, V, ⟨α, rfl⟩, hT⟩
      exact ⟨α, (one Q _ T).2 ⟨hQ, hT⟩⟩
  · intro O _ R _ I γ p X q κ Q ι U S hS
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      obtain ⟨a, ha⟩ := hS
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h a ha)).1,
        (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).2 fun α hα => ((one Q _ T).1 (h α hα)).2⟩
    · intro h α hα
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).1 hT α hα⟩
  · intro O _ R _ I γ p X q κ Q ι U n i
    have key : ∀ T : Thick (nlFun γ p X q κ), InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
      intro T
      have h := GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun a => U (i a)) (Finset.univ : Finset (Fin (n + 1))) T
      have e : (⨅ a ∈ (Finset.univ : Finset (Fin (n + 1))), U (i a)) = capO U i := by
        simp [capO]
      rw [e] at h
      simpa using h
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h 0)).1, (key T).2 fun a => ((one Q _ T).1 (h a)).2⟩
    · intro h a
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (key T).1 hT a⟩

end GlobalTheory.CompanionTheory.StFam
