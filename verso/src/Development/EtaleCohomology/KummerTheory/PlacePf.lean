import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PlaceEx : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K],
  ∃ (T : ValuationSubring K) (σ : k →+* T), (∀ x, (σ x : K) = algebraMap k K x) ∧
    Function.Surjective ((IsLocalRing.residue T).comp σ)

def ValAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (T : ValuationSubring K), AIC T ∧ HenselianLocalRing T

/- English proof (translation)
Introduce `k K _ _ _ _ _`. Take `⟨T, σ, hσ, hs⟩` from `h1 k K`. Take `⟨hA, hH⟩` from `h2 K T`. Establish `hb : Function.Bijective ((IsLocalRing.residue T).comp σ)` using `⟨RingHom.injective _, hs⟩`. Use `⟨T, σ, hσ, hb, hA, hH, ?_⟩` and prove the remaining obligations.

Establish `: IsAlgClosed (IsLocalRing.ResidueField T)` using `IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)`. Use `infer_instance`.
-/
theorem Place_of (h1 : PlaceEx) (h2 : ValAIC) : Place := by
  intro k K _ _ _ _ _
  obtain ⟨T, σ, hσ, hs⟩ := h1 k K
  obtain ⟨hA, hH⟩ := h2 K T
  have hb : Function.Bijective ((IsLocalRing.residue T).comp σ) := ⟨RingHom.injective _, hs⟩
  refine ⟨T, σ, hσ, hb, hA, hH, ?_⟩
  have : IsAlgClosed (IsLocalRing.ResidueField T) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

end LateralTheory.KummerTheory
