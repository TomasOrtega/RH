import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace QPK

section
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem prodSet_eq_mul (N H : Set G) : prodSet N H = N * H := by
  ext s
  simp only [prodSet, Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem prodSet_isClosed {N H : Set G} (hN : IsClosed N) (hH : IsCompact H) :
    IsClosed (prodSet N H) := by
  rw [prodSet_eq_mul]
  first
    | exact hN.mul_isCompact hH
    | exact IsClosed.mul_isCompact hN hH
    | exact hN.mul_right_of_isCompact hH
    | exact IsClosed.mul_right_of_isCompact hN hH
    | exact hN.mul_isCompact_right hH
    | exact (hN.smul_left_of_isCompact hH)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Treat this case separately. Treat this case separately. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem prodSet_isGrp {N H : Set G} (hN : IsGrp N) (hH : IsGrp H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) : IsGrp (prodSet N H) := by
  obtain ⟨n1, nmul, ninv⟩ := hN
  obtain ⟨h1, hmul, hinv⟩ := hH
  refine ⟨⟨1, n1, 1, h1, (mul_one 1).symm⟩, ?_, ?_⟩
  · rintro _ ⟨m, hm, h, hh, rfl⟩ _ ⟨m', hm', h', hh', rfl⟩
    refine ⟨m * (h * m' * h⁻¹), nmul _ hm _ (hnorm h hh m' hm'), h * h', hmul _ hh _ hh', ?_⟩
    first
      | group
      | simp [mul_assoc]
  · rintro _ ⟨m, hm, h, hh, rfl⟩
    refine ⟨h⁻¹ * m⁻¹ * h⁻¹⁻¹, hnorm _ (hinv _ hh) _ (ninv _ hm), h⁻¹, hinv _ hh, ?_⟩
    first
      | group
      | simp [mul_assoc]
end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem locPack_of (hE : HaarExist) (hC : ConjInv) (hS : SMeas) (hB : Bruhat) (hW : LocWeil) :
    LocPack := by
  intro G _ _ _ _ _ _ _ _ muG _ N H hN hH gN gH hnorm hR
  obtain ⟨μN, hNinv, hNf, hNpos⟩ := hE G N hN gN
  obtain ⟨μH, hHinv, hHf, hHpos⟩ := hE G H hH.isClosed gH
  have hconj := hC G N H hN hH gN gH hnorm μN hNinv hNf hNpos
  obtain ⟨hPinv, hPf, hPpos, hPright, hPinvol⟩ :=
    hS G N H hN hH gN gH hnorm hR μN μH hNinv hNf hNpos hHinv hHf hHpos hconj
  obtain ⟨β, hβm, hβ⟩ := hB G (prodSet N H) (prodSet_isClosed hN hH) (prodSet_isGrp gN gH hnorm)
    (mulMap μN μH) hPinv hPf hPpos hPright
  refine ⟨μN, μH, β, hNinv, hHinv, hPinv, hβm, hβ, ?_⟩
  intro F hF
  haveI := hPf
  have hsf : SigmaFinite (mulMap μN μH) := by
    first
      | exact inferInstance
      | exact MeasureTheory.sigmaFinite_of_isFiniteMeasureOnCompacts _
  exact hW G muG (mulMap μN μH) hsf hPinvol β hβm hβ F hF

end QPK
