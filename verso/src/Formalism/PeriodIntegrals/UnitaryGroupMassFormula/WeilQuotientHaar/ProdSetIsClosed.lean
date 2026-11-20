import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace QPK

section
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/- English proof (translation)
Use extensionality with `s`. Simplify using `only [prodSet, Set.mem_setOf_eq, Set.mem_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, h, hh, rfl⟩`. Conclude with `⟨m, hm, h, hh, rfl⟩`.

Introduce and unpack `⟨m, hm, h, hh, rfl⟩`. Conclude with `⟨m, hm, h, hh, rfl⟩`.
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
Rewrite using `[prodSet_eq_mul]`. Use `first`. Consider the case `exact hN.mul_isCompact hH`. Consider the case `exact IsClosed.mul_isCompact hN hH`. Consider the case `exact hN.mul_right_of_isCompact hH`.

Consider the case `exact IsClosed.mul_right_of_isCompact hN hH`. Consider the case `exact hN.mul_isCompact_right hH`. Consider the case `exact (hN.smul_left_of_isCompact hH)`.
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
Take `⟨n1, nmul, ninv⟩` from `hN`. Take `⟨h1, hmul, hinv⟩` from `hH`. Use `⟨⟨1, n1, 1, h1, (mul_one 1).symm⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, h, hh, rfl⟩ _ ⟨m', hm', h', hh', rfl⟩`. Use `⟨m * (h * m' * h⁻¹), nmul _ hm _ (hnorm h hh m' hm'), h * h', hmul _ hh _ hh', ?_⟩` and prove the remaining obligations.

Use `first`. Consider the case `group`. Consider the case `simp [mul_assoc]`. Introduce and unpack `_ ⟨m, hm, h, hh, rfl⟩`. Use `⟨h⁻¹ * m⁻¹ * h⁻¹⁻¹, hnorm _ (hinv _ hh) _ (ninv _ hm), h⁻¹, hinv _ hh, ?_⟩` and prove the remaining obligations.

Use `first`. Consider the case `group`. Consider the case `simp [mul_assoc]`.
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
Introduce `G _ _ _ _ _ _ _ _ muG _ N H hN hH gN gH hnorm hR`. Take `⟨μN, hNinv, hNf, hNpos⟩` from `hE G N hN gN`. Take `⟨μH, hHinv, hHf, hHpos⟩` from `hE G H hH.isClosed gH`. Establish `hconj` using `hC G N H hN hH gN gH hnorm μN hNinv hNf hNpos`. Take `⟨hPinv, hPf, hPpos, hPright, hPinvol⟩` from `hS G N H hN hH gN gH hnorm hR μN μH hNinv hNf hNpos hHinv hHf hHpos hconj`.

Take `⟨β, hβm, hβ⟩` from `hB G (prodSet N H) (prodSet_isClosed hN hH) (prodSet_isGrp gN gH hnorm) (mulMap μN μH) hPinv hPf hPpos hPright`. Use `⟨μN, μH, β, hNinv, hHinv, hPinv, hβm, hβ, ?_⟩` and prove the remaining obligations. Introduce `F hF`. Use `haveI := hPf`. Establish `hsf : SigmaFinite (mulMap μN μH)` using `by first`.

Consider the case `exact inferInstance`. Consider the case `exact MeasureTheory.sigmaFinite_of_isFiniteMeasureOnCompacts _`. Conclude with `hW G muG (mulMap μN μH) hsf hPinvol β hβm hβ F hF`.
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
