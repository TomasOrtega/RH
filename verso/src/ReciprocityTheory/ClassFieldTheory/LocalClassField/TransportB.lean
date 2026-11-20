import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBC

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime]
  (m : Model K p)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.isUniformiser_iff (π : Kˣ) : IsUniformiser K (π : K) ↔ vK p m.K' (m.eU π) = 1 := m.isUniformiser_iff_valuation_one π

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.isHomeomorph_eU : IsHomeomorph m.eU := m.isHomeomorph_units_model

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Model.exists_isGalIso : ∃ φ, m.IsGalIso φ := ⟨m.galIso, m.isGalIso_galIso⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.isFrobeniusLift_iff {φ} (hφ : m.IsGalIso φ) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    IsFrobeniusLift K g ↔ IsFrob p m.K' (φ g) := Model.isFrobeniusLift_iff_model hφ g

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.exists_abIso {φ} (hφ : m.IsGalIso φ) :
    ∃ ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K', IsHomeomorph ψ ∧
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g) := Model.exists_abelianization_iso hφ

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Model.exists_corr (L : IntermediateField K (AlgebraicClosure K)) :
    ∃ L' : IntermediateField ℚ_[p] (PadicAlgCl p), m.K' ≤ L' ∧ m.Corr L L' :=
  ⟨m.mapField L, (m.corr_mapField L).le, m.corr_mapField L⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Model.exists_corr' (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    ∃ L : IntermediateField K (AlgebraicClosure K), m.Corr L L' :=
  ⟨m.comapField L' h, m.corr_comapField L' h⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.isFiniteAbelian_iff {L : IntermediateField K (AlgebraicClosure K)}
    {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : m.Corr L L') :
    IsFiniteAbelian K L ↔ IsAbLK p m.K' L' := Model.isFiniteAbelian_iff_model h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.abRestrict_eq_one_iff {φ} (hφ : m.IsGalIso φ) {L : IntermediateField K (AlgebraicClosure K)}
    {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : m.Corr L L') (hL : IsFiniteAbelian K L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    abRestrict K L hL (toAb K g) = 1 ↔ φ g ∈ subG p m.K' L' := Model.abelian_restriction_eq_one_iff hφ h hL g

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Model.mem_normGroup_iff {L : IntermediateField K (AlgebraicClosure K)}
    {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : m.Corr L L') (hL : FiniteDimensional K L) (x : Kˣ) :
    x ∈ normGroup K L ↔ m.eU x ∈ normGrp p m.K' L' := Model.mem_normGroup_iff_model h hL x

end ReciprocityTheory.DiscreteGroups.LocalClassField
