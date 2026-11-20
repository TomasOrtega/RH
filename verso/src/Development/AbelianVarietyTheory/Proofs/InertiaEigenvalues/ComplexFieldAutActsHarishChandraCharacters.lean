import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.FieldAut

section Rep

variable {G : Type} [Group G]

def galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  ((Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin (Module.finrank ℂ V))).toMulEquiv.toMonoidHom).comp
    (((σ : ℂ →+* ℂ).mapMatrix (m := Fin (Module.finrank ℂ V))).toMonoidHom.comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toMulEquiv.toMonoidHom).comp V.ρ))

/- English proof (translation)
Establish `h1 : galRep σ V x = Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).map σ)` using `rfl`. Establish `h2 : V.character x = (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).trace` using `LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (V.ρ x)`. Rewrite using `[h1, Matrix.trace_toLin'_eq, h2]`. Simplify using `[Matrix.trace]`.
-/
theorem trace_galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) (x : G) :
    LinearMap.trace ℂ _ (galRep σ V x) = σ (V.character x) := by
  have h1 : galRep σ V x =
      Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).map σ) := rfl
  have h2 : V.character x =
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (V.ρ x)
  rw [h1, Matrix.trace_toLin'_eq, h2]
  simp [Matrix.trace]

variable [Fintype G]

/- English proof (translation)
Take `⟨V, hs, hV⟩` from `h`. Establish `hW : ∀ x, (FDRep.of (galRep σ V)).character x = σ (V.character x)` using `fun x => trace_galRep σ V x`. Use `⟨FDRep.of (galRep σ V), ?_, fun x => by rw [hW, hV]; rfl⟩` and prove the remaining obligations. Rewrite using `[FDRep.simple_iff_char_is_norm_one]`. Establish `h` using `congrArg σ ((FDRep.simple_iff_char_is_norm_one V).1 hs)`.

Rewrite `h` using `[map_natCast, map_sum]`. Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [map_mul, hW, hW]`.
-/
theorem isIrr_comp (σ : ℂ ≃+* ℂ) {χ : G → ℂ} (h : IsIrr χ) : IsIrr (σ ∘ χ) := by
  obtain ⟨V, hs, hV⟩ := h
  have hW : ∀ x, (FDRep.of (galRep σ V)).character x = σ (V.character x) := fun x => trace_galRep σ V x
  refine ⟨FDRep.of (galRep σ V), ?_, fun x => by rw [hW, hV]; rfl⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  have h := congrArg σ ((FDRep.simple_iff_char_is_norm_one V).1 hs)
  rw [map_natCast, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => by rw [map_mul, hW, hW]

/- English proof (translation)
Simplify using `only [zOf, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem coeff_zOf (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Finsupp.mapRange_apply, coeff_zOf, coeff_zOf]`. Simplify using `only [Function.comp, map_mul, map_div₀, map_natCast]`.
-/
theorem mapRange_zOf (σ : ℂ ≃+* ℂ) (χ : G → ℂ) :
    (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff := by
  ext y
  rw [Finsupp.mapRange_apply, coeff_zOf, coeff_zOf]
  simp only [Function.comp, map_mul, map_div₀, map_natCast]

/- English proof (translation)
Simplify using `only [ip, Function.comp, map_mul, map_sum, map_inv₀, map_natCast]`.
-/
theorem ip_comp (σ : ℂ ≃+* ℂ) (α β : G → ℂ) : ip (σ ∘ α) (σ ∘ β) = σ (ip α β) := by
  simp only [ip, Function.comp, map_mul, map_sum, map_inv₀, map_natCast]

end Rep

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [hc, hcT, Function.comp, map_mul, map_sum, map_inv₀, map_natCast, apply_ite σ, map_zero]`.
-/
theorem hc_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) :
    hc a b (σ ∘ α) (σ ∘ β) n = σ ∘ hc a b α β n := by
  funext x
  simp only [hc, hcT, Function.comp, map_mul, map_sum, map_inv₀, map_natCast, apply_ite σ, map_zero]

/- English proof (translation)
Simplify using `[degL, List.map_map, Function.comp_def]`.
-/
theorem degL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) = degL L := by
  simp [degL, List.map_map, Function.comp_def]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Introduce `n`. Use function extensionality and compare the values at `x`. Simplify using `[hcL_nil]`.

Consider the case `cons p L ih`. Introduce `n`. Use `show hc p.1 (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g))) (σ ∘ p.2) (hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)))) n = _`. Rewrite using `[degL_map, ih, hc_comp, hcL_cons]`.
-/
theorem hcL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    ∀ n, hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n := by
  induction L with
  | nil =>
    intro n
    funext x
    simp [hcL_nil]
  | cons p L ih =>
    intro n
    show hc p.1 (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g))) (σ ∘ p.2)
      (hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)))) n = _
    rw [degL_map, ih, hc_comp, hcL_cons]

/- English proof (translation)
Simplify using `only [res, Function.comp, map_mul, map_sum, map_inv₀, map_pow, map_natCast, apply_ite σ, map_zero]`.
-/
theorem res_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b (σ ∘ χ) h₁ h₂ = σ (res a b χ h₁ h₂) := by
  simp only [res, Function.comp, map_mul, map_sum, map_inv₀, map_pow, map_natCast, apply_ite σ, map_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, isIrr_comp σ h.2.1, fun a ha ha' => by rw [res_comp, h.2.2 a ha ha', map_zero]⟩`.
-/
theorem isCusp_comp (σ : ℂ ≃+* ℂ) {d : ℕ} {χ : Gn g d → ℂ} (h : IsCusp χ) : IsCusp (σ ∘ χ) :=
  ⟨h.1, isIrr_comp σ h.2.1, fun a ha ha' => by rw [res_comp, h.2.2 a ha ha', map_zero]⟩

end GlobalTheory.CompanionTheory.FieldAut

/- English proof (translation)
Introduce `g _ σ`. Conclude with `⟨fun G _ _ χ => ⟨GlobalTheory.CompanionTheory.FieldAut.isIrr_comp σ, GlobalTheory.CompanionTheory.FieldAut.mapRange_zOf σ χ, GlobalTheory.CompanionTheory.FieldAut.ip_comp σ χ⟩, fun L n => GlobalTheory.CompanionTheory.FieldAut.hcL_map σ L n, fun d χ h => GlobalTheory.CompanionTheo …`.
-/
theorem GlobalTheory.CompanionTheory.FieldAut.action : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  intro g _ σ
  exact ⟨fun G _ _ χ => ⟨GlobalTheory.CompanionTheory.FieldAut.isIrr_comp σ, GlobalTheory.CompanionTheory.FieldAut.mapRange_zOf σ χ,
    GlobalTheory.CompanionTheory.FieldAut.ip_comp σ χ⟩, fun L n => GlobalTheory.CompanionTheory.FieldAut.hcL_map σ L n,
    fun d χ h => GlobalTheory.CompanionTheory.FieldAut.isCusp_comp σ h⟩

end
end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FieldAut.action | exact GlobalTheory.CompanionTheory.FieldAut.action | (intros; apply GlobalTheory.CompanionTheory.FieldAut.action <;> assumption)`.
-/
theorem _root_.GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.CompanionTheory.FieldAut.action | exact GlobalTheory.CompanionTheory.FieldAut.action | (intros; apply GlobalTheory.CompanionTheory.FieldAut.action <;> assumption)

end
