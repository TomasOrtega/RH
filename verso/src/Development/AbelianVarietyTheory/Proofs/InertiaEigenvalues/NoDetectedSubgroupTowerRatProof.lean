import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.DifferentGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCongruenceFiltrationFiniteTowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisKerLeRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeIndexMulCardMapInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictNormalHomMemLowerRamificationGroupZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrdIsEqCardInertia

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `l _ N hanti hopen h1 h2 h3`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨k₀, hk₀⟩` from `h3 8`. Establish `hex : ∃ k ≥ k₀, ∃ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ ∉ N (k + 1)`.

Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Take `⟨j, σ, hσ, hi, hj⟩` from `hcon k₀`. Establish `: ∀ i, σ ∈ N (k₀ + i)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => exact hσ`. Consider the case `succ i ih => exact hno (k₀ + i) (by omega) σ ih hi`. Conclude with `hj (hanti (by omega : j ≤ k₀ + j) (this j))`. Take `⟨k, hk, σ₀, hσ₀, hi₀, hn₀⟩` from `hex`.

Establish `hT : (N k).index ≠ 0`. Establish `: Finite (GQ l ⧸ N k)` using `Subgroup.quotient_finite_of_isOpen _ (hopen k)`. Conclude with `Subgroup.index_ne_zero_of_finite`. Use `set T := (N k).index with hTdef`. Use `choose ι hι x a hxa hdet using fun i : ℕ => hk₀ (k + i) (by omega)`.

Establish `hS : (⋃ i ∈ Set.Iic (2 * T), Set.range (x i)).Finite` using `(Set.finite_Iic _).biUnion fun i _ => by have := hι i; exact Set.finite_range _`. Take `⟨L, _, _, _, _, _, _, _, _, _, _, hker, hSL⟩` from `exists_galois_ker_le_range l (N (k + (2 * T + 8))) _ (hopen _) hS`. Use `set res : GQ l →* (L ≃ₐ[ℚ_[l]] L) := AlgEquiv.restrictNormalHom L with hres`. Use `set I := lowerRamificationGroup ℚ_[l] L 0 with hI`. Establish `hlift : ∀ j ≤ 2 * T + 8, ∀ σ : GQ l, res σ ∈ (N (k + j)).map res → σ ∈ N (k + j)`.

Introduce `j hj σ ⟨τ, hτ, e⟩`. Establish `h : τ⁻¹ * σ ∈ res.ker` using `by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]`. Establish `h' : τ⁻¹ * σ ∈ N (k + j)` using `hanti (by omega) (hker h)`. Simplify using `using (N (k + j)).mul_mem hτ h'`. Establish `hE : 0 < Nat.card I` using `Nat.card_pos`.

Establish `hfin` using `GlobalTheory.T.inertia_congruenceFiltration_finite_tower_bound ℚ_[l] L l (Nat.card I) T (fun j => (N (k + j)).map res ⊓ I) Fact.out hE (ordIs_eq_card_inertia l L) (GlobalTheory.T.axLemma_finiteGalois_padic l L) (fun i j hij => inf_le_inf_right _ (Subgroup.map_mono (hanti (by omeg …`. Introduce and unpack `_ ⟨⟨σ, hσ, rfl⟩, hσI⟩`. Conclude with `⟨⟨σ ^ l, h1 k σ hσ, map_pow _ _ _⟩, I.pow_mem hσI l⟩)`. Use the proof step `(by`. Introduce and unpack `j hj _ ⟨⟨σ, hσ, rfl⟩, hσI⟩ hp`.

Use `⟨⟨σ, h2 (k + j) σ (hanti (Nat.zero_le _) hσ) (hlift (j + 1) hj _ ?_), rfl⟩, hσI⟩` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `hp.1)`. Use the proof step `(by`. Introduce `i hi`.

Use `GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel l L 8 (N (k + i)) (N (k + i + 8)) I (ι i) (x i) (a i) (fun b => hSL (Set.mem_biUnion (show i ∈ Set.Iic (2 * T) from hi) ⟨b, rfl⟩)) (hxa i) (hdet i)` as an intermediate fact. Simplify `this)` using `[add_assoc]`. Establish `hidx` using `card_le_index_mul_card_map_inf (GQ l) (L ≃ₐ[ℚ_[l]] L) res (N k) I (AlgEquiv.restrictNormalHom_surjective _) hT`. Establish `hlt : T < 2 ^ T` using `Nat.lt_two_pow_self`. Establish `hpos : 0 < Nat.card ↥((N k).map res ⊓ I)` using `Nat.card_pos`.

Simplify using `only [add_zero] at hfin`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem noTowerQ_holds : NoTowerQ := by
  intro l _ N hanti hopen h1 h2 h3
  by_contra hcon
  push Not at hcon
  obtain ⟨k₀, hk₀⟩ := h3 8
  have hex : ∃ k ≥ k₀, ∃ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ ∉ N (k + 1) := by
    by_contra hno
    push Not at hno
    obtain ⟨j, σ, hσ, hi, hj⟩ := hcon k₀
    have : ∀ i, σ ∈ N (k₀ + i) := by
      intro i
      induction i with
      | zero => exact hσ
      | succ i ih => exact hno (k₀ + i) (by omega) σ ih hi
    exact hj (hanti (by omega : j ≤ k₀ + j) (this j))
  obtain ⟨k, hk, σ₀, hσ₀, hi₀, hn₀⟩ := hex
  have hT : (N k).index ≠ 0 := by
    have : Finite (GQ l ⧸ N k) := Subgroup.quotient_finite_of_isOpen _ (hopen k)
    exact Subgroup.index_ne_zero_of_finite
  set T := (N k).index with hTdef
  choose ι hι x a hxa hdet using fun i : ℕ => hk₀ (k + i) (by omega)
  have hS : (⋃ i ∈ Set.Iic (2 * T), Set.range (x i)).Finite :=
    (Set.finite_Iic _).biUnion fun i _ => by have := hι i; exact Set.finite_range _
  obtain ⟨L, _, _, _, _, _, _, _, _, _, _, hker, hSL⟩ :=
    exists_galois_ker_le_range l (N (k + (2 * T + 8))) _ (hopen _) hS
  set res : GQ l →* (L ≃ₐ[ℚ_[l]] L) := AlgEquiv.restrictNormalHom L with hres
  set I := lowerRamificationGroup ℚ_[l] L 0 with hI
  have hlift : ∀ j ≤ 2 * T + 8, ∀ σ : GQ l, res σ ∈ (N (k + j)).map res → σ ∈ N (k + j) := by
    intro j hj σ ⟨τ, hτ, e⟩
    have h : τ⁻¹ * σ ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    have h' : τ⁻¹ * σ ∈ N (k + j) := hanti (by omega) (hker h)
    simpa using (N (k + j)).mul_mem hτ h'
  have hE : 0 < Nat.card I := Nat.card_pos
  have hfin := GlobalTheory.T.inertia_congruenceFiltration_finite_tower_bound ℚ_[l] L l (Nat.card I) T (fun j => (N (k + j)).map res ⊓ I) Fact.out hE
    (ordIs_eq_card_inertia l L) (GlobalTheory.T.axLemma_finiteGalois_padic l L)
    (fun i j hij => inf_le_inf_right _ (Subgroup.map_mono (hanti (by omega)))) inf_le_right
    (fun h => hn₀ (hlift 1 (by omega) σ₀
      (h ⟨⟨σ₀, hσ₀, rfl⟩, restrictNormalHom_mem_lowerRamificationGroup_zero l L σ₀ hi₀⟩).1))
    (by
      rintro _ ⟨⟨σ, hσ, rfl⟩, hσI⟩
      exact ⟨⟨σ ^ l, h1 k σ hσ, map_pow _ _ _⟩, I.pow_mem hσI l⟩)
    (by
      rintro j hj _ ⟨⟨σ, hσ, rfl⟩, hσI⟩ hp
      refine ⟨⟨σ, h2 (k + j) σ (hanti (Nat.zero_le _) hσ) (hlift (j + 1) hj _ ?_), rfl⟩, hσI⟩
      rw [map_pow]; exact hp.1)
    (by
      intro i hi
      have := GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel l L 8 (N (k + i)) (N (k + i + 8)) I (ι i) (x i) (a i)
        (fun b => hSL (Set.mem_biUnion (show i ∈ Set.Iic (2 * T) from hi) ⟨b, rfl⟩)) (hxa i) (hdet i)
      simpa [add_assoc] using this)
  have hidx := card_le_index_mul_card_map_inf (GQ l) (L ≃ₐ[ℚ_[l]] L) res (N k) I
    (AlgEquiv.restrictNormalHom_surjective _) hT
  have hlt : T < 2 ^ T := Nat.lt_two_pow_self
  have hpos : 0 < Nat.card ↥((N k).map res ⊓ I) := Nat.card_pos
  simp only [add_zero] at hfin
  nlinarith

end GlobalTheory.PMon.Ram

end
