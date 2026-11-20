import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Introduce `F _ _ _ S T hS hST hA`. Establish `hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F), Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z` using `fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z`. Establish `hTS : ∀ v ∈ T, v ∉ S` using `fun v hv h => Finset.disjoint_left.1 hST h hv`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Take `⟨a, ha⟩` from `exists_unit_valuation_eq_of_adm F S T (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS (fun v hv => by simp [hv])`. Establish `haU : a ∈ sUnits F (S ∪ T)`. Rewrite using `[mem_sUnits]`. Introduce `v hv`. Rewrite `hv` using `[Finset.mem_union, not_or]`.

Rewrite using `[ha v hv.1]`. Simplify using `[hv.2]`. Establish `hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1`. Introduce `v hv`. Establish `hx0 : v.valuation F (x : F) ≠ 0` using `by simp`.

Rewrite using `[Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg, WithZero.exp_log hx0, inv_mul_cancel₀ hx0]`. Take `⟨u, hu, huA⟩` from `hA (T.filter fun v => ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))`. Establish `huU : u ∈ sUnits F (S ∪ T)`. Rewrite `hu`, the goal using `[mem_sUnits]`. Introduce `v hv`.

Conclude with `hu v fun h => hv (Finset.mem_union_left _ h)`. Establish `hsq : u * (a * x) ∈ finSq F T`. Simplify using `only [finSq, Subgroup.mem_iInf]`. Introduce `v hv`. Rewrite using `[mem_sqSub, Units.val_mul, map_mul]`.

Establish `h` using `huA v hv`. Rewrite `h` using `[Finset.mem_filter]`. Distinguish the cases in `hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))`. Conclude with `(h.2 fun hh => hh.2 hs).mul hs`. Use `isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs` and prove the remaining obligations.

Rewrite using `[← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]`. Conclude with `(hS v (hTS v hv)).1`. Rewrite using `[hval]`. Conclude with `(mem_sUnits F S u).1 hu v (hTS v hv)`. Rewrite using `[hval]`.

Conclude with `hy v hv`. Establish `hx : x = (u * a)⁻¹ * (u * (a * x))` using `by group`. Rewrite using `[hx]`. Conclude with `Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq`.
-/
theorem sUnits_union_sup_finSq_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by
  intro F _ _ _ S T hS hST hA
  classical
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  obtain ⟨u, hu, huA⟩ := hA (T.filter fun v =>
    ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))
  have huU : u ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits] at hu ⊢
    intro v hv
    exact hu v fun h => hv (Finset.mem_union_left _ h)
  have hsq : u * (a * x) ∈ finSq F T := by
    simp only [finSq, Subgroup.mem_iInf]
    intro v hv
    rw [mem_sqSub, Units.val_mul, map_mul]
    have h := huA v hv
    rw [Finset.mem_filter] at h
    by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))
    · exact (h.2 fun hh => hh.2 hs).mul hs
    · refine isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs
      · rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]
        exact (hS v (hTS v hv)).1
      · rw [hval]
        exact (mem_sUnits F S u).1 hu v (hTS v hv)
      · rw [hval]
        exact hy v hv
  have hx : x = (u * a)⁻¹ * (u * (a * x)) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq

end GlobalTheory.QNorm
