import Mathlib
import Formalism.LocalToGlobal.Columns.RecLevelLocK
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

def OffRow (g : GL (Fin n) Rv) : Prop :=
  (∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v) ∧
    ∀ j, j ≠ lastIdx n → ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j = ιv pE * s

/- English proof (translation)
Apply the tactic sequence `have h1 := rll_inv_entry hc n v (Subgroup.inv_mem _ hg) i (lastIdx n)`. Rewrite `h1` using `[inv_inv]`. Take `⟨s, hs, e⟩` from `hi.2 i hne`. Use `⟨_, rll_sigV_mem hc v hs, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, e, map_mul, rll_sigV_incl]`.
-/
theorem offRow_col {g : GL (Fin n) Rv} (hg : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (hi : OffRow n (π := π) v g⁻¹) (i : Fin n) (hne : i ≠ lastIdx n) :
    ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s := by
  have h1 := rll_inv_entry hc n v (Subgroup.inv_mem _ hg) i (lastIdx n)
  rw [inv_inv] at h1
  obtain ⟨s, hs, e⟩ := hi.2 i hne
  refine ⟨_, rll_sigV_mem hc v hs, ?_⟩
  rw [h1, e, map_mul, rll_sigV_incl]

variable (h : BasePi ST π)
include h

/- English proof (translation)
Rewrite `hz`, the goal using `[rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)]`. Take `⟨h1, h2⟩` from `hz`. Establish `hzi : ∀ j, z j ∈ 𝒪v` using `fun j => by`. Distinguish the cases in `hj : j = lastIdx n`. Substitute `hj` using the available equality.

Rewrite using `[← rll_p_mul_pinv v h (z (lastIdx n))]`. Conclude with `mul_mem (rll_incl_int v π) h2`. Conclude with `h1 j hj`. Use `⟨fun i _ => ?_, ?_⟩` and prove the remaining obligations. Use `show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v`.

Conclude with `sum_mem fun j _ => mul_mem (hg.1 i j) (hzi j)`. Use `show ιv pE⁻¹ * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v`. Rewrite using `[Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = lastIdx n`.

Substitute `hj` using the available equality. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem (hg.1 _ _) h2`. Take `⟨s, hs, e⟩` from `hg.2 j hj`. Rewrite using `[e, mul_assoc, rll_pinv_mul v h]`.

Conclude with `mul_mem hs (h1 j hj)`.
-/
theorem offRow_maps_L {g : GL (Fin n) Rv} (hg : OffRow n (π := π) v g) (z : Fin n → Rv)
    (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  have hzi : ∀ j, z j ∈ 𝒪v := fun j => by
    by_cases hj : j = lastIdx n
    · subst hj
      rw [← rll_p_mul_pinv v h (z (lastIdx n))]
      exact mul_mem (rll_incl_int v π) h2
    · exact h1 j hj
  refine ⟨fun i _ => ?_, ?_⟩
  · show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v
    exact sum_mem fun j _ => mul_mem (hg.1 i j) (hzi j)
  show ιv pE⁻¹ * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  by_cases hj : j = lastIdx n
  · subst hj
    rw [mul_left_comm]; exact mul_mem (hg.1 _ _) h2
  · obtain ⟨s, hs, e⟩ := hg.2 j hj
    rw [e, mul_assoc, rll_pinv_mul v h]
    exact mul_mem hs (h1 j hj)

/- English proof (translation)
Establish `hq : star pE / pE ≠ 0` using `div_ne_zero h.star_ne_zero h.coe_ne_zero`. Establish `key : ιv (star pE) = ιv (star pE / pE) * ιv pE`. Rewrite using `[← map_mul, div_mul_cancel₀ _ h.coe_ne_zero]`. Establish `hcp : ιv (star pE) ∈ 𝒪v` using `rll_incl_int v (cO E π)`. Rewrite `hz`, the goal using `[rll_mem_loc_dLat n v _ hq]`.

Take `⟨h1, h2⟩` from `hz`. Prove the components needed by the constructor for the conclusion. Introduce `i hi show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = lastIdx n`.

Substitute `hj` using the available equality. Take `⟨s, hs, e⟩` from `hcol i hi`. Establish `e2 : (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) * z (lastIdx n) = ιv pE * s * (ιv (star pE / pE) * z (lastIdx n))`. Rewrite using `[e, key]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2]`. Conclude with `mul_mem (mul_mem (rll_incl_int v π) hs) h2`. Conclude with `mul_mem (hg.1 i j) (h1 j hj)`. Use `show ιv (star pE / pE) * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v`. Rewrite using `[Finset.mul_sum]`.

Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = lastIdx n`. Substitute `hj` using the available equality. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem (hg.1 _ _) h2`.

Take `⟨s, hs, e⟩` from `hg.2 j hj`. Establish `e2 : ιv (star pE / pE) * ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j) = ιv (star pE) * (s * z j)`. Rewrite using `[e, key]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `mul_mem hcp (mul_mem hs (h1 j hj))`.
-/
theorem offRow_maps_Ker {g : GL (Fin n) Rv} (hg : OffRow n (π := π) v g)
    (hcol : ∀ i, i ≠ lastIdx n → ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s)
    (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE))) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE)) := by
  have hq : star pE / pE ≠ 0 := div_ne_zero h.star_ne_zero h.coe_ne_zero
  have key : ιv (star pE) = ιv (star pE / pE) * ιv pE := by
    rw [← map_mul, div_mul_cancel₀ _ h.coe_ne_zero]
  have hcp : ιv (star pE) ∈ 𝒪v := rll_incl_int v (cO E π)
  rw [rll_mem_loc_dLat n v _ hq] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  constructor
  · intro i hi
    show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      obtain ⟨s, hs, e⟩ := hcol i hi
      have e2 : (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) * z (lastIdx n) =
          ιv pE * s * (ιv (star pE / pE) * z (lastIdx n)) := by
        rw [e, key]; ring
      rw [e2]
      exact mul_mem (mul_mem (rll_incl_int v π) hs) h2
    · exact mul_mem (hg.1 i j) (h1 j hj)
  · show ιv (star pE / pE) * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v
    rw [Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      rw [mul_left_comm]; exact mul_mem (hg.1 _ _) h2
    · obtain ⟨s, hs, e⟩ := hg.2 j hj
      have e2 : ιv (star pE / pE) * ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j) = ιv (star pE) * (s * z j) := by
        rw [e, key]; ring
      rw [e2]
      exact mul_mem hcp (mul_mem hs (h1 j hj))

end Loc

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n _ ST π h v g hU h1 h2`. Establish `hr1 : OffRow n (π` using `π) v g := h1`. Establish `hr2 : OffRow n (π` using `π) v g⁻¹ := h2`. Establish `hUi` using `Subgroup.inv_mem _ hU`. Establish `hcol` using `offRow_col hc n v hU hr2`.

Establish `hcol'` using `offRow_col hc n v hUi (by rw [inv_inv]; exact hr1)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rll_baseLb_eq n h]`. Conclude with `rll_stab_of_maps _ g (offRow_maps_L n v h hr1) (offRow_maps_L n v h hr2)`. Rewrite using `[rll_dualV_eq hc n v h]`.

Conclude with `rll_stab_of_maps _ g (rll_maps_Sh n v h hr1.1 hcol) (rll_maps_Sh n v h hr2.1 hcol')`. Rewrite using `[rll_baseKer_eq n h]`. Conclude with `rll_stab_of_maps _ g (offRow_maps_Ker n v h hr1 hcol) (offRow_maps_Ker n v h hr2 hcol')`.
-/
theorem unitary_offRow_stab_three :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → ((∀ i j, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → ((∀ i j, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧ g ∈ stabGL (baseDualV hc n ST v) ∧ g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
  intro F E _ _ _ _ _ _ hc n _ ST π h v g hU h1 h2
  have hr1 : OffRow n (π := π) v g := h1
  have hr2 : OffRow n (π := π) v g⁻¹ := h2
  have hUi := Subgroup.inv_mem _ hU
  have hcol := offRow_col hc n v hU hr2
  have hcol' := offRow_col hc n v hUi (by rw [inv_inv]; exact hr1)
  refine ⟨?_, ?_, ?_⟩
  · rw [rll_baseLb_eq n h]
    exact rll_stab_of_maps _ g (offRow_maps_L n v h hr1) (offRow_maps_L n v h hr2)
  · rw [rll_dualV_eq hc n v h]
    exact rll_stab_of_maps _ g (rll_maps_Sh n v h hr1.1 hcol) (rll_maps_Sh n v h hr2.1 hcol')
  · rw [rll_baseKer_eq n h]
    exact rll_stab_of_maps _ g (offRow_maps_Ker n v h hr1 hcol) (offRow_maps_Ker n v h hr2 hcol')

end GlobalTheory
