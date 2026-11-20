import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrLift

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_Hs (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

/- English proof (translation)
Simplify using `only [cr_Hs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem cr_mem_Hs (E : GLOps n K V) (lam : Fin n → ℤ) (x : V) :
    x ∈ cr_Hs E lam ↔ x ∈ weightSp E lam ∧ ∀ a b : Fin n, a < b → E a b x = 0 := by
  simp only [cr_Hs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Use `choose Q hQ using fun lam : Fin n → ℤ => Submodule.exists_isCompl (cr_Hs E lam ⊓ W)`. Use `set H' : (Fin n → ℤ) → Submodule K V := fun lam => cr_Hs E lam ⊓ Q lam with hH'`. Use `set W' : Submodule K V := ⨆ lam, isotypicPartIn E (H' lam) lam with hW'`. Establish `hW'st : IsStableUnderOperators E W'` using `v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E (H' mu) mu`. Use `⟨W', ⟨?_, ?_⟩, hW'st⟩` and prove the remaining obligations.

Rewrite using `[disjoint_iff]`. Assume the negation of the conclusion as `hne`. Establish `hst : IsStableUnderOperators E (W ⊓ W')` using `fun a b x hx => ⟨hW a b x hx.1, hW'st a b x hx.2⟩`. Take `⟨lam, w, hwm, hw⟩` from `v2rep_exists_hwv E hR (W ⊓ W') hst (le_top.trans hT.ge) hne`. Establish `hdl : Dominant lam` using `cr_hwv_dom E hR hw`.

Take `⟨r, hr1, hr2⟩` from `casimir_polynomial_isolates_level E hR H' w hwm.2 (cr_c lam)`. Rewrite `hr2` using `[cr_aeval_eig (cr_C E) _ w (cr_C_hwv E hR lam w hw) r, hr1, one_smul]`. Establish `hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c lam}, isotypicPartIn E (H' ν) ν) ≤ H' lam ⊔ cr_WS E {τ | τ ≠ lam}`. Use `iSup₂_le fun ν hν x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hνl : ν = lam`.

Substitute `hνl` using the available equality. Establish `hsub : cr_Low ν ⊆ {τ | τ ≠ ν}`. Introduce `τ hτ h`. Establish `h2` using `hτ.2`. Rewrite `h2` using `[h, sub_self, cr_ht_zero]`.

Conclude with `lt_irrefl _ h2`. Conclude with `(sup_le_sup inf_le_left (cr_WS_mono E hsub)) (cr_isoIn_le E hR (H' ν) ν hx)`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `zero_mem _`.

Establish `hd` using `cr_isoIn_dom E hR (H' ν) hx hx0`. Establish `hsub : weightsBelow ν ⊆ {τ | τ ≠ lam}`. Introduce `τ hτ h`. Establish `hτ' : ν - τ ∈ cr_Pos n` using `hτ`. Rewrite `hτ'` using `[h]`.

Break down `cr_Pos_zero_or hτ' with h0 | h0` into its components or cases. Conclude with `hνl (sub_eq_zero.1 h0)`. Use `cr_c_lt hd hdl hτ' h0` as an intermediate fact. Establish `hν' : cr_c ν = cr_c lam` using `hν`. Use linear arithmetic over natural numbers and integers.

Conclude with `Submodule.mem_sup_right (cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (H' ν) ν hx))`. Take `⟨h, hh, l, hl, hsum⟩` from `Submodule.mem_sup.1 (hle hr2)`. Establish `hhw : h ∈ weightSp E lam` using `((cr_mem_Hs E lam h).1 hh.1).1`. Establish `hl0 : l = 0`. Assume the negation of the conclusion as `hl0`.

Establish `hlw : l ∈ weightSp E lam`. Establish `: l = w - h` using `by rw [← hsum]; abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hw.2.1 hhw`. Conclude with `(cr_WS_mem E hl hlw hl0) rfl`.

Rewrite `hsum` using `[hl0, add_zero]`. Rewrite `hh` using `[hsum]`. Establish `hwHs : w ∈ cr_Hs E lam ⊓ W` using `⟨hh.1, hwm.1⟩`. Use `(hQ lam).disjoint.le_bot ⟨hwHs, hh.2⟩` as an intermediate fact. Conclude with `hw.1 ((Submodule.mem_bot K).1 this)`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Use `(cr_CR E hR hT ⊤ (fun _ _ _ _ => trivial)).trans (iSup_le fun mu => ?_)` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, v, _, hv, rfl⟩`. Establish `hvHs : v ∈ cr_Hs E mu` using `(cr_mem_Hs E mu v).2 ⟨hv.2.1, hv.2.2⟩`.

Establish `hvt : v ∈ (cr_Hs E mu ⊓ W) ⊔ Q mu` using `by rw [(hQ mu).sup_eq_top]; trivial`. Take `⟨v1, hv1, v2, hv2, rfl⟩` from `Submodule.mem_sup.1 hvt`. Establish `hv2Hs : v2 ∈ cr_Hs E mu`. Establish `: v2 = (v1 + v2) - v1` using `by abel`. Rewrite using `[this]`.

Conclude with `Submodule.sub_mem _ hvHs hv1.1`. Use `show u (v1 + v2) ∈ W ⊔ W'`. Rewrite using `[map_add]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left (v2rep_Umon_stable E W hW u hu v1 hv1.2)) (Submodule.mem_sup_right ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : v2 = 0`.

Rewrite using `[h0, map_zero]`. Conclude with `zero_mem _`. Establish `h2` using `(cr_mem_Hs E mu v2).1 hv2Hs`. Conclude with `Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨u, hu, v2, ⟨hv2Hs, hv2⟩, ⟨h0, h2.1, h2.2⟩, rfl⟩)`.
-/
theorem cr_compl [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    ∃ W' : Submodule K V, IsCompl W W' ∧ IsStableUnderOperators E W' := by
  classical
  choose Q hQ using fun lam : Fin n → ℤ => Submodule.exists_isCompl (cr_Hs E lam ⊓ W)
  set H' : (Fin n → ℤ) → Submodule K V := fun lam => cr_Hs E lam ⊓ Q lam with hH'
  set W' : Submodule K V := ⨆ lam, isotypicPartIn E (H' lam) lam with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E (H' mu) mu
  refine ⟨W', ⟨?_, ?_⟩, hW'st⟩
  ·
    rw [disjoint_iff]
    by_contra hne
    have hst : IsStableUnderOperators E (W ⊓ W') := fun a b x hx => ⟨hW a b x hx.1, hW'st a b x hx.2⟩
    obtain ⟨lam, w, hwm, hw⟩ := v2rep_exists_hwv E hR (W ⊓ W') hst (le_top.trans hT.ge) hne
    have hdl : Dominant lam := cr_hwv_dom E hR hw
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR H' w hwm.2 (cr_c lam)
    rw [cr_aeval_eig (cr_C E) _ w (cr_C_hwv E hR lam w hw) r, hr1, one_smul] at hr2
    have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c lam}, isotypicPartIn E (H' ν) ν) ≤
        H' lam ⊔ cr_WS E {τ | τ ≠ lam} := by
      refine iSup₂_le fun ν hν x hx => ?_
      by_cases hνl : ν = lam
      · subst hνl
        have hsub : cr_Low ν ⊆ {τ | τ ≠ ν} := by
          intro τ hτ h
          have h2 := hτ.2
          rw [h, sub_self, cr_ht_zero] at h2
          exact lt_irrefl _ h2
        exact (sup_le_sup inf_le_left (cr_WS_mono E hsub)) (cr_isoIn_le E hR (H' ν) ν hx)
      · by_cases hx0 : x = 0
        · rw [hx0]; exact zero_mem _
        · have hd := cr_isoIn_dom E hR (H' ν) hx hx0
          have hsub : weightsBelow ν ⊆ {τ | τ ≠ lam} := by
            intro τ hτ h
            have hτ' : ν - τ ∈ cr_Pos n := hτ
            rw [h] at hτ'
            rcases cr_Pos_zero_or hτ' with h0 | h0
            · exact hνl (sub_eq_zero.1 h0)
            · have := cr_c_lt hd hdl hτ' h0
              have hν' : cr_c ν = cr_c lam := hν
              omega
          exact Submodule.mem_sup_right (cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (H' ν) ν hx))
    obtain ⟨h, hh, l, hl, hsum⟩ := Submodule.mem_sup.1 (hle hr2)
    have hhw : h ∈ weightSp E lam := ((cr_mem_Hs E lam h).1 hh.1).1
    have hl0 : l = 0 := by
      by_contra hl0
      have hlw : l ∈ weightSp E lam := by
        have : l = w - h := by rw [← hsum]; abel
        rw [this]; exact Submodule.sub_mem _ hw.2.1 hhw
      exact (cr_WS_mem E hl hlw hl0) rfl
    rw [hl0, add_zero] at hsum
    rw [hsum] at hh
    have hwHs : w ∈ cr_Hs E lam ⊓ W := ⟨hh.1, hwm.1⟩
    have := (hQ lam).disjoint.le_bot ⟨hwHs, hh.2⟩
    exact hw.1 ((Submodule.mem_bot K).1 this)
  ·
    rw [codisjoint_iff, eq_top_iff]
    refine (cr_CR E hR hT ⊤ (fun _ _ _ _ => trivial)).trans (iSup_le fun mu => ?_)
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, v, _, hv, rfl⟩
    have hvHs : v ∈ cr_Hs E mu := (cr_mem_Hs E mu v).2 ⟨hv.2.1, hv.2.2⟩
    have hvt : v ∈ (cr_Hs E mu ⊓ W) ⊔ Q mu := by rw [(hQ mu).sup_eq_top]; trivial
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hvt
    have hv2Hs : v2 ∈ cr_Hs E mu := by
      have : v2 = (v1 + v2) - v1 := by abel
      rw [this]; exact Submodule.sub_mem _ hvHs hv1.1
    show u (v1 + v2) ∈ W ⊔ W'
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (v2rep_Umon_stable E W hW u hu v1 hv1.2))
      (Submodule.mem_sup_right ?_)
    by_cases h0 : v2 = 0
    · rw [h0, map_zero]; exact zero_mem _
    · have h2 := (cr_mem_Hs E mu v2).1 hv2Hs
      exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨u, hu, v2, ⟨hv2Hs, hv2⟩, ⟨h0, h2.1, h2.2⟩, rfl⟩)

/- English proof (translation)
Introduce `K V _ _ _ _ _ n E hE W hW`. Conclude with `cr_compl E hE.1 hE.2.2 W hW`.
-/
theorem weight_condition_from_integral_form (D : Formalism.BasicNotions.D7) : adm2 D := by
  intro K V _ _ _ _ _ n E hE W hW
  exact cr_compl E hE.1 hE.2.2 W hW

end Formalism.MainNotions.G.GLWeightTheory
