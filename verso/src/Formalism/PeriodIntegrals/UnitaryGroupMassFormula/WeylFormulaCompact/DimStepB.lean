import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStepA

noncomputable section

namespace PI.WeylForKWork.DimensionInduction

open scoped InnerProductSpace
open Module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*} {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS`. Introduce `n`. Use `Nat.strong_induction_on n fun n ih => ?_` and prove the remaining obligations. Introduce `W hWS hWs hWn`. Use `haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS`.

Distinguish the cases in `hW0 : W = ⊥`. Substitute `hW0` using the available equality. Simplify using the standard rewrite rules. Take `⟨c, hc, hcW, hc0⟩` from `exists_hit hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 hWS hW0 hWs`. Establish `hcX : ∀ x ∈ X, c x ∈ W` using `into hρ hc hWs hXs hXi hx₀ h0 hcW`.

Establish `hYW : X.map c ≤ W`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hcX x hx`. Establish `hYs : Stab ρ (X.map c)` using `stab_map hc hXs`. Use `haveI : FiniteDimensional ℂ (X.map c) := Submodule.finiteDimensional_of_le hYW`.

Establish `hinj : Function.Injective (c.domRestrict X)`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Rewrite `hab` using `[LinearMap.domRestrict_apply, LinearMap.domRestrict_apply]`. Establish `hab' : c ((a : H) - b) = 0` using `by rw [map_sub, hab, sub_self]`.

Establish `hne' : (a : H) - b ≠ 0` using `fun h => hne (Subtype.ext (sub_eq_zero.1 h))`. Conclude with `hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)`. Establish `hYrank : finrank ℂ (X.map c) = finrank ℂ X`. Rewrite using `[← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]`. Establish `hYi : Irr ρ (X.map c)`.

Introduce `Y' hY'Y hY's`. Establish `hst : Stab ρ (X ⊓ Y'.comap c)` using `stab_inf hXs (fun i v hv => by show c (ρ i v) ∈ Y'`. Rewrite using `[hc i v]`. Conclude with `hY's i _ hv)`. Break down `hXi _ inf_le_left hst with h | h` into its components or cases.

Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `hY'Y hy`. Establish `hm : x ∈ X ⊓ Y'.comap c` using `⟨hx, hy⟩`.

Rewrite `hm` using `[h]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hm, map_zero]`. Conclude with `Submodule.zero_mem _`. Use `right`. Apply `le_antisymm hY'Y` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hm : x ∈ X ⊓ Y'.comap c`. Rewrite using `[h]`. Conclude with `hx`. Conclude with `hm.2`.

Establish `hYpos : 0 < finrank ℂ (X.map c)` using `finrank_pos_iff_exists_ne_zero.2 ⟨⟨c x₀, x₀, hx₀, rfl⟩, fun h => hc0 (congrArg Subtype.val h)⟩`. Establish `hW's : Stab ρ ((X.map c)ᗮ ⊓ W)` using `stab_inf (stab_orth hρ hYs) hWs`. Establish `hW'S : (X.map c)ᗮ ⊓ W ≤ S` using `inf_le_right.trans hWS`. Establish `hsum` using `Submodule.finrank_add_inf_finrank_orthogonal hYW`. Establish `hsl : slice ρ x₀ ⊓ W = (ℂ ∙ c x₀) ⊔ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W))`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `z ⟨⟨d, hd, rfl⟩, hzW⟩ set P : H →ₗ[ℂ] H := ((X.map c).starProjection : H →ₗ[ℂ] H) with hP`. Establish `hPd : Comm ρ (P ∘ₗ d)` using `comm_comp (proj_comm hρ hYs) hd`. Establish `hPdY : (P ∘ₗ d) x₀ ∈ X.map c`. Simplify using `only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]`.

Conclude with `((X.map c).orthogonalProjection _).2`. Take `⟨μ, hμ⟩` from `(schur2 hρ hXs hXi hYs hYi hx₀ h0 hc hPd ⟨x₀, hx₀, rfl⟩ hc0 hPdY).2`. Use `Submodule.mem_sup.2 ⟨μ • c x₀, Submodule.smul_mem _ μ (Submodule.mem_span_singleton_self _), d x₀ - μ • c x₀, ⟨?_, ?_, ?_⟩, by abel⟩` and prove the remaining obligations. Conclude with `⟨d - μ • c, (commSub ρ).sub_mem hd ((commSub ρ).smul_mem μ hc), rfl⟩`. Rewrite using `[← hμ]`.

Simplify using `only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]`. Conclude with `(X.map c).sub_starProjection_mem_orthogonal _`. Conclude with `W.sub_mem hzW (W.smul_mem μ hcW)`. Use `sup_le ?_ (inf_le_inf_left _ inf_le_right)` and prove the remaining obligations. Conclude with `(Submodule.span_singleton_le_iff_mem _ _).2 ⟨⟨c, hc, rfl⟩, hcW⟩`.

Establish `hdisj : (ℂ ∙ c x₀) ⊓ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `z ⟨hz1, -, hz2, -⟩`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hz1`. Establish `hin` using `(Submodule.mem_orthogonal _ _).1 hz2 (c x₀) ⟨x₀, hx₀, rfl⟩`.

Rewrite `hin` using `[inner_smul_right]`. Break down `mul_eq_zero.1 hin with ha | ha` into its components or cases. Rewrite using `[ha, zero_smul]`. Conclude with `Submodule.zero_mem _`. Conclude with `absurd (inner_self_eq_zero.1 ha) hc0`.

Establish `hrk1 : finrank ℂ (ℂ ∙ c x₀) = 1` using `finrank_span_singleton hc0`. Use `haveI : FiniteDimensional ℂ ↥(slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) := Submodule.finiteDimensional_of_le (inf_le_right.trans inf_le_right)`. Establish `hsup` using `Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ c x₀) (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W))`. Rewrite `hsup` using `[hdisj, finrank_bot, add_zero, ← hsl, hrk1]`. Establish `hih` using `ih (finrank ℂ ↥((X.map c)ᗮ ⊓ W)) (by omega) _ hW'S hW's rfl`.

Rewrite using `[hsup, ← hsum, hYrank, hih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem count (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X : Submodule ℂ H} [FiniteDimensional ℂ S] (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0) :
    ∀ n, ∀ W : Submodule ℂ H, W ≤ S → Stab ρ W → finrank ℂ W = n →
      finrank ℂ W = finrank ℂ X * finrank ℂ ↥(slice ρ x₀ ⊓ W) := by
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro W hWS hWs hWn
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  by_cases hW0 : W = ⊥
  · subst hW0
    simp
  obtain ⟨c, hc, hcW, hc0⟩ := exists_hit hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 hWS hW0 hWs
  have hcX : ∀ x ∈ X, c x ∈ W := into hρ hc hWs hXs hXi hx₀ h0 hcW
  have hYW : X.map c ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcX x hx
  have hYs : Stab ρ (X.map c) := stab_map hc hXs
  haveI : FiniteDimensional ℂ (X.map c) := Submodule.finiteDimensional_of_le hYW
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hYrank : finrank ℂ (X.map c) = finrank ℂ X := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  have hYi : Irr ρ (X.map c) := by
    intro Y' hY'Y hY's
    have hst : Stab ρ (X ⊓ Y'.comap c) := stab_inf hXs (fun i v hv => by
      show c (ρ i v) ∈ Y'
      rw [hc i v]
      exact hY's i _ hv)
    rcases hXi _ inf_le_left hst with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hY'Y hy
      have hm : x ∈ X ⊓ Y'.comap c := ⟨hx, hy⟩
      rw [h] at hm
      rw [(Submodule.mem_bot ℂ).1 hm, map_zero]
      exact Submodule.zero_mem _
    · right
      apply le_antisymm hY'Y
      rintro _ ⟨x, hx, rfl⟩
      have hm : x ∈ X ⊓ Y'.comap c := by
        rw [h]
        exact hx
      exact hm.2
  have hYpos : 0 < finrank ℂ (X.map c) :=
    finrank_pos_iff_exists_ne_zero.2 ⟨⟨c x₀, x₀, hx₀, rfl⟩, fun h => hc0 (congrArg Subtype.val h)⟩
  have hW's : Stab ρ ((X.map c)ᗮ ⊓ W) := stab_inf (stab_orth hρ hYs) hWs
  have hW'S : (X.map c)ᗮ ⊓ W ≤ S := inf_le_right.trans hWS
  have hsum := Submodule.finrank_add_inf_finrank_orthogonal hYW
  have hsl : slice ρ x₀ ⊓ W = (ℂ ∙ c x₀) ⊔ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) := by
    apply le_antisymm
    · rintro z ⟨⟨d, hd, rfl⟩, hzW⟩
      set P : H →ₗ[ℂ] H := ((X.map c).starProjection : H →ₗ[ℂ] H) with hP
      have hPd : Comm ρ (P ∘ₗ d) := comm_comp (proj_comm hρ hYs) hd
      have hPdY : (P ∘ₗ d) x₀ ∈ X.map c := by
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact ((X.map c).orthogonalProjection _).2
      obtain ⟨μ, hμ⟩ := (schur2 hρ hXs hXi hYs hYi hx₀ h0 hc hPd ⟨x₀, hx₀, rfl⟩ hc0 hPdY).2
      refine Submodule.mem_sup.2 ⟨μ • c x₀, Submodule.smul_mem _ μ (Submodule.mem_span_singleton_self _),
        d x₀ - μ • c x₀, ⟨?_, ?_, ?_⟩, by abel⟩
      · exact ⟨d - μ • c, (commSub ρ).sub_mem hd ((commSub ρ).smul_mem μ hc), rfl⟩
      · rw [← hμ]
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact (X.map c).sub_starProjection_mem_orthogonal _
      · exact W.sub_mem hzW (W.smul_mem μ hcW)
    · refine sup_le ?_ (inf_le_inf_left _ inf_le_right)
      exact (Submodule.span_singleton_le_iff_mem _ _).2 ⟨⟨c, hc, rfl⟩, hcW⟩
  have hdisj : (ℂ ∙ c x₀) ⊓ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, -, hz2, -⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz1
    have hin := (Submodule.mem_orthogonal _ _).1 hz2 (c x₀) ⟨x₀, hx₀, rfl⟩
    rw [inner_smul_right] at hin
    rcases mul_eq_zero.1 hin with ha | ha
    · rw [ha, zero_smul]
      exact Submodule.zero_mem _
    · exact absurd (inner_self_eq_zero.1 ha) hc0
  have hrk1 : finrank ℂ (ℂ ∙ c x₀) = 1 := finrank_span_singleton hc0
  haveI : FiniteDimensional ℂ ↥(slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) :=
    Submodule.finiteDimensional_of_le (inf_le_right.trans inf_le_right)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ c x₀) (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W))
  rw [hdisj, finrank_bot, add_zero, ← hsl, hrk1] at hsup
  have hih := ih (finrank ℂ ↥((X.map c)ᗮ ⊓ W)) (by omega) _ hW'S hW's rfl
  rw [hsup, ← hsum, hYrank, hih]
  ring

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS`. Use `haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYS`. Take `⟨x₀, hx₀, h0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hX0`. Take `⟨y₀, hy₀, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hY0`. Establish `hc1` using `count hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 (finrank ℂ S) S le_rfl hSρ rfl`.

Rewrite using `[hc1]`. Use `congr 1`. Use `set U := slice ρ x₀ ⊓ S with hUdef`. Establish `hUS : U ≤ S` using `inf_le_right`. Use `haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUS`.

Establish `hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H)` using `fun j i v => (hcomm i j v).symm`. Establish `hUs : Stab ρ' U`. Introduce and unpack `j _ ⟨⟨d, hd, rfl⟩, hS'⟩`. Conclude with `⟨⟨(ρ' j : H →ₗ[ℂ] H) ∘ₗ d, comm_comp (hρ'c j) hd, rfl⟩, hSρ' j _ hS'⟩`. Establish `hx₀U : x₀ ∈ U` using `⟨⟨LinearMap.id, fun i v => rfl, rfl⟩, hXS hx₀⟩`.

Establish `hU0 : U ≠ ⊥`. Introduce `h`. Rewrite `hx₀U` using `[h]`. Conclude with `h0 ((Submodule.mem_bot ℂ).1 hx₀U)`. Establish `hUi : Irr ρ' U`.

Introduce `U' hU'U hU's`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨hU'0, hU'ne⟩` from `hne`. Establish `hU''le : U'ᗮ ⊓ U ≤ U` using `inf_le_right`.

Establish `hU''0 : U'ᗮ ⊓ U ≠ ⊥`. Introduce `h`. Establish `hfr` using `Submodule.finrank_add_inf_finrank_orthogonal hU'U`. Rewrite `hfr` using `[h, finrank_bot, add_zero]`. Conclude with `hU'ne (Submodule.eq_of_le_of_finrank_eq hU'U hfr)`.

Take `⟨w, hwU'', hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU''0`. Establish `hwS : w ∈ S` using `hUS (hU''le hwU'')`. Establish `hTρ : Stab ρ (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H))`. Introduce `i v hv`. Establish `hle : (⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)) ≤ (⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)).comap (ρ i : H →ₗ[ℂ] H)`.

Use `iSup_le fun k => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨m, hm⟩` from `hρ.mul i k`. Use `show ρ i (ρ k z) ∈ ⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)`. Rewrite using `[hm z]`.

Conclude with `Submodule.mem_iSup_of_mem m ⟨z, hz, rfl⟩`. Conclude with `hle hv`. Establish `hTρ' : Stab ρ' (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H))` using `stab_iSup fun k => stab_map (fun j v => hcomm k j v) hU's`. Establish `hTS : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≤ S`. Use `iSup_le fun k => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `hSρ k z (hUS (hU'U hz))`. Establish `hT0 : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≠ ⊥`. Take `⟨u, huU', hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU'0`. Take `⟨o, ho⟩` from `hρ.one`.

Introduce `h`. Establish `hm : ρ o u ∈ ⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)` using `Submodule.mem_iSup_of_mem o ⟨u, huU', rfl⟩`. Rewrite `hm` using `[h, ho]`. Conclude with `hu0 ((Submodule.mem_bot ℂ).1 hm)`. Establish `hTeq` using `(hSirr _ hTS hTρ hTρ').resolve_left hT0`.

Establish `key : ∀ k, ∀ z ∈ U', ⟪w, ρ k z⟫_ℂ = 0`. Introduce `k z hz`. Take `⟨⟨d', hd', rfl⟩, -⟩` from `hU'U hz`. Distinguish the cases in `hd0 : d' x₀ = 0`. Rewrite using `[hd0, map_zero, inner_zero_right]`.

Take `⟨⟨d'', hd'', hw_eq⟩, -⟩` from `hU''le hwU''`. Establish `hKs : Stab ρ (X.map d')` using `stab_map hd' hXs`. Establish `hKi : Irr ρ (X.map d')`. Introduce `Y' hY'Y hY's`. Establish `hst : Stab ρ (X ⊓ Y'.comap d')` using `stab_inf hXs (fun i v hv => by show d' (ρ i v) ∈ Y'`.

Rewrite using `[hd' i v]`. Conclude with `hY's i _ hv)`. Break down `hXi _ inf_le_left hst with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `hY'Y hy`. Establish `hm : x ∈ X ⊓ Y'.comap d'` using `⟨hx, hy⟩`. Rewrite `hm` using `[h]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hm, map_zero]`.

Conclude with `Submodule.zero_mem _`. Use `right`. Apply `le_antisymm hY'Y` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hm : x ∈ X ⊓ Y'.comap d'`.

Rewrite using `[h]`. Conclude with `hx`. Conclude with `hm.2`. Use `set P : H →ₗ[ℂ] H := ((X.map d').starProjection : H →ₗ[ℂ] H) with hP`. Establish `hPd : Comm ρ (P ∘ₗ d'')` using `comm_comp (proj_comm hρ hKs) hd''`.

Establish `hPdK : (P ∘ₗ d'') x₀ ∈ X.map d'`. Simplify using `only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]`. Conclude with `((X.map d').orthogonalProjection _).2`. Take `⟨μ, hμ⟩` from `(schur2 hρ hXs hXi hKs hKi hx₀ h0 hd' hPd ⟨x₀, hx₀, rfl⟩ hd0 hPdK).2`. Establish `hPw : (X.map d').starProjection w = μ • d' x₀`.

Rewrite using `[← hw_eq]`. Simplify `hμ` using `only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]`. Establish `horth : ⟪d' x₀, w⟫_ℂ = 0` using `(Submodule.mem_orthogonal _ _).1 hwU''.1 _ hz`. Establish `h1 : ⟪d' x₀, w - (X.map d').starProjection w⟫_ℂ = 0` using `(Submodule.mem_orthogonal _ _).1 ((X.map d').sub_starProjection_mem_orthogonal w) _ ⟨x₀, hx₀, rfl⟩`. Rewrite `h1` using `[inner_sub_right, horth, hPw, inner_smul_right, zero_sub, neg_eq_zero]`.

Establish `hμ0 : μ = 0`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (inner_self_eq_zero.1 h) hd0`. Rewrite `hPw` using `[hμ0, zero_smul]`.

Rewrite using `[← hd' k x₀]`. Establish `hmemK : d' (ρ k x₀) ∈ X.map d'` using `⟨ρ k x₀, hXs k x₀ hx₀, rfl⟩`. Establish `h2 : ⟪d' (ρ k x₀), w - (X.map d').starProjection w⟫_ℂ = 0` using `(Submodule.mem_orthogonal _ _).1 ((X.map d').sub_starProjection_mem_orthogonal w) _ hmemK`. Rewrite `h2` using `[hPw, sub_zero]`. Conclude with `inner_eq_zero_symm.1 h2`.

Establish `hle : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≤ (ℂ ∙ w)ᗮ`. Use `iSup_le fun k => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_right]`. Conclude with `key k z hz`.

Rewrite `hle` using `[hTeq]`. Establish `hww` using `Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hwS)`. Conclude with `hw0 (inner_self_eq_zero.1 hww)`. Establish `hcomm' : ∀ j i v, ρ' j (ρ i v) = ρ i (ρ' j v)` using `fun j i v => (hcomm i j v).symm`. Establish `hSirr' : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ' S' → Stab ρ S' → S' = ⊥ ∨ S' = S` using `fun S' h1 h2 h3 => hSirr S' h1 h3 h2`.

Take `⟨e, he, heU, he0⟩` from `exists_hit hρ' hρ hcomm' hSρ hSirr' hYS hYs hYi hy₀ hy0 hUS hU0 hUs`. Conclude with `(schur2 hρ' hYs hYi hUs hUi hy₀ hy0 he he heU he0 heU).1.symm`.
-/
theorem main (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X Y : Submodule ℂ H} [FiniteDimensional ℂ S] (hSρ : Stab ρ S) (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hX0 : X ≠ ⊥) (hXs : Stab ρ X) (hXi : Irr ρ X)
    (hYS : Y ≤ S) (hY0 : Y ≠ ⊥) (hYs : Stab ρ' Y) (hYi : Irr ρ' Y) :
    finrank ℂ S = finrank ℂ X * finrank ℂ Y := by
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYS
  obtain ⟨x₀, hx₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  obtain ⟨y₀, hy₀, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hc1 := count hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 (finrank ℂ S) S le_rfl hSρ rfl
  rw [hc1]
  congr 1
  set U := slice ρ x₀ ⊓ S with hUdef
  have hUS : U ≤ S := inf_le_right
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUS
  have hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H) := fun j i v => (hcomm i j v).symm
  have hUs : Stab ρ' U := by
    rintro j _ ⟨⟨d, hd, rfl⟩, hS'⟩
    exact ⟨⟨(ρ' j : H →ₗ[ℂ] H) ∘ₗ d, comm_comp (hρ'c j) hd, rfl⟩, hSρ' j _ hS'⟩
  have hx₀U : x₀ ∈ U := ⟨⟨LinearMap.id, fun i v => rfl, rfl⟩, hXS hx₀⟩
  have hU0 : U ≠ ⊥ := by
    intro h
    rw [h] at hx₀U
    exact h0 ((Submodule.mem_bot ℂ).1 hx₀U)
  have hUi : Irr ρ' U := by
    intro U' hU'U hU's
    by_contra hne
    push_neg at hne
    obtain ⟨hU'0, hU'ne⟩ := hne
    have hU''le : U'ᗮ ⊓ U ≤ U := inf_le_right
    have hU''0 : U'ᗮ ⊓ U ≠ ⊥ := by
      intro h
      have hfr := Submodule.finrank_add_inf_finrank_orthogonal hU'U
      rw [h, finrank_bot, add_zero] at hfr
      exact hU'ne (Submodule.eq_of_le_of_finrank_eq hU'U hfr)
    obtain ⟨w, hwU'', hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU''0
    have hwS : w ∈ S := hUS (hU''le hwU'')
    have hTρ : Stab ρ (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) := by
      intro i v hv
      have hle : (⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)) ≤
          (⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)).comap (ρ i : H →ₗ[ℂ] H) := by
        refine iSup_le fun k => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨m, hm⟩ := hρ.mul i k
        show ρ i (ρ k z) ∈ ⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)
        rw [hm z]
        exact Submodule.mem_iSup_of_mem m ⟨z, hz, rfl⟩
      exact hle hv
    have hTρ' : Stab ρ' (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) :=
      stab_iSup fun k => stab_map (fun j v => hcomm k j v) hU's
    have hTS : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≤ S := by
      refine iSup_le fun k => ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hSρ k z (hUS (hU'U hz))
    have hT0 : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≠ ⊥ := by
      obtain ⟨u, huU', hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU'0
      obtain ⟨o, ho⟩ := hρ.one
      intro h
      have hm : ρ o u ∈ ⨆ i, U'.map (ρ i : H →ₗ[ℂ] H) := Submodule.mem_iSup_of_mem o ⟨u, huU', rfl⟩
      rw [h, ho] at hm
      exact hu0 ((Submodule.mem_bot ℂ).1 hm)
    have hTeq := (hSirr _ hTS hTρ hTρ').resolve_left hT0
    have key : ∀ k, ∀ z ∈ U', ⟪w, ρ k z⟫_ℂ = 0 := by
      intro k z hz
      obtain ⟨⟨d', hd', rfl⟩, -⟩ := hU'U hz
      by_cases hd0 : d' x₀ = 0
      · rw [hd0, map_zero, inner_zero_right]
      obtain ⟨⟨d'', hd'', hw_eq⟩, -⟩ := hU''le hwU''
      have hKs : Stab ρ (X.map d') := stab_map hd' hXs
      have hKi : Irr ρ (X.map d') := by
        intro Y' hY'Y hY's
        have hst : Stab ρ (X ⊓ Y'.comap d') := stab_inf hXs (fun i v hv => by
          show d' (ρ i v) ∈ Y'
          rw [hd' i v]
          exact hY's i _ hv)
        rcases hXi _ inf_le_left hst with h | h
        · left
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hY'Y hy
          have hm : x ∈ X ⊓ Y'.comap d' := ⟨hx, hy⟩
          rw [h] at hm
          rw [(Submodule.mem_bot ℂ).1 hm, map_zero]
          exact Submodule.zero_mem _
        · right
          apply le_antisymm hY'Y
          rintro _ ⟨x, hx, rfl⟩
          have hm : x ∈ X ⊓ Y'.comap d' := by
            rw [h]
            exact hx
          exact hm.2
      set P : H →ₗ[ℂ] H := ((X.map d').starProjection : H →ₗ[ℂ] H) with hP
      have hPd : Comm ρ (P ∘ₗ d'') := comm_comp (proj_comm hρ hKs) hd''
      have hPdK : (P ∘ₗ d'') x₀ ∈ X.map d' := by
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact ((X.map d').orthogonalProjection _).2
      obtain ⟨μ, hμ⟩ := (schur2 hρ hXs hXi hKs hKi hx₀ h0 hd' hPd ⟨x₀, hx₀, rfl⟩ hd0 hPdK).2
      have hPw : (X.map d').starProjection w = μ • d' x₀ := by
        rw [← hw_eq]
        simpa only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe] using hμ
      have horth : ⟪d' x₀, w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hwU''.1 _ hz
      have h1 : ⟪d' x₀, w - (X.map d').starProjection w⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 ((X.map d').sub_starProjection_mem_orthogonal w) _
          ⟨x₀, hx₀, rfl⟩
      rw [inner_sub_right, horth, hPw, inner_smul_right, zero_sub, neg_eq_zero] at h1
      have hμ0 : μ = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd (inner_self_eq_zero.1 h) hd0
      rw [hμ0, zero_smul] at hPw
      rw [← hd' k x₀]
      have hmemK : d' (ρ k x₀) ∈ X.map d' := ⟨ρ k x₀, hXs k x₀ hx₀, rfl⟩
      have h2 : ⟪d' (ρ k x₀), w - (X.map d').starProjection w⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 ((X.map d').sub_starProjection_mem_orthogonal w) _ hmemK
      rw [hPw, sub_zero] at h2
      exact inner_eq_zero_symm.1 h2
    have hle : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≤ (ℂ ∙ w)ᗮ := by
      refine iSup_le fun k => ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact key k z hz
    rw [hTeq] at hle
    have hww := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hwS)
    exact hw0 (inner_self_eq_zero.1 hww)
  have hcomm' : ∀ j i v, ρ' j (ρ i v) = ρ i (ρ' j v) := fun j i v => (hcomm i j v).symm
  have hSirr' : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ' S' → Stab ρ S' → S' = ⊥ ∨ S' = S :=
    fun S' h1 h2 h3 => hSirr S' h1 h3 h2
  obtain ⟨e, he, heU, he0⟩ := exists_hit hρ' hρ hcomm' hSρ hSirr' hYS hYs hYi hy₀ hy0 hUS hU0 hUs
  exact (schur2 hρ' hYs hYi hUs hUi hy₀ hy0 he he heU he0 heU).1.symm

end PI.WeylForKWork.DimensionInduction
