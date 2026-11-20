import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinK
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinD
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSpan

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix PhiCMin

/- English proof (translation)
The claim follows from `|(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) = 1 := by have hd : (discr E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E have ha : (((discr E).natAbs : ℝ)) = |(discr E : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs] rw [ha] have ha0 : 0 < |(discr E : ℝ)| := abs_pos.mpr hd …`.
-/
theorem const_eq (E : Type) [Field E] [NumberField E] :
    ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) *
      |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) = 1 := by
  have hd : (discr E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have ha : (((discr E).natAbs : ℝ)) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [ha]
  have ha0 : 0 < |(discr E : ℝ)| := abs_pos.mpr hd
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
  have h2 : ((2 : ℕ) : ℝ) * (1 / (finrank ℚ E : ℝ)) = 2 / (finrank ℚ E : ℝ) := by
    push_cast; ring
  rw [h2]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos ha0 _).ne'

/- English proof (translation)
Introduce `E _ _ cj hcj hne w₀ hw Y _ _ _ _ β hβ`. Take `⟨ι, hι, b0, hpd⟩` from `hβ`. Establish `hcard : Fintype.card ι = finrank ℤ Y` using `(Module.finrank_eq_card_basis b0).symm`. Use `set d := finrank ℤ Y with hd_def`. Set `b : Basis (Fin d) ℤ Y` to `b0.reindex (Fintype.equivFinOfCardEq hcard)`.

Establish `hG : (Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)).PosDef`. Establish `h` using `hpd.submatrix (Fintype.equivFinOfCardEq hcard).symm.injective`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a c`. Simplify using `[b, Basis.reindex_apply]`.

Break down `Nat.eq_zero_or_pos d with hd0 | hdpos` into its components or cases. Establish `: IsEmpty (Fin d)` using `by rw [hd0]; infer_instance`. Conclude with `⟨fun i => isEmptyElim i, linearIndependent_empty_type, fun i => isEmptyElim i⟩`. Use `set G := Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) with hGdef`. Establish `hcjO : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c` using `cj_integral hcj`.

Set `l0 : SymB cj Y →ₗ[ℝ] ℝ` to `{ toFun := fun γ => ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) map_add' := fun γ γ' => by simp [Finset.sum_add_distrib] map_smul' := fun t γ => by simp [Finset.mul_sum] }`. Establish `hl0int : ∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l0 γ = z`. Introduce `γ hγ`. Use `choose f hf using hγ`. Use `⟨∑ a, f (w₀ • b a) (b a), ?_⟩` and prove the remaining obligations.

Use `show ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = _`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun a _ => hf _ _`. Establish `hl0pos : ∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l0 γ`. Introduce `γ hγ hne0`.

Establish `h2 : ∀ a, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b a)` using `fun a => two_mul_form_half_unit hcjO w₀ hw γ (b a)`. Establish `hnn : ∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)` using `fun a => by`. Combine the linear relations using `[h2 a, hγ (b a)]`. Use `show 0 < ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)`. Assume the negation of the conclusion as `hle`.

Use `push Not at hle`. Establish `hz : ∀ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = 0` using `fun a => (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 (le_antisymm hle (Finset.sum_nonneg fun a _ => hnn a)) a (Finset.mem_univ _)`. Establish `hrad : ∀ a z, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) z = 0` using `fun a z => bil_rad _ γ.2.1 hγ (b a) (by rw [← h2 a, hz a, mul_zero]) z`. Apply `hne0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use `LinearMap.ext₂ fun y z => ?_` and prove the remaining obligations. Rewrite using `[← repr_left b (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z]`. Simplify using `[hrad]`. Set `Q : (Fin d → ℤ) → ℝ` to `fun c => (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))`. Establish `hne_u : (Finset.univ : Finset (Fin d)).Nonempty` using `⟨⟨0, hdpos⟩, Finset.mem_univ _⟩`.

Set `F : (Fin d → Fin d → ℤ) → ℝ` to `fun c => Finset.univ.sup' hne_u fun j => Q (c j)`. Set `B0 : ℝ` to `(1 / 2) * l0 β * ((d : ℝ) / muC E + 1) ^ 2`. Set `T : Set (Fin d → Fin d → ℤ)` to `{c | LinearIndependent ℤ c ∧ ∀ j, Q (c j) ≤ B0}`. Establish `hTfin : T.Finite`. Use `(Set.Finite.pi (t := fun _ : Fin d => {c : Fin d → ℤ | Q c ≤ B0}) fun _ => finiteShort_holds d G hG B0).subset ?_` and prove the remaining obligations.

Introduce `c hc j _`. Conclude with `hc.2 j`. Take `⟨c1, hc1li, hc1⟩` from `main_ineq hcj hne hdpos b β hG l0 hl0int hl0pos 1 one_pos`. Establish `hTne : T.Nonempty` using `⟨c1, hc1li, hc1⟩`. Take `⟨cs, hcsT, hcsmin⟩` from `Set.exists_min_image T F hTfin hTne`.

Establish `hclaim : ∀ l : SymB cj Y →ₗ[ℝ] ℝ, (∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l γ = z) → (∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l γ) → F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2`. Introduce `l hlint hlpos`. Establish `hev : ∀ δ : ℝ, 0 < δ → F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2`. Introduce `δ hδ`. Take `⟨c, hcli, hcq⟩` from `main_ineq hcj hne hdpos b β hG l hlint hlpos δ hδ`.

Distinguish the cases in `hle : (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 ≤ B0`. Conclude with `(hcsmin c ⟨hcli, fun j => (hcq j).trans hle⟩).trans (Finset.sup'_le _ _ fun j _ => hcq j)`. Use `push Not at hle`. Conclude with `(Finset.sup'_le _ _ fun j _ => hcsT.2 j).trans hle.le`. Establish `hcont : Continuous fun δ : ℝ => (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2` using `by fun_prop`.

Establish `ht` using `(hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))`. Simplify using `only [add_zero] at ht`. Conclude with `ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => hev δ hδ)`. Establish `hn : (0 : ℝ) < finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`. Establish `hD : (0 : ℝ) < ((discr E).natAbs : ℝ)`.

Conclude with `Int.natAbs_pos.mpr (discr_ne_zero E)` after adjusting the coercions. Establish `hXpos : (0 : ℝ) < ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E)`. Check the signs of the components of the expression. Establish `hP : |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) = (((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E))⁻¹` using `eq_inv_of_mul_eq_one_right (const_eq E)`. Establish `hdpos' : (0 : ℝ) < d` using `by exact_mod_cast hdpos`.

Use `set κ : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) / (finrank ℚ E) * (d : ℝ) ^ 2 with hκdef`. Establish `hκpos : 0 < κ` using `by rw [hκdef, hP]; positivity`. Establish `hκ : ∀ l : SymB cj Y →ₗ[ℝ] ℝ, (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 = κ * l β`. Introduce `l`. Rewrite using `[div_pow, muC_sq, hκdef, hP]`.

Clear the denominators using the available nonvanishing facts. Establish `hphi : F cs ≤ κ * phiC cj β`. Establish `h1 : F cs / κ ≤ phiC cj β`. Unfold `phiC`. Use `le_csInf ⟨l0 β, l0, hl0int, hl0pos, rfl⟩ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨l, hl1, hl2, rfl⟩`. Rewrite using `[div_le_iff₀ hκpos, mul_comm, ← hκ l]`. Conclude with `hclaim l hl1 hl2`. Rewrite `h1` using `[div_le_iff₀ hκpos, mul_comm]`. Then use the resulting hypothesis. Use `⟨fun j => b.equivFun.symm (cs j), ?_, fun j => ?_⟩` and prove the remaining obligations.

Conclude with `hcsT.1.map' b.equivFun.symm.toLinearMap (LinearEquiv.ker _)`. Establish `hr : ∀ a : Fin d, PhiCMin.bs b a (b.equivFun.symm (cs j)) = (cs j a : ℝ)` using `fun a => by`. Rewrite using `[PhiCMin.bs_apply]`. Use `congr 1`. Rewrite using `[← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.

Establish `hq : (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j)) = Q (cs j)`. Rewrite using `[← gram_expand b _ (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j))]`. Simplify using `only [hr, Q, dotProduct, Matrix.mulVec, hGdef, Matrix.of_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring`. Establish `hle : Q (cs j) ≤ F cs` using `Finset.le_sup' (fun j => Q (cs j)) (Finset.mem_univ j)`.

Rewrite using `[hq]`. Establish `hk : κ * phiC cj β = 2 * (|(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) / (2 * finrank ℚ E) * (d : ℝ) ^ 2 * phiC cj β)`. Rewrite using `[hκdef]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phiCMinima_holds : PhiCMinimaStatement := by
  intro E _ _ cj hcj hne w₀ hw Y _ _ _ _ β hβ
  classical
  obtain ⟨ι, hι, b0, hpd⟩ := hβ
  have hcard : Fintype.card ι = finrank ℤ Y := (Module.finrank_eq_card_basis b0).symm
  set d := finrank ℤ Y with hd_def
  let b : Basis (Fin d) ℤ Y := b0.reindex (Fintype.equivFinOfCardEq hcard)
  have hG : (Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)).PosDef := by
    have h := hpd.submatrix (Fintype.equivFinOfCardEq hcard).symm.injective
    convert h using 1
    ext a c
    simp [b, Basis.reindex_apply]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have : IsEmpty (Fin d) := by rw [hd0]; infer_instance
    exact ⟨fun i => isEmptyElim i, linearIndependent_empty_type, fun i => isEmptyElim i⟩
  set G := Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) with hGdef

  have hcjO : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c := cj_integral hcj
  let l0 : SymB cj Y →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)
      map_add' := fun γ γ' => by simp [Finset.sum_add_distrib]
      map_smul' := fun t γ => by simp [Finset.mul_sum] }
  have hl0int : ∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) →
      ∃ z : ℤ, l0 γ = z := by
    intro γ hγ
    choose f hf using hγ
    refine ⟨∑ a, f (w₀ • b a) (b a), ?_⟩
    show ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = _
    push_cast
    exact Finset.sum_congr rfl fun a _ => hf _ _
  have hl0pos : ∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l0 γ := by
    intro γ hγ hne0
    have h2 : ∀ a, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) =
        (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b a) := fun a => two_mul_form_half_unit hcjO w₀ hw γ (b a)
    have hnn : ∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) := fun a => by
      linarith [h2 a, hγ (b a)]
    show 0 < ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)
    by_contra hle
    push Not at hle
    have hz : ∀ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1
        (le_antisymm hle (Finset.sum_nonneg fun a _ => hnn a)) a (Finset.mem_univ _)
    have hrad : ∀ a z, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) z = 0 := fun a z =>
      bil_rad _ γ.2.1 hγ (b a) (by rw [← h2 a, hz a, mul_zero]) z
    apply hne0
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    rw [← repr_left b (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z]
    simp [hrad]

  let Q : (Fin d → ℤ) → ℝ := fun c => (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))
  have hne_u : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
  let F : (Fin d → Fin d → ℤ) → ℝ := fun c => Finset.univ.sup' hne_u fun j => Q (c j)
  let B0 : ℝ := (1 / 2) * l0 β * ((d : ℝ) / muC E + 1) ^ 2
  let T : Set (Fin d → Fin d → ℤ) := {c | LinearIndependent ℤ c ∧ ∀ j, Q (c j) ≤ B0}
  have hTfin : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin d => {c : Fin d → ℤ | Q c ≤ B0})
      fun _ => finiteShort_holds d G hG B0).subset ?_
    intro c hc j _
    exact hc.2 j
  obtain ⟨c1, hc1li, hc1⟩ := main_ineq hcj hne hdpos b β hG l0 hl0int hl0pos 1 one_pos
  have hTne : T.Nonempty := ⟨c1, hc1li, hc1⟩
  obtain ⟨cs, hcsT, hcsmin⟩ := Set.exists_min_image T F hTfin hTne
  have hclaim : ∀ l : SymB cj Y →ₗ[ℝ] ℝ,
      (∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l γ = z) →
      (∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l γ) →
      F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 := by
    intro l hlint hlpos
    have hev : ∀ δ : ℝ, 0 < δ → F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by
      intro δ hδ
      obtain ⟨c, hcli, hcq⟩ := main_ineq hcj hne hdpos b β hG l hlint hlpos δ hδ
      by_cases hle : (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 ≤ B0
      · exact (hcsmin c ⟨hcli, fun j => (hcq j).trans hle⟩).trans
          (Finset.sup'_le _ _ fun j _ => hcq j)
      · push Not at hle
        exact (Finset.sup'_le _ _ fun j _ => hcsT.2 j).trans hle.le
    have hcont : Continuous fun δ : ℝ => (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by fun_prop
    have ht := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [add_zero] at ht
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => hev δ hδ)

  have hn : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hD : (0 : ℝ) < ((discr E).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero E)
  have hXpos : (0 : ℝ) < ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) := by
    positivity
  have hP : |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) =
      (((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E))⁻¹ :=
    eq_inv_of_mul_eq_one_right (const_eq E)
  have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
  set κ : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) / (finrank ℚ E) * (d : ℝ) ^ 2 with hκdef
  have hκpos : 0 < κ := by rw [hκdef, hP]; positivity
  have hκ : ∀ l : SymB cj Y →ₗ[ℝ] ℝ, (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 = κ * l β := by
    intro l
    rw [div_pow, muC_sq, hκdef, hP]
    field_simp
  have hphi : F cs ≤ κ * phiC cj β := by
    have h1 : F cs / κ ≤ phiC cj β := by
      unfold phiC
      refine le_csInf ⟨l0 β, l0, hl0int, hl0pos, rfl⟩ ?_
      rintro _ ⟨l, hl1, hl2, rfl⟩
      rw [div_le_iff₀ hκpos, mul_comm, ← hκ l]
      exact hclaim l hl1 hl2
    rwa [div_le_iff₀ hκpos, mul_comm] at h1

  refine ⟨fun j => b.equivFun.symm (cs j), ?_, fun j => ?_⟩
  · exact hcsT.1.map' b.equivFun.symm.toLinearMap (LinearEquiv.ker _)
  · have hr : ∀ a : Fin d, PhiCMin.bs b a (b.equivFun.symm (cs j)) = (cs j a : ℝ) := fun a => by
      rw [PhiCMin.bs_apply]
      congr 1
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hq : (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j)) =
        Q (cs j) := by
      rw [← gram_expand b _ (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j))]
      simp only [hr, Q, dotProduct, Matrix.mulVec, hGdef, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    have hle : Q (cs j) ≤ F cs := Finset.le_sup' (fun j => Q (cs j)) (Finset.mem_univ j)
    rw [hq]
    have hk : κ * phiC cj β = 2 * (|(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) /
        (2 * finrank ℚ E) * (d : ℝ) ^ 2 * phiC cj β) := by
      rw [hκdef]; field_simp
    linarith

end Formalism.MainNotions.ModuliIntegralCharts.H1
