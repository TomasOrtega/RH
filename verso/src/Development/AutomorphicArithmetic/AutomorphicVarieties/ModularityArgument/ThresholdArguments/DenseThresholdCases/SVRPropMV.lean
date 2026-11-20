import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
namespace UpperTheory.Esk.PropMVAux
variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end UpperTheory.Esk.PropMVAux
open UpperTheory.Esk.PropMVAux in
open Classical in
/- English proof (translation)
Introduce `hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2`. Establish `: IsGalois F Ω` using `{}`. Take `⟨art, ha⟩` from `hPH.litN.aut.art F Ω`. Establish `hc` using `continuous_of_isOpen_ker' ξ ho`. Establish `: Finite (G F Ω ⧸ ξ.ker)` using `ξ.ker.quotient_finite_of_isOpen ho`.

Establish `hm : 0 < ξ.ker.index` using `Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite`. Establish `hξm : ξ ^ ξ.ker.index = 1` using `MonoidHom.ext fun g => by`. Rewrite using `[MonoidHom.pow_apply, ← map_pow]`. Conclude with `ξ.ker.pow_index_mem g`. Establish `hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1` using `fun s => by`.

Establish `h2 : ξ s ^ ξ.ker.index = 1` using `DFunLike.congr_fun hξm s`. Establish `h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1` using `by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3`. Take `⟨ω, ⟨hω, hL⟩, -⟩` from `exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm`. Establish `hfo : IsOfFinOrder ω` using `isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩`.

Take `⟨c, hcond, hc0, hfin⟩` from `cond_ex ω hm hω`. Establish `hine : ∀ (w : Pl F) (A : ValuationSubring Ω), IsPlaceOver A w → (Ine (F` using `F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA => (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm`. Establish `hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0` using `fun w hw => by`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Conclude with `(hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))`.

Establish `hfr : ∀ (w : Pl F), c w = 0 → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ → ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ)` using `fun w hw A hA σ hσ => by`. Rewrite using `[map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]`. Establish `hsg : ∀ v, ω.locInf v (-1) = -1` using `fun v => by`. Take `⟨j, σ, hσ, rfl⟩` from `GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)`. Establish `e` using `hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)`.

Rewrite `e` using `[infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩]`. Use `Units.ext (ι.symm.injective (e.symm.trans ?_))` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hex : ∃ w, c w ≠ 0`. Take `⟨u, A, -, hA, hnA⟩` from `hram`.

Conclude with `⟨u, fun h => hnA ((hine u A hA).2 h)⟩`. Establish `hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F` using `F) A, ¬ Cong (ξ σ) 1) → ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by`. Introduce and unpack `w ⟨hw, A, hA, σ, hσ, h⟩`. Conclude with `⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩`. Take `⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩` from `hMH F l hl2 ι ω c hfo hsg hcond hex hcl P (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3`.

Establish `hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w` using `fun w hw => if_neg hw`. Establish `hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1` using `fun w hw => if_pos hw`. Establish `hfinL : {w | levL l c w ≠ 0}.Finite`. Use `(hfin.union (fin_l (l := l))).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h`. Conclude with `hw ((hlev w h.2).trans h.1)`. Establish `heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1` using `fun w hw => by`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨σ, hσ⟩` from `exists_isFrob hA`.

Rewrite using `[eisT, if_pos hw]`. Use `split_ifs`. Rewrite using `[hfr w (hcl w hw) A hA σ hσ, hn]`. Simplify using the standard rewrite rules. Take `⟨D⟩` from `Wc.exL F l ι hsplit`.

Establish `hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2`. Take `⟨u, A, h2, hA, hnA⟩` from `hram`. Use `⟨u, ?_, h2⟩` and prove the remaining obligations. Distinguish the cases in `hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal`. Rewrite using `[hlev1 u hl]`.

Conclude with `one_ne_zero`. Rewrite using `[hlev u hl]`. Conclude with `fun h => hnA ((hine u A hA).2 h)`. Establish `hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1` using `fun v => by`. Rewrite using `[nu_eq]`.

Use `norm_eq_one (heu _ (D.mem v)) ?_` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `hlam _`. Take `⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩` from `hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit {v | D.pl v ∈ P} 2`. Establish `hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w - eisT l ω c P w)‖ < 1` using `fun w => by`.

Rewrite using `[← sub_add_sub_cancel _ (lam w), map_add]`. Conclude with `add_lt (nu_lt.1 (hcong w)) (hlam w)`. Establish `haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1` using `fun w hw => by`. Establish `h` using `hlam' w`. Rewrite `h` using `[prod_away D _ t w hw, one_mul]`. Then use the resulting hypothesis.

Take `⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩` from `hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0) (levL l c) ω hfo φ' lam' hV hne heig hcusp`. Take `⟨r, wt, HT, hG, hatt, -⟩` from `_root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol`. Take `⟨hdet, hres⟩` from `det_res ξ hc r hG.cont k hk hn (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by`. Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw`. Take `⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩` from `hw`.

Take `⟨B₂, hB₂, e⟩` from `hsat w ((hlev w hl).trans h0)`. Take `rfl` from `hB₁.unique hB₂`. Take `⟨h2, h3⟩` from `tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)`. Establish `h4` using `haway w hl`. Rewrite `h4` using `[eisT, if_neg hl, if_pos h0, map_sub, map_add, map_one, hfr w h0 A hA σ hσ]`.

Rewrite using `[h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]`. Conclude with `⟨h4, rfl⟩`. Use `⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r, ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩, hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hine w A hA]`. Distinguish the cases in `hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal`.

Simplify using `[hl, hcl w hl]`. Simplify using `[hl, hlev w hl]`. Take `⟨v, h1, h2, -⟩` from `hU w`. Rewrite `h2` using `[hw]`. Conclude with `⟨v, h1, h2⟩`.

Use `⟨lam' w, hU w, norm_one_of ?_⟩` and prove the remaining obligations. Establish `h4` using `haway w hl`. Rewrite `h4` using `[eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one]`. Then use the resulting hypothesis. Take `⟨v₀, hv₀⟩` from `D.surj w hw`. Establish `hnorm : normV w = l` using `hv₀ ▸ D.norm v₀`.

Establish `hc'` using `hlam' w`. Rewrite `hc'` using `[prod_at D _ t w v₀ hv₀]`. Use `⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `by_cases h : w ∈ P <;> simp [h] <;> omega`. Apply the tactic sequence `by_cases h : w ∈ P <;> simp [h] <;> ring`.

Rewrite using `[hnorm]`. Distinguish the cases in `h : w ∈ P`. Establish `hv : v₀ ∈ {v | D.pl v ∈ P}` using `by simpa [hv₀] using h`. Rewrite `hc'` using `[if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm]`. Rewrite using `[if_pos h]`.

Simplify using `using hc'`. Establish `hv : v₀ ∉ {v | D.pl v ∈ P}` using `by simpa [hv₀] using h`. Rewrite `hc'` using `[if_neg hv, one_mul, map_sub]`. Rewrite using `[if_neg h]`. Simplify using `using hc'`.

Take `⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v` from `⟨_, rfl⟩`. Establish `hv : D.pl v = w` using `hvd ▸ (D.embAt τ w).1 hτ`. Rewrite using `[hvd]`. Use `hinf v using 3` and compare the differences between its conclusion and the goal. Distinguish the cases in `h : w ∈ P`.

Establish `hS : v ∈ {v | D.pl v ∈ P}` using `by simpa [hv] using h`. Apply the tactic sequence `ext i; fin_cases i <;> simp [h, hS] <;> omega`. Establish `hS : v ∉ {v | D.pl v ∈ P}` using `by simpa [hv] using h`. Apply the tactic sequence `ext i; fin_cases i <;> simp [h, hS] <;> omega`. Simplify using `only [eisT, if_pos hw, if_pos h]`.

Conclude with `hfr w (hcl w hw) A hA σ hσ`. Simplify using `only [eisT, if_pos hw, if_neg h, map_one]`.
-/
theorem UpperTheory.Esk.pf_PropMV_sv_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropMHol → UpperTheory.Esk.HolWC → UpperTheory.Esk.HRep → UpperTheory.Esk.PropMV := by
  intro hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2
  have : IsGalois F Ω := {}
  obtain ⟨art, ha⟩ := hPH.litN.aut.art F Ω
  have hc := continuous_of_isOpen_ker' ξ ho
  have : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen ho
  have hm : 0 < ξ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hξm : ξ ^ ξ.ker.index = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.pow_apply, ← map_pow]
    exact ξ.ker.pow_index_mem g
  have hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1 := fun s => by
    have h2 : ξ s ^ ξ.ker.index = 1 := DFunLike.congr_fun hξm s
    have h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  obtain ⟨ω, ⟨hω, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm
  have hfo : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩
  obtain ⟨c, hcond, hc0, hfin⟩ := cond_ex ω hm hω
  have hine : ∀ (w : Pl F) (A : ValuationSubring Ω), IsPlaceOver A w → (Ine (F := F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA =>
    (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm
  have hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact (hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))
  have hfr : ∀ (w : Pl F), c w = 0 → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ) := fun w hw A hA σ hσ => by
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]
  have hsg : ∀ v, ω.locInf v (-1) = -1 := fun v => by
    obtain ⟨j, σ, hσ, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)
    have e := hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩] at e
    refine Units.ext (ι.symm.injective (e.symm.trans ?_))
    simp
  have hex : ∃ w, c w ≠ 0 := by
    obtain ⟨u, A, -, hA, hnA⟩ := hram
    exact ⟨u, fun h => hnA ((hine u A hA).2 h)⟩
  have hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by
    rintro w ⟨hw, A, hA, σ, hσ, h⟩
    exact ⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩
  obtain ⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩ := hMH F l hl2 ι ω c hfo hsg hcond hex hcl P
    (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3
  have hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hfinL : {w | levL l c w ≠ 0}.Finite := by
    refine (hfin.union (fin_l (l := l))).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hw ((hlev w h.2).trans h.1)
  have heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    rw [eisT, if_pos hw]
    split_ifs
    · rw [hfr w (hcl w hw) A hA σ hσ, hn]
    · simp
  obtain ⟨D⟩ := Wc.exL F l ι hsplit
  have hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2 := by
    obtain ⟨u, A, h2, hA, hnA⟩ := hram
    refine ⟨u, ?_, h2⟩
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal
    · rw [hlev1 u hl]; exact one_ne_zero
    · rw [hlev u hl]; exact fun h => hnA ((hine u A hA).2 h)
  have hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1 := fun v => by
    rw [nu_eq]
    refine norm_eq_one (heu _ (D.mem v)) ?_
    rw [← map_sub]
    exact hlam _
  obtain ⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩ :=
    hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit
      {v | D.pl v ∈ P} 2
  have hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w -
      eisT l ω c P w)‖ < 1 := fun w => by
    rw [← sub_add_sub_cancel _ (lam w), map_add]
    exact add_lt (nu_lt.1 (hcong w)) (hlam w)
  have haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1 := fun w hw => by
    have h := hlam' w
    rwa [prod_away D _ t w hw, one_mul] at h
  obtain ⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩ := hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0)
    (levL l c) ω hfo φ' lam' hV hne heig hcusp
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol
  obtain ⟨hdet, hres⟩ := det_res ξ hc r hG.cont k hk hn
    (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
      obtain ⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩ := hw
      obtain ⟨B₂, hB₂, e⟩ := hsat w ((hlev w hl).trans h0)
      obtain rfl := hB₁.unique hB₂
      obtain ⟨h2, h3⟩ := tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)
      have h4 := haway w hl
      rw [eisT, if_neg hl, if_pos h0, map_sub, map_add, map_one, hfr w h0 A hA σ hσ] at h4
      rw [h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]
      exact ⟨h4, rfl⟩
  refine ⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r,
    ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩,
    hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hine w A hA]
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · simp [hl, hcl w hl]
    · simp [hl, hlev w hl]
  · obtain ⟨v, h1, h2, -⟩ := hU w
    rw [hw] at h2
    exact ⟨v, h1, h2⟩
  · refine ⟨lam' w, hU w, norm_one_of ?_⟩
    have h4 := haway w hl
    rwa [eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one] at h4
  · obtain ⟨v₀, hv₀⟩ := D.surj w hw
    have hnorm : normV w = l := hv₀ ▸ D.norm v₀
    have hc' := hlam' w
    rw [prod_at D _ t w v₀ hv₀] at hc'
    refine ⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩
    · by_cases h : w ∈ P <;> simp [h] <;> omega
    · by_cases h : w ∈ P <;> simp [h] <;> ring
    · rw [hnorm]
      by_cases h : w ∈ P
      · have hv : v₀ ∈ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm] at hc'
        rw [if_pos h]
        simpa using hc'
      · have hv : v₀ ∉ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_neg hv, one_mul, map_sub] at hc'
        rw [if_neg h]
        simpa using hc'
    · obtain ⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v := ⟨_, rfl⟩
      have hv : D.pl v = w := hvd ▸ (D.embAt τ w).1 hτ
      rw [hvd]
      convert hinf v using 3
      by_cases h : w ∈ P
      · have hS : v ∈ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
      · have hS : v ∉ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
  · simp only [eisT, if_pos hw, if_pos h]
    exact hfr w (hcl w hw) A hA σ hσ
  · simp only [eisT, if_pos hw, if_neg h, map_one]
end
