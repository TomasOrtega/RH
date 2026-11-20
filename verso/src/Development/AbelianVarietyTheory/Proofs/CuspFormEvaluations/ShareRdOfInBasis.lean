import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPair
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpanStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

/- English proof (translation)
Consider the cases of `u`. Simplify using `[addL, wadd, wsmul]`.
-/
theorem addL_zero_wt (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  simp [addL, wadd, wsmul]

/- English proof (translation)
Establish `hL : Submodule.IsLattice B.KO (B.Mlat j ka)` using `h`. Unfold `PJ.rk`. Rewrite using `[hL.span_eq_top]`.
-/
theorem rk_Mlat_eq_finrank (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (h : LatAt B j ka) :
    X.rk ka (B.Mlat j ka) = Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
  have hL : Submodule.IsLattice B.KO (B.Mlat j ka) := h
  unfold PJ.rk
  rw [hL.span_eq_top]

/- English proof (translation)
Unfold `Rdg.s Rdg.sp`. Use `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨w k, Set.mem_univ _, rfl⟩`.
-/
private lemma s_mem_sp_univ (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) : R.s w t i ∈ R.sp wL Set.univ := by
  unfold Rdg.s Rdg.sp
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨w k, Set.mem_univ _, rfl⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hv`. Consider the case `succ m ih`. Rewrite using `[pow_succ', mul_assoc, ← Nat.add_assoc, ← wadd_addL]`. Conclude with `hmul _ _ _ (s_mem_sp_univ R w t i) _ ih`.
-/
theorem Rdg.s_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) : R.s w t i ^ m * v ∈ R.sp (addL u wL (n + m)) Set.univ := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>

    rw [pow_succ', mul_assoc, ← Nat.add_assoc, ← wadd_addL]
    exact hmul _ _ _ (s_mem_sp_univ R w t i) _ ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hv`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]`. Establish `h` using `R.s_pow_mul_mem w t hmul a.succ u (n + ∑ i ∈ s, α i) (α a) ih`.

Establish `e : n + (α a + ∑ i ∈ s, α i) = n + ∑ i ∈ s, α i + α a` using `by ring`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem Rdg.prod_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j))) (u : WeightFamilies.Wt D j) (n : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) :
    (∏ i ∈ s, R.s w t i.succ ^ α i) * v ∈ R.sp (addL u wL (n + ∑ i ∈ s, α i)) Set.univ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have h := R.s_pow_mul_mem w t hmul a.succ u (n + ∑ i ∈ s, α i) (α a) ih
    have e : n + (α a + ∑ i ∈ s, α i) = n + ∑ i ∈ s, α i + α a := by ring
    rw [e]
    exact h

/- English proof (translation)
Introduce `D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka hDT _ hlat hex`. Take `⟨la, hla⟩` from `hex`. Establish `hI` using `(GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka la).1 hla`. Take `⟨-, -, -, -, -, hmul, -, hfin⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t`. Establish `hθ : ∀ i, R.ev (X.inc wF (G.th' i)) ∈ R.sp wF Set.univ` using `fun i => Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩`.

Establish `hLI` using `(hfac.indep G.del (fun i => R.ev (X.inc wF (G.th' i))) hθ hI.1).1`. Establish `hmem : ∀ p, R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p ∈ R.sp ka Set.univ`. Introduce and unpack `⟨⟨α, hα⟩, i⟩`. Establish `h0 : R.ev (X.inc wF (G.th' i)) ∈ R.sp (addL wF wL 0) Set.univ`. Rewrite using `[addL_zero_wt]`.

Conclude with `hθ i`. Establish `h1` using `R.s_pow_mul_mem G.w t hmul 0 wF 0 (T - ∑ k, α k) h0`. Establish `h2` using `R.prod_pow_mul_mem G.w t hmul α Finset.univ wF (0 + (T - ∑ k, α k)) h1`. Establish `hle : ∑ k, α k ≤ T`. Unfold `a0 at hα`.

Use linear arithmetic over natural numbers and integers. Establish `e : 0 + (T - ∑ k, α k) + ∑ k ∈ Finset.univ, α k = T` using `by omega`. Rewrite `h2` using `[e, hka]`. Use `show R.mon G.w t α * R.s G.w t 0 ^ (T - ∑ k, α k) * R.ev (X.inc wF (G.th' i)) ∈ R.sp ka Set.univ`. Rewrite using `[mul_assoc]`.

Conclude with `h2`. Take `⟨hfd, hfr⟩` from `hfin ka ⊤`. Rewrite `hfd`, `hfr` using `[Submodule.top_coe]`. Establish `hcard : Nat.card ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del) ≤ Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka))`. Rewrite using `[← hfr]`.

Use `haveI : FiniteDimensional ℂ (R.sp ka Set.univ) := hfd`. Establish `hLI' : LinearIndependent ℂ (fun p => (⟨R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p, hmem p⟩ : R.sp ka Set.univ))` using `LinearIndependent.of_comp (R.sp ka Set.univ).subtype hLI`. Use `haveI := hLI'.finite`. Use `haveI := Fintype.ofFinite ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del)`. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `hLI'.fintype_card_le_finrank`. Establish `hcnt : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} = (T - 1).choose (WeightFamilies.dimY D j)` using `GlobalTheory.card_exponents_sum_lt_sub _ _ hDT`. Rewrite `hcard` using `[Nat.card_prod, Nat.card_fin, hcnt]`. Unfold `ShareRd`. Rewrite using `[rk_Mlat_eq_finrank X ka hlat]`.

Conclude with `hcard` after adjusting the coercions.
-/
theorem shareRd_of_inBasis : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → WeightFamilies.dimY D j < T → 0 < WeightFamilies.dimY D j → LatAt B j ka → (∃ la, InBasis G la) → ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka hDT _ hlat hex
  obtain ⟨la, hla⟩ := hex

  have hI := (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka la).1 hla
  obtain ⟨-, -, -, -, -, hmul, -, hfin⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hθ : ∀ i, R.ev (X.inc wF (G.th' i)) ∈ R.sp wF Set.univ := fun i =>
    Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩

  have hLI := (hfac.indep G.del (fun i => R.ev (X.inc wF (G.th' i))) hθ hI.1).1

  have hmem : ∀ p, R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p ∈
      R.sp ka Set.univ := by
    rintro ⟨⟨α, hα⟩, i⟩
    have h0 : R.ev (X.inc wF (G.th' i)) ∈ R.sp (addL wF wL 0) Set.univ := by
      rw [addL_zero_wt]
      exact hθ i
    have h1 := R.s_pow_mul_mem G.w t hmul 0 wF 0 (T - ∑ k, α k) h0
    have h2 := R.prod_pow_mul_mem G.w t hmul α Finset.univ wF (0 + (T - ∑ k, α k)) h1
    have hle : ∑ k, α k ≤ T := by
      unfold a0 at hα
      omega
    have e : 0 + (T - ∑ k, α k) + ∑ k ∈ Finset.univ, α k = T := by omega
    rw [e, hka] at h2
    show R.mon G.w t α * R.s G.w t 0 ^ (T - ∑ k, α k) * R.ev (X.inc wF (G.th' i)) ∈ R.sp ka Set.univ
    rw [mul_assoc]
    exact h2

  obtain ⟨hfd, hfr⟩ := hfin ka ⊤
  rw [Submodule.top_coe] at hfd hfr
  have hcard : Nat.card ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del) ≤
      Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
    rw [← hfr]
    haveI : FiniteDimensional ℂ (R.sp ka Set.univ) := hfd
    have hLI' : LinearIndependent ℂ (fun p =>
        (⟨R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p, hmem p⟩ :
          R.sp ka Set.univ)) :=
      LinearIndependent.of_comp (R.sp ka Set.univ).subtype hLI
    haveI := hLI'.finite
    haveI := Fintype.ofFinite ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del)
    rw [Nat.card_eq_fintype_card]
    exact hLI'.fintype_card_le_finrank
  have hcnt : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} =
      (T - 1).choose (WeightFamilies.dimY D j) :=
    GlobalTheory.card_exponents_sum_lt_sub _ _ hDT
  rw [Nat.card_prod, Nat.card_fin, hcnt] at hcard
  unfold ShareRd
  rw [rk_Mlat_eq_finrank X ka hlat]
  exact_mod_cast hcard

end GlobalTheory.Shares
