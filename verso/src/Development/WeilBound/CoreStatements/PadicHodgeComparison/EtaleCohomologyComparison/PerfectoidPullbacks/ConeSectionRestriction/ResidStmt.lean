import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TraceChart
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ChartExt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResR
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.InfinityCoordAlgebraicIndependent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

/- English proof (translation)
Introduce `K _ _ n R _ _ _ t ht D hD B hTB hFG hInt hMono hFrac ω η hω hη heq`. Establish `hne : ∀ i : Fin (n + 2), (Finset.univ.erase i).Nonempty` using `fun i => by`. Rewrite using `[← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Establish `hune : (Finset.univ : Finset (Fin (n + 2))).Nonempty` using `Finset.univ_nonempty`.

Establish `hfin : FiniteDimensional (fldF K t) (FractionRing R)` using `fldF_findim t (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac`. Take `⟨res, hres1, hres0, hresD⟩` from `res_R t ht D hD`. Set `Φ : R →+ FractionRing R` to `((algebraMap (fldF K t) (FractionRing R)).toAddMonoidHom.comp (Algebra.trace (fldF K t) (FractionRing R)).toAddMonoidHom).comp (algebraMap R (FractionRing R)).toAddMonoidHom`. Establish `hΦ : ∀ x, Φ x = algebraMap (fldF K t) (FractionRing R) (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) x))` using `fun _ => rfl`. Establish `hchart : ∀ i : Fin (n + 2), ∃ B' : Subalgebra K R, B (Finset.univ.erase i) ≤ B' ∧ torusS K t (Finset.univ.erase i) ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral (torusS K t (Finset.univ.erase i)) b) ∧ ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b` using `fun i => by`.

Take `⟨w, hwA, hw0, hscale⟩` from `torus_scale (K := K) t i`. Take `⟨B', hB', hFG', hInt', hFrac'⟩` from `chart_ext (torusS K t (Finset.univ.erase i)) (torusS K t Finset.univ) (B (Finset.univ.erase i)) (B Finset.univ) (torusS_le_univ t _) (hTB _ (hne i)) (hMono i) (hTB _ hune) (hFG _ (hne i)) (hInt _ (hne i)) (hFG _ hune) (hInt _ hune) hFrac w hwA hw0 hscale`. Conclude with `⟨B', hB', (hTB _ (hne i)).trans hB', hFG', hInt', hFrac'⟩`. Establish `hω' : ∀ i, ∃ a : R, Φ (ω i) = algebraMap R (FractionRing R) a ∧ res a = 0`. Introduce `i`.

Take `⟨B', hB', hTB', hFG', hInt', hFrac'⟩` from `hchart i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Take `⟨y', hy', hyeq⟩` from `jacobian_infinityDerivation t D (B (Finset.univ.erase 0)) (ω 0) (hω 0)`. Take `⟨hinj, hloc⟩` from `infinityCoord_localization t ht`.

Take `⟨a', ha'S, ha'⟩` from `trace_chart t (Finset.univ.erase 0) (fun k => ⟨u0 t k, infinityCoord_mem_torus t k⟩) hinj hloc (torusS_frac t _ (hne 0)) B' hTB' hFG' hInt' hFrac' (infinityDerivation t D) (fun k j => infinityDerivation_coord t D hD k j) id Function.injective_id y' (jacS_mono _ _ hB' _ _ hy')`. Use `set c : R := -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) with hc`. Establish `hcT : c ∈ torusS K t Finset.univ` using `neg_mem (pow_mem (inv_mem_univ t 0) _)`. Set `cF : fldF K t` to `⟨algebraMap R (FractionRing R) c, torus_mem_fldF t Finset.univ c hcT⟩`. Use `⟨c * a', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hΦ, hyeq, RingHom.map_mul (algebraMap R (FractionRing R)) c y']`. Establish `h1 : algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) y' = cF • algebraMap R (FractionRing R) y'` using `rfl`. Rewrite using `[h1, LinearMap.map_smul, smul_eq_mul, RingHom.map_mul, ha', RingHom.map_mul]`. Both sides reduce to the same expression. Rewrite using `[hc, neg_mul, map_neg, hres0 _ (infinityCoord_span_residue_ne t a' ha'S), neg_zero]`.

Consider the case `succ k`. Establish `h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ` using `Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩`. Take `⟨hinj, hloc⟩` from `torusS_loc t ht _ h0`. Take `⟨a, haS, ha⟩` from `trace_chart t (Finset.univ.erase k.succ) (fun k => ⟨t k, t_mem_torusS t _ h0 k⟩) hinj hloc (torusS_frac t _ (hne _)) B' hTB' hFG' hInt' hFrac' D (fun k j => hD k j) id Function.injective_id (ω k.succ) (jacS_mono _ _ hB' _ _ (hω k.succ))`. Conclude with `⟨a, ha, hres0 _ (torusS_succ_span t k a haS)⟩`.

Establish `hη' : ∀ k, ∃ b : R, Φ (D k (η k)) = algebraMap R (FractionRing R) b ∧ res b = 0`. Introduce `k`. Take `⟨hinj, hloc⟩` from `torusS_loc t ht Finset.univ (Finset.mem_univ 0)`. Take `⟨b, hbT, hb⟩` from `trace_chart t Finset.univ (fun k => ⟨t k, t_mem_torusS t _ (Finset.mem_univ 0) k⟩) hinj hloc (torusS_frac t _ hune) (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac D (fun k j => hD k j) (Fin.succAbove k) Fin.succAbove_right_injective (η k) (hη k)`. Establish `hDc : ∀ j, D k (t j : R) ∈ Set.range (algebraMap K R)` using `fun j => by`.

Rewrite using `[hD]`. Use `split_ifs`. Conclude with `⟨1, map_one _⟩`. Conclude with `⟨0, map_zero _⟩`. Conclude with `⟨D k b, trace_deriv t (D k) hDc (η k) b hbT hb, hresD k b hbT⟩`.

Use `choose a ha using hω'`. Use `choose b hb using hη'`. Establish `: Module.Free (fldF K t) (FractionRing R)` using `Module.Free.of_divisionRing _ _`. Establish `hp : (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ` using `prod_inv_mem t`. Set `pF : fldF K t` to `⟨algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R), torus_mem_fldF t _ _ hp⟩`.

Establish `hsign : ∀ (k : Fin (n + 1)) (x : R), (-1 : R) ^ (k : ℕ) * x = ((-1 : ℤ) ^ (k : ℕ)) • x` using `fun k x => by`. Rewrite using `[zsmul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hrel : Module.finrank (fldF K t) (FractionRing R) • (((∏ k, t k)⁻¹ : Rˣ) : R) = ∑ i, a i + ∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) • b k`.

Apply `IsFractionRing.injective R (FractionRing R)` to reduce the goal to its premises. Establish `h1` using `congrArg Φ heq`. Simplify using `only [map_add, map_sum, hsign] at h1`. Rewrite using `[map_nsmul, map_add, map_sum, map_sum]`. Simplify using `only [map_zsmul]`.

Simplify using `only [map_zsmul, fun i => (ha i).1, fun k => (hb k).1] at h1`. Rewrite using `[← h1, hΦ]`. Establish `h2 : algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R) = algebraMap (fldF K t) (FractionRing R) pF` using `rfl`. Rewrite using `[h2, Algebra.trace_algebraMap, map_nsmul]`. Establish `hres` using `congrArg res hrel`.

Rewrite `hres` using `[map_nsmul, hres1, map_add, map_sum, map_sum]`. Simplify using `only [map_zsmul, fun i => (ha i).2, fun k => (hb k).2, smul_zero, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one] at hres`. Rewrite `hres` using `[Nat.cast_eq_zero]`. Conclude with `(Module.finrank_pos (R := fldF K t) (M := FractionRing R)).ne' hres`.
-/
theorem resid_alg : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [Algebra K R]
    (t : Fin (n + 1) → Rˣ), AlgebraicIndependent K (fun k => (t k : R)) →
    ∀ (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    ∀ (B : Finset (Fin (n + 2)) → Subalgebra K R), (∀ S, S.Nonempty → torusS K t S ≤ B S) → (∀ S, S.Nonempty → (B S).FG) →
    (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K t S) b) → (∀ i, B (Finset.univ.erase i) ≤ B Finset.univ) →
    (∀ r : R, ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) →
    ∀ (ω : Fin (n + 2) → R) (η : Fin (n + 1) → R), (∀ i, ω i ∈ jacS (B (Finset.univ.erase i)) D id) →
      (∀ k, η k ∈ jacS (B Finset.univ) D (Fin.succAbove k)) →
      ((∏ k, t k)⁻¹ : Rˣ) ≠ (∑ i, ω i + ∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * D k (η k) : R) :=
  by
  intro K _ _ n R _ _ _ t ht D hD B hTB hFG hInt hMono hFrac ω η hω hη heq
  have hne : ∀ i : Fin (n + 2), (Finset.univ.erase i).Nonempty := fun i => by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hune : (Finset.univ : Finset (Fin (n + 2))).Nonempty := Finset.univ_nonempty
  have hfin : FiniteDimensional (fldF K t) (FractionRing R) :=
    fldF_findim t (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac
  obtain ⟨res, hres1, hres0, hresD⟩ := res_R t ht D hD

  let Φ : R →+ FractionRing R :=
    ((algebraMap (fldF K t) (FractionRing R)).toAddMonoidHom.comp
      (Algebra.trace (fldF K t) (FractionRing R)).toAddMonoidHom).comp
      (algebraMap R (FractionRing R)).toAddMonoidHom
  have hΦ : ∀ x, Φ x = algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) x)) := fun _ => rfl

  have hchart : ∀ i : Fin (n + 2), ∃ B' : Subalgebra K R, B (Finset.univ.erase i) ≤ B' ∧
      torusS K t (Finset.univ.erase i) ≤ B' ∧ B'.FG ∧
      (∀ b ∈ B', IsIntegral (torusS K t (Finset.univ.erase i)) b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := fun i => by
    obtain ⟨w, hwA, hw0, hscale⟩ := torus_scale (K := K) t i
    obtain ⟨B', hB', hFG', hInt', hFrac'⟩ := chart_ext (torusS K t (Finset.univ.erase i)) (torusS K t Finset.univ)
      (B (Finset.univ.erase i)) (B Finset.univ) (torusS_le_univ t _) (hTB _ (hne i)) (hMono i) (hTB _ hune)
      (hFG _ (hne i)) (hInt _ (hne i)) (hFG _ hune) (hInt _ hune) hFrac w hwA hw0 hscale
    exact ⟨B', hB', (hTB _ (hne i)).trans hB', hFG', hInt', hFrac'⟩

  have hω' : ∀ i, ∃ a : R, Φ (ω i) = algebraMap R (FractionRing R) a ∧ res a = 0 := by
    intro i
    obtain ⟨B', hB', hTB', hFG', hInt', hFrac'⟩ := hchart i
    induction i using Fin.cases with
    | zero =>
      obtain ⟨y', hy', hyeq⟩ := jacobian_infinityDerivation t D (B (Finset.univ.erase 0)) (ω 0) (hω 0)
      obtain ⟨hinj, hloc⟩ := infinityCoord_localization t ht
      obtain ⟨a', ha'S, ha'⟩ := trace_chart t (Finset.univ.erase 0) (fun k => ⟨u0 t k, infinityCoord_mem_torus t k⟩) hinj hloc
        (torusS_frac t _ (hne 0)) B' hTB' hFG' hInt' hFrac' (infinityDerivation t D) (fun k j => infinityDerivation_coord t D hD k j) id
        Function.injective_id y' (jacS_mono _ _ hB' _ _ hy')
      set c : R := -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) with hc
      have hcT : c ∈ torusS K t Finset.univ := neg_mem (pow_mem (inv_mem_univ t 0) _)
      let cF : fldF K t := ⟨algebraMap R (FractionRing R) c, torus_mem_fldF t Finset.univ c hcT⟩
      refine ⟨c * a', ?_, ?_⟩
      · rw [hΦ, hyeq, RingHom.map_mul (algebraMap R (FractionRing R)) c y']
        have h1 : algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) y' =
            cF • algebraMap R (FractionRing R) y' := rfl
        rw [h1, LinearMap.map_smul, smul_eq_mul, RingHom.map_mul, ha', RingHom.map_mul]
        rfl
      · rw [hc, neg_mul, map_neg, hres0 _ (infinityCoord_span_residue_ne t a' ha'S), neg_zero]
    | succ k =>
      have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ :=
        Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩
      obtain ⟨hinj, hloc⟩ := torusS_loc t ht _ h0
      obtain ⟨a, haS, ha⟩ := trace_chart t (Finset.univ.erase k.succ)
        (fun k => ⟨t k, t_mem_torusS t _ h0 k⟩) hinj hloc
        (torusS_frac t _ (hne _)) B' hTB' hFG' hInt' hFrac' D (fun k j => hD k j) id
        Function.injective_id (ω k.succ) (jacS_mono _ _ hB' _ _ (hω k.succ))
      exact ⟨a, ha, hres0 _ (torusS_succ_span t k a haS)⟩

  have hη' : ∀ k, ∃ b : R, Φ (D k (η k)) = algebraMap R (FractionRing R) b ∧ res b = 0 := by
    intro k
    obtain ⟨hinj, hloc⟩ := torusS_loc t ht Finset.univ (Finset.mem_univ 0)
    obtain ⟨b, hbT, hb⟩ := trace_chart t Finset.univ (fun k => ⟨t k, t_mem_torusS t _ (Finset.mem_univ 0) k⟩)
      hinj hloc (torusS_frac t _ hune) (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac D
      (fun k j => hD k j) (Fin.succAbove k) Fin.succAbove_right_injective (η k) (hη k)
    have hDc : ∀ j, D k (t j : R) ∈ Set.range (algebraMap K R) := fun j => by
      rw [hD]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    exact ⟨D k b, trace_deriv t (D k) hDc (η k) b hbT hb, hresD k b hbT⟩
  choose a ha using hω'
  choose b hb using hη'

  have : Module.Free (fldF K t) (FractionRing R) := Module.Free.of_divisionRing _ _
  have hp : (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := prod_inv_mem t
  let pF : fldF K t := ⟨algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R), torus_mem_fldF t _ _ hp⟩
  have hsign : ∀ (k : Fin (n + 1)) (x : R), (-1 : R) ^ (k : ℕ) * x = ((-1 : ℤ) ^ (k : ℕ)) • x := fun k x => by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  have hrel : Module.finrank (fldF K t) (FractionRing R) • (((∏ k, t k)⁻¹ : Rˣ) : R) =
      ∑ i, a i + ∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) • b k := by
    apply IsFractionRing.injective R (FractionRing R)
    have h1 := congrArg Φ heq
    simp only [map_add, map_sum, hsign] at h1
    rw [map_nsmul, map_add, map_sum, map_sum]
    simp only [map_zsmul]
    simp only [map_zsmul, fun i => (ha i).1, fun k => (hb k).1] at h1
    rw [← h1, hΦ]
    have h2 : algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R) =
        algebraMap (fldF K t) (FractionRing R) pF := rfl
    rw [h2, Algebra.trace_algebraMap, map_nsmul]
  have hres := congrArg res hrel
  rw [map_nsmul, hres1, map_add, map_sum, map_sum] at hres
  simp only [map_zsmul, fun i => (ha i).2, fun k => (hb k).2, smul_zero, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, mul_one] at hres
  rw [Nat.cast_eq_zero] at hres
  exact (Module.finrank_pos (R := fldF K t) (M := FractionRing R)).ne' hres

end CrystallineSemistableComparison.Pb
