import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

/- English proof (translation)
Establish `hlpos : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hl : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `hlk : (l : ℚ_[l]) ^ k ≠ 0` using `pow_ne_zero k hl`. Establish `hy : ‖x / (l : ℚ_[l]) ^ k‖ ≤ 1`. Rewrite using `[norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hlpos _)]`.

Conclude with `hx`. Choose the witnesses or unpack the hypotheses as in `⟨y, hxy⟩ : ∃ y : ℤ_[l], x = (l : ℚ_[l]) ^ k * (y : ℚ_[l]) := by`. Use `⟨⟨x / (l : ℚ_[l]) ^ k, hy⟩, ?_⟩` and prove the remaining obligations. Use `show x = (l : ℚ_[l]) ^ k * (x / (l : ℚ_[l]) ^ k)`. Clear the denominators using the available nonvanishing facts.

Establish `hmem : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) ∈ OL LL`. Establish `e : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) = algebraMap ℤ_[l] ↥LL.1 y` using `rfl`. Rewrite using `[e]`. Conclude with `(OL LL).algebraMap_mem y`. Establish `hv0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]))` using `(P.27 LL _).2 hmem`.

Establish `hk : k • (1 : WithTop ℚ) = ((k : ℚ) : WithTop ℚ)`. Rewrite using `[← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]`. Rewrite using `[hxy, map_mul, map_pow, map_natCast, (P.v LL).map_mul, (P.v LL).map_pow, P.26 LL, hk]`. Conclude with `le_add_of_nonneg_right hv0`.
-/
theorem le_v_of_norm_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (hx : ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ))) :
    ((k : ℚ) : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlk : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero k hl
  have hy : ‖x / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hlpos _)]
    exact hx
  obtain ⟨y, hxy⟩ : ∃ y : ℤ_[l], x = (l : ℚ_[l]) ^ k * (y : ℚ_[l]) := by
    refine ⟨⟨x / (l : ℚ_[l]) ^ k, hy⟩, ?_⟩
    show x = (l : ℚ_[l]) ^ k * (x / (l : ℚ_[l]) ^ k)
    field_simp
  have hmem : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) ∈ OL LL := by
    have e : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) = algebraMap ℤ_[l] ↥LL.1 y := rfl
    rw [e]
    exact (OL LL).algebraMap_mem y
  have hv0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l])) := (P.27 LL _).2 hmem
  have hk : k • (1 : WithTop ℚ) = ((k : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  rw [hxy, map_mul, map_pow, map_natCast, (P.v LL).map_mul, (P.v LL).map_pow, P.26 LL, hk]
  exact le_add_of_nonneg_right hv0

/- English proof (translation)
Introduce `l _ P _ K s LL _ W hW g`. Establish `hcyc : IsCyc P.χQ` using `P.20`. Establish `hχ : ((P.PD K).χ g : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l])` using `P.PD_χ K g`. Use `⟨fun hg => ?_, fun hg => ?_⟩` and prove the remaining obligations. Unfold `Gj at hg`.

Take `⟨ζ, hζ⟩` from `exists_primRoot_pow (l := l) s`. Establish `hmem : ζ ∈ Ks K s`. Unfold `Ks`. Conclude with `(le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ _) (IntermediateField.subset_adjoin ℚ_[l] _ hζ.pow_eq_one)`. Establish `hfix : (g : GQ l) ζ = ζ` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem`.

Establish `hn : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ))` using `hcyc.norm_sub_one_le_of_prim (g : GQ l) s hζ hfix`. Establish `hv` using `le_v_of_norm_le P LL ((P.χQ (g : GQ l) : ℚ_[l]) - 1) s hn`. Establish `e : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) - 1 = algebraMap ℚ_[l] ↥LL.1 ((P.χQ (g : GQ l) : ℚ_[l]) - 1)`. Rewrite using `[hχ, map_sub, map_one]`. Rewrite using `[W.GKs_def g, hW, e]`.

Conclude with `hv` after adjusting the coercions. Unfold `Hinf at hg`. Establish `hall : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Introduce `m`. Use `(hcyc.fix_iff (g : GQ l) m).1 (fun ζ hζ => ?_)` and prove the remaining obligations.

Establish `hmem : ζ ∈ Kinf K`. Unfold `Kinf`. Conclude with `(le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} ≤ _) (IntermediateField.subset_adjoin ℚ_[l] _ ⟨m, hζ⟩)`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem`. Establish `h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1`.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hne)`. Take `⟨m, hm⟩` from `exists_zpow_neg_lt (l := l) hpos`. Conclude with `absurd (hall m) (not_le.2 hm)`. Establish `h2 : (algebraMap ↥(OL LL) ↥LL.1) ↑(W.χΓ (W.resΓ g)) = 1`.

Rewrite using `[W.χΓ_res g, hχ, h1, map_one]`. Establish `h3 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1` using `Subtype.ext h2`. Establish `h4 : W.χΓ (W.resΓ g) = 1` using `Units.val_eq_one.1 h3`. Conclude with `W.χΓ_inj (by rw [h4, map_one])`.
-/
theorem grp_GKs_H : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  intro l _ P _ K s LL _ W hW g
  have hcyc : IsCyc P.χQ := P.20
  have hχ : ((P.PD K).χ g : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := P.PD_χ K g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · unfold Gj at hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) s
    have hmem : ζ ∈ Ks K s := by
      unfold Ks
      exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ _)
        (IntermediateField.subset_adjoin ℚ_[l] _ hζ.pow_eq_one)
    have hfix : (g : GQ l) ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have hn : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) :=
      hcyc.norm_sub_one_le_of_prim (g : GQ l) s hζ hfix
    have hv := le_v_of_norm_le P LL ((P.χQ (g : GQ l) : ℚ_[l]) - 1) s hn
    have e : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) - 1 =
        algebraMap ℚ_[l] ↥LL.1 ((P.χQ (g : GQ l) : ℚ_[l]) - 1) := by
      rw [hχ, map_sub, map_one]
    rw [W.GKs_def g, hW, e]
    exact_mod_cast hv
  · unfold Hinf at hg
    have hall : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      intro m
      refine (hcyc.fix_iff (g : GQ l) m).1 (fun ζ hζ => ?_)
      have hmem : ζ ∈ Kinf K := by
        unfold Kinf
        exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} ≤ _)
          (IntermediateField.subset_adjoin ℚ_[l] _ ⟨m, hζ⟩)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      by_contra hne
      have hpos : 0 < ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd (hall m) (not_le.2 hm)
    have h2 : (algebraMap ↥(OL LL) ↥LL.1) ↑(W.χΓ (W.resΓ g)) = 1 := by
      rw [W.χΓ_res g, hχ, h1, map_one]
    have h3 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 := Subtype.ext h2
    have h4 : W.χΓ (W.resΓ g) = 1 := Units.val_eq_one.1 h3
    exact W.χΓ_inj (by rw [h4, map_one])

end GlobalTheory.Cyc.Decomp
