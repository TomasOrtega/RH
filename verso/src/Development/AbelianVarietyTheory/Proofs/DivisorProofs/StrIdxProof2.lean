import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

/- English proof (translation)
Introduce `n ε P`. Use `choose Qm hQm using fun s s' : Finset (Fin (n * n)) => ffMat_poly (ε := ε) s s'`. Use `set Q : Poly n := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef`. Establish `hQ : ∀ m : Mat n, ev m Q = physDet ε m`. Introduce `m`.

Use `show MvPolynomial.eval (entVar m) Q = _`. Rewrite using `[← strPhys_eq_physDet, strPhys, hQdef, map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eval, hQm]`. Both sides reduce to the same expression.

Take `⟨d2, hd2⟩ : ∃ d2 : ℕ, ∀ s s' : Finset (Fin (n * n)), (P * Qm s s').totalDegree ≤ d2` from `⟨∑ s, ∑ s', (P * Qm s s').totalDegree, fun s s' => le_trans (Finset.single_le_sum (f := fun s' => (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s')) (Finset.single_le_sum (f := fun s => ∑ s', (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _) (Finset.m …`. Use `⟨max (P * Q).totalDegree d2, ?_⟩` and prove the remaining obligations. Introduce `H _ _ _ σ D E hσ hD L _ hLK hLd Y _ hY0Y hYP hG hK B hB`. Establish `hdeg1 : (P * Q).totalDegree ≤ max (P * Q).totalDegree d2` using `le_max_left _ _`. Establish `hdeg2 : ∀ s s', (P * Qm s s').totalDegree ≤ max (P * Q).totalDegree d2` using `fun s s' => (hd2 s s').trans (le_max_right _ _)`.

Establish `hemb : Topology.IsEmbedding (fun k : KG ε => toMK k)` using `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)` using `inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Establish `: SecondCountableTopology (KG ε)` using `hemb.isInducing.secondCountableTopology`. Establish `hφc : Continuous (fun k : KG ε => toMK k)` using `hemb.continuous`. Establish `hφK : ∀ g : KG ε, toMK g ∈ Kset ε` using `fun g => g.2`.

Establish `hent : ∀ R : Poly n, Continuous fun k : KG ε => ev (toMK k) R`. Introduce `R`. Use `(MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)` and prove the remaining obligations. Break down `p with p | p` into its components or cases. Conclude with `(continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)`.

Conclude with `continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))`. Establish `hBL : ∀ w, B w ∈ L.map D.subtype`. Introduce `w`. Rewrite using `[hB]`. Use `hLd (P * Q) hdeg1 w` as an intermediate fact.

Simplify `this` using `only [map_mul, hQ]`. Use `⟨hBL, ?_⟩` and prove the remaining obligations. Establish `hAL : ∀ k : KG ε, ∀ x ∈ L.map D.subtype, σ (toMK k) x ∈ L.map D.subtype`. Introduce and unpack `k _ ⟨y, hy, rfl⟩`. Conclude with `⟨sigD hD (hφK k) y, hLK _ (hφK k) y hy, rfl⟩`.

Establish `hAc : ∀ v, Continuous fun k : KG ε => σ (toMK k) v` using `fun v => (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)`. Establish `hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k)`. Use `hent (P * Q)` as an intermediate fact. Simplify `this` using `only [map_mul, hQ]`. Rewrite using `[trace_integral_restrict (μ := muK ε) (L.map D.subtype) hcont (fun k => σ (toMK k)) hAc hAL B hB (fun x _ => hBL x)]`.

Establish `hY0G : ∀ y ∈ tensFock (n` using `n) L ⊓ physicalSubspace (N := D) ε, gradT y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun y hy => ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε E).2.2.2.2 y hy.2⟩`. Establish `hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ tensFock (n` using `n) L ⊓ physicalSubspace (N := D) ε, wK hD hk y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun k hk y hy => ⟨wK_tensFock hD hk (hLK k hk) hy.1, wK_physSub hD hk hy.2⟩`. Establish `hpt : ∀ k : KG ε, ev (toMK k) P * physDet ε (toMK k) * LinearMap.trace ℂ (L.map D.subtype) (((σ (toMK k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) = ev (toMK k) P * LinearMap.trace ℂ ↥(tensFock (n` using `n) L ⊓ physicalSubspace (N := D) ε) ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by`. Introduce `k`. Rewrite using `[trace_map_subtype (sigD hD (hφK k)) (fun x hx => hLK _ (hφK k) x hx) _ _ (fun x => rfl)]`.

Use `str_tensFock_physSub hD (hφK k) (fun x hx => hLK _ (hφK k) x hx) (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))` as an intermediate fact. Rewrite using `[show LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε) ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hpt]`. Establish `hcP` using `hent P`.

Establish `hrange` using `fun y => btot_range (μ := muK ε) hσ hD hK (L := L) hφc hφK hcP (fun s s' u => by`. Establish `h1` using `hLd (P * Qm s s') (hdeg2 s s') u`. Establish `h2 : ∫ k : KG ε, (ev (toMK k) P * ffMat ε (toMK k) s s') • σ (toMK k) u ∂(muK ε) = ∫ k : KG ε, ev (toMK k) (P * Qm s s') • σ (toMK k) u ∂(muK ε)`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[map_mul, hQm]`. Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `h1) hYP y`. Conclude with `(int_str_eq (μ := muK ε) hσ hD hY0Y hK hY0K hG hY0G hφc hφK hcP hrange).symm`.
-/
theorem StrIdx_proof2 : StrIdx := by
  intro n ε P
  choose Qm hQm using fun s s' : Finset (Fin (n * n)) => ffMat_poly (ε := ε) s s'
  set Q : Poly n := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m : Mat n, ev m Q = physDet ε m := by
    intro m
    show MvPolynomial.eval (entVar m) Q = _
    rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, ∀ s s' : Finset (Fin (n * n)), (P * Qm s s').totalDegree ≤ d2 :=
    ⟨∑ s, ∑ s', (P * Qm s s').totalDegree, fun s s' =>
      le_trans (Finset.single_le_sum (f := fun s' => (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s'))
      (Finset.single_le_sum (f := fun s => ∑ s', (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s))⟩
  refine ⟨max (P * Q).totalDegree d2, ?_⟩
  intro H _ _ _ σ D E hσ hD L _ hLK hLd Y _ hY0Y hYP hG hK B hB
  have hdeg1 : (P * Q).totalDegree ≤ max (P * Q).totalDegree d2 := le_max_left _ _
  have hdeg2 : ∀ s s', (P * Qm s s').totalDegree ≤ max (P * Q).totalDegree d2 := fun s s' =>
    (hd2 s s').trans (le_max_right _ _)
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
  have hφc : Continuous (fun k : KG ε => toMK k) := hemb.continuous
  have hφK : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hent : ∀ R : Poly n, Continuous fun k : KG ε => ev (toMK k) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ L.map D.subtype := by
    intro w
    rw [hB]
    have := hLd (P * Q) hdeg1 w
    simpa only [map_mul, hQ] using this
  refine ⟨hBL, ?_⟩
  have hAL : ∀ k : KG ε, ∀ x ∈ L.map D.subtype, σ (toMK k) x ∈ L.map D.subtype := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, hLK _ (hφK k) y hy, rfl⟩
  have hAc : ∀ v, Continuous fun k : KG ε => σ (toMK k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := muK ε) (L.map D.subtype) hcont (fun k => σ (toMK k)) hAc hAL B hB
    (fun x _ => hBL x)]
  have hY0G : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε, gradT y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε :=
    fun y hy => ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε E).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε,
      wK hD hk y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun k hk y hy =>
    ⟨wK_tensFock hD hk (hLK k hk) hy.1, wK_physSub hD hk hy.2⟩
  have hpt : ∀ k : KG ε, ev (toMK k) P * physDet ε (toMK k) *
      LinearMap.trace ℂ (L.map D.subtype) (((σ (toMK k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      ev (toMK k) P * LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => hLK _ (hφK k) x hx) _ _ (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => hLK _ (hφK k) x hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]
  have hcP := hent P
  have hrange := fun y => btot_range (μ := muK ε) hσ hD hK (L := L) hφc hφK hcP
    (fun s s' u => by
      have h1 := hLd (P * Qm s s') (hdeg2 s s') u
      have h2 : ∫ k : KG ε, (ev (toMK k) P * ffMat ε (toMK k) s s') • σ (toMK k) u ∂(muK ε) =
          ∫ k : KG ε, ev (toMK k) (P * Qm s s') • σ (toMK k) u ∂(muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      rw [h2]
      exact h1) hYP y
  exact (int_str_eq (μ := muK ε) hσ hD hY0Y hK hY0K hG hY0G hφc hφK hcP hrange).symm

end GlobalTheory.PsCo.PcEF

end
end
