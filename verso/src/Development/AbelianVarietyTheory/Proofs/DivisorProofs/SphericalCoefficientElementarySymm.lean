import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.SphPar

/- English proof (translation)
Establish `h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0`. Simplify using `[dualLab, splitLab]`. Rewrite using `[h]`. Use `split_ifs with hi`. Rewrite using `[List.getD_append _ _ _ _ (by simpa using hi)]`.

Simplify using `[List.getD_eq_getElem?_getD, hi]`. Rewrite using `[List.getD_append_right _ _ _ _ (by simpa using hi)]`. Simplify using `only [List.getD_eq_getElem?_getD, List.getElem?_replicate]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem dualLab_splitLab_getD (n k : ℕ) (i : ℕ) :
    (dualLab (splitLab n k)).getD i 0 = if i < k then 1 else 0 := by
  have h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0 := by
    simp [dualLab, splitLab]
  rw [h]
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

/- English proof (translation)
Unfold `diagJ`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[dualLab_splitLab_getD]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem diagonal_dualLab_splitLab {L : Type} [Field L] (n k : ℕ) (ϖ : L) :
    Matrix.diagonal (fun i : Fin n => ϖ ^ (dualLab (splitLab n k)).getD i 0) = diagJ n ϖ k := by
  unfold diagJ
  congr 1
  funext i
  rw [dualLab_splitLab_getD]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨π, hπ⟩` from `P.valuation_exists_uniformizer E`. Use `⟨(π : P.adicCompletion E), ?_⟩` and prove the remaining obligations. Unfold `IsUnifV`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`. Both sides reduce to the same expression.
-/
theorem exists_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : P.adicCompletion E, IsUnifV E P ϖ := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  refine ⟨(π : P.adicCompletion E), ?_⟩
  unfold IsUnifV
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  rfl

/- English proof (translation)
Unfold `IsUnifV at h h'`. Establish `hv0 : Valued.v ϖ ≠ 0` using `by rw [h]; exact WithZero.coe_ne_zero`. Establish `hv0' : Valued.v ϖ' ≠ 0` using `by rw [h']; exact WithZero.coe_ne_zero`. Establish `h0 : ϖ ≠ 0` using `fun e => hv0 (by rw [e, map_zero])`. Establish `h0' : ϖ' ≠ 0` using `fun e => hv0' (by rw [e, map_zero])`.

Establish `hu : Valued.v (ϖ' / ϖ) = 1`. Rewrite using `[map_div₀, h', ← h, div_self hv0]`. Establish `e : ϖ' = ϖ' / ϖ * ϖ` using `(div_mul_cancel₀ _ h0).symm`. Rewrite using `[e]`. Use `Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)` and prove the remaining obligations.

Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])`.
-/
theorem Tj_eq_of_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ ϖ' : P.adicCompletion E} (h : IsUnifV E P ϖ) (h' : IsUnifV E P ϖ') :
    Tj ℂ n (Ov E P) ϖ' k = Tj ℂ n (Ov E P) ϖ k := by
  unfold IsUnifV at h h'
  have hv0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hv0' : Valued.v ϖ' ≠ 0 := by rw [h']; exact WithZero.coe_ne_zero
  have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have h0' : ϖ' ≠ 0 := fun e => hv0' (by rw [e, map_zero])
  have hu : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, h', ← h, div_self hv0]
  have e : ϖ' = ϖ' / ϖ * ϖ := (div_mul_cancel₀ _ h0).symm
  rw [e]
  refine Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])

/- English proof (translation)
Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g`. Take `⟨ϖ', h', hab⟩` from `id hg`. Rewrite `hab` using `[diagonal_dualLab_splitLab]`. Rewrite using `[← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg), Set.indicator_of_mem (by exact hab)]`.

Rewrite using `[divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]`. Introduce `hab`. Use `hg ⟨ϖ, h, ?_⟩` and prove the remaining obligations. Rewrite using `[diagonal_dualLab_splitLab]`. Conclude with `hab`.
-/
theorem divInd_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ : P.adicCompletion E} (h : IsUnifV E P ϖ) :
    divInd (n := n) (Ov E P) (dualLab (splitLab n k)) = Tj ℂ n (Ov E P) ϖ k := by
  funext g
  by_cases hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g
  · obtain ⟨ϖ', h', hab⟩ := id hg
    rw [diagonal_dualLab_splitLab] at hab
    rw [← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg),
      Set.indicator_of_mem (by exact hab)]
  · rw [divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]
    intro hab
    refine hg ⟨ϖ, h, ?_⟩
    rw [diagonal_dualLab_splitLab]
    exact hab

/- English proof (translation)
Take `⟨hcard, h0, hpar⟩` from `hs`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : Fin n → ℂ, Finset.univ.val.map α = s := by`. Proceed by induction on `s using Quotient.inductionOn with`. Consider the case `h l`. Establish `hl' : l.length = n` using `by simpa using hcard`.

Substitute `hl'` using the available equality. Use `⟨l.get, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map, List.ofFn_get]`. Both sides reduce to the same expression. Establish `hne : ∀ i, α i ≠ 0` using `fun i e => h0 (by`.

Rewrite using `[← hα]`. Conclude with `Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)`. Take `⟨φ, hφ, h1, -⟩` from `Final.SphericalExists E P n α hne`. Take `⟨ϖ, hϖ⟩` from `exists_isUnifV E P`. Establish `hO : ϖ ∈ Ov E P` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by`.

Unfold `IsUnifV at hϖ`. Rewrite using `[hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]`. Use the proof step `omega)`. Establish `h2` using `hpar α hα φ hφ _ hl`. Rewrite `h2` using `[divInd_dualLab_splitLab E P n k hϖ, Final.SatakeTj E P n ϖ hO hϖ α hne φ hφ k hk, hα]`.

Simplify `h2.symm` using `[h1]`.
-/
theorem parGL_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) (k : ℕ) (hs : ParGL P n lab c s) (hk : k ≤ n)
    (hl : lab (dualLab (splitLab n k))) :
    c (dualLab (splitLab n k)) = (qV E P : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) * s.esymm k := by
  obtain ⟨hcard, h0, hpar⟩ := hs
  obtain ⟨α, hα⟩ : ∃ α : Fin n → ℂ, Finset.univ.val.map α = s := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl' : l.length = n := by simpa using hcard
      subst hl'
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have hne : ∀ i, α i ≠ 0 := fun i e => h0 (by
    rw [← hα]; exact Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E P n α hne
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E P
  have hO : ϖ ∈ Ov E P := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
    unfold IsUnifV at hϖ
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega)
  have h2 := hpar α hα φ hφ _ hl
  rw [divInd_dualLab_splitLab E P n k hϖ, Final.SatakeTj E P n ϖ hO hϖ α hne φ hφ k hk, hα] at h2
  simpa [h1] using h2.symm

end GlobalTheory.SphPar
