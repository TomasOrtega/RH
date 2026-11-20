import ReciprocityTheory.SemistableReduction.SemiContractB
import ReciprocityTheory.SemistableReduction.SemiContractC

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

/- English proof (translation)
Introduce `K _ _ r S L hLat hSD`. Take `⟨M, hM⟩` from `hP K r S L hLat hSD`. Use `⟨M, hM, fun N hNL hN => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hN0`. Take `⟨b, hbL, hbN, hbli, hker⟩` from `sc_kerfam L hLat.2 N`.

Take `⟨c, hcL, hcli⟩` from `sc_imfam L hLat.2 N`. Establish `hm` using `sc_rank_pos N hN0`. Establish `hli` using `sc_append_li N b c hbN hbli hcli`. Establish `hkm : finrank K (LinearMap.ker N.mulVecLin) + finrank K (LinearMap.range N.mulVecLin) = r`. Use `LinearMap.finrank_range_add_finrank_ker N.mulVecLin` as an intermediate fact.

Rewrite `this` using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Establish `hspan : Submodule.span K (Set.range (Fin.append b c)) = ⊤` using `hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_fin_fun, hkm])`. Establish `happL : ∀ i, Fin.append b c i ∈ L`. Introduce `i`.

Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => rw [Fin.append_left]`. Conclude with `hbL i`. Consider the case `right j => rw [Fin.append_right]`. Conclude with `hcL j`.

Establish `hspanL : ∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c))`. Introduce `x _`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Establish `hdegL` using `hM.1 _ (Fin.append b c) ⟨happL, hli, hspanL⟩`.

Establish `hdegK` using `hM.2 (satSub L b) inf_le_left _ b ⟨fun i => ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩, hbli, fun x hx => hx.2⟩`. Establish `hadd` using `hD K r _ _ M.H L b c M.posDef hLat.1 hbL hcL hli hspanL`. Use `set NL := L.map (N.mulVecLin.restrictScalars (𝓞 K)) with hNLdef`. Establish `hNLle : NL ≤ L`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `hNL x hx`. Establish `hNspan : ∀ y, N *ᵥ y ∈ Submodule.span K (Set.range fun j => N *ᵥ c j)`. Introduce `y`. Establish `hy : y ∈ Submodule.span K (Set.range (Fin.append b c))`. Rewrite using `[hspan]`.

Conclude with `Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Proceed by induction on `i using Fin.addCases with`.

Consider the case `left i => rw [Fin.append_left, hbN i]`. Conclude with `Submodule.zero_mem _`. Consider the case `right j => rw [Fin.append_right]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Consider the case `zero => rw [mulVec_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [mulVec_smul]`. Conclude with `Submodule.smul_mem _ a hx`.

Establish `hdegN` using `hM.2 NL hNLle _ (fun j => N *ᵥ c j) ⟨fun j => ⟨c j, hcL j, rfl⟩, hcli, by rintro _ ⟨x, _, rfl⟩; exact hNspan x⟩`. Establish `hidx` using `sc_index L N b c hcL hbN hker`. Establish `hσ` using `fun σ => sc_gram_lt hm (M.H σ) (M.posDef σ) σ N (hN σ) b c hli hbN hcli`. Establish `hsum : ∑ σ : K →+* ℂ, Real.log (gramC (M.H σ) σ fun j => N *ᵥ c j).det.re < ∑ σ : K →+* ℂ, Real.log (quotGramC (M.H σ) σ b c).det.re` using `Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun σ _ => Real.log_lt_log (hσ σ).1 (hσ σ).2`. Establish `hlt : quotDeg M.H L b c < latDeg M.H NL (fun j => N *ᵥ c j)`.

Rewrite using `[quotDeg, latDeg, ← hidx]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem semiContract_holds (hP : SemiPointStatement) (hD : DegAddStatement) :
    SemistableStatement := by
  intro K _ _ r S L hLat hSD
  obtain ⟨M, hM⟩ := hP K r S L hLat hSD
  refine ⟨M, hM, fun N hNL hN => ?_⟩
  by_contra hN0
  obtain ⟨b, hbL, hbN, hbli, hker⟩ := sc_kerfam L hLat.2 N
  obtain ⟨c, hcL, hcli⟩ := sc_imfam L hLat.2 N
  have hm := sc_rank_pos N hN0
  have hli := sc_append_li N b c hbN hbli hcli
  have hkm : finrank K (LinearMap.ker N.mulVecLin) + finrank K (LinearMap.range N.mulVecLin) = r := by
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at this
    omega
  have hspan : Submodule.span K (Set.range (Fin.append b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_fin_fun, hkm])
  have happL : ∀ i, Fin.append b c i ∈ L := by
    intro i
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hbL i
    | right j => rw [Fin.append_right]; exact hcL j
  have hspanL : ∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c)) := by
    intro x _; rw [hspan]; exact Submodule.mem_top

  have hdegL := hM.1 _ (Fin.append b c) ⟨happL, hli, hspanL⟩
  have hdegK := hM.2 (satSub L b) inf_le_left _ b
    ⟨fun i => ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩, hbli, fun x hx => hx.2⟩
  have hadd := hD K r _ _ M.H L b c M.posDef hLat.1 hbL hcL hli hspanL

  set NL := L.map (N.mulVecLin.restrictScalars (𝓞 K)) with hNLdef
  have hNLle : NL ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNL x hx
  have hNspan : ∀ y, N *ᵥ y ∈ Submodule.span K (Set.range fun j => N *ᵥ c j) := by
    intro y
    have hy : y ∈ Submodule.span K (Set.range (Fin.append b c)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction i using Fin.addCases with
      | left i => rw [Fin.append_left, hbN i]; exact Submodule.zero_mem _
      | right j => rw [Fin.append_right]; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx
  have hdegN := hM.2 NL hNLle _ (fun j => N *ᵥ c j)
    ⟨fun j => ⟨c j, hcL j, rfl⟩, hcli, by rintro _ ⟨x, _, rfl⟩; exact hNspan x⟩

  have hidx := sc_index L N b c hcL hbN hker
  have hσ := fun σ => sc_gram_lt hm (M.H σ) (M.posDef σ) σ N (hN σ) b c hli hbN hcli
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramC (M.H σ) σ fun j => N *ᵥ c j).det.re <
      ∑ σ : K →+* ℂ, Real.log (quotGramC (M.H σ) σ b c).det.re :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun σ _ =>
      Real.log_lt_log (hσ σ).1 (hσ σ).2
  have hlt : quotDeg M.H L b c < latDeg M.H NL (fun j => N *ᵥ c j) := by
    rw [quotDeg, latDeg, ← hidx]
    linarith
  linarith

end ReciprocityTheory.MultiplicativeHeights
