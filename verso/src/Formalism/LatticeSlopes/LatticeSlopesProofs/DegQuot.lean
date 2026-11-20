import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram

open Module Submodule

noncomputable section

namespace Formalism.F

/- English proof (translation)
Establish `hs : Submodule.span ℤ (Set.range fun i => (b i : E)) = L`. Establish `h1 : (Set.range fun i => (b i : E)) = L.subtype '' Set.range b` using `Set.range_comp L.subtype b`. Rewrite using `[h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hd : DiscreteTopology (Submodule.span ℤ (Set.range fun i => (b i : E)))`. Rewrite using `[hs]`.

Use `infer_instance`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hd]`. Unfold `Set.finrank`. Rewrite using `[hs, Module.finrank_eq_card_basis b]`.
-/
theorem linearIndependent_coe_basis''' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical
  have hs : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 : (Set.range fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp L.subtype b
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range fun i => (b i : E))) := by
    rw [hs]; infer_instance
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hd]
  unfold Set.finrank
  rw [hs, Module.finrank_eq_card_basis b]

/- English proof (translation)
Set `φ : (ι → ℝ) →ₗ[ℝ] E` to `Fintype.linearCombination ℝ c`. Establish `hker : LinearMap.ker φ = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `r hr`. Use function extensionality and compare the values at `i`.

Conclude with `Fintype.linearIndependent_iff.1 hc r (by rw [← Fintype.linearCombination_apply]; exact hr) i`. Take `⟨K, hK, hφ⟩` from `LinearMap.exists_antilipschitzWith φ hker`. Establish `hKpos : (0 : ℝ) < K` using `by exact_mod_cast hK`. Establish `key : ∀ x ∈ Submodule.span ℤ (Set.range c), x ≠ 0 → (K : ℝ)⁻¹ ≤ ‖x‖`. Introduce `x hx hx0`.

Take `⟨n, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hx`. Establish `hφn : φ (fun i => (n i : ℝ)) = ∑ i, n i • c i`. Simplify using `only [φ, Fintype.linearCombination_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ (n i) (c i)`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, n i ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hx0` to reduce the goal to its premises. Simplify using `[hcon]`. Establish `h1 : (1 : ℝ) ≤ ‖(fun i => (n i : ℝ))‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `hφ.le_mul_dist (fun i => (n i : ℝ)) 0`. Rewrite `h2` using `[dist_zero_right, map_zero, dist_zero_right, hφn]`. Rewrite using `[inv_eq_one_div, div_le_iff₀ hKpos]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hε : (0 : ℝ) < (K : ℝ)⁻¹` using `inv_pos.mpr hKpos`. Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Use `isOpen_induced_iff.mpr ⟨Metric.ball 0 (K : ℝ)⁻¹, Metric.isOpen_ball, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`. Establish `hy : (y : E) ≠ 0` using `fun h0 => hne (Subtype.ext h0)`. Conclude with `absurd (key y y.2 hy) (not_le.mpr h)`.

Introduce `h`. Rewrite using `[h]`. Simplify using `using hε`.
-/
theorem discreteTopology_span_range_of_linearIndependent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : LinearIndependent ℝ c) :
    DiscreteTopology (span ℤ (Set.range c)) := by
  classical
  let φ : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ c
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro r hr
    funext i
    exact Fintype.linearIndependent_iff.1 hc r
      (by rw [← Fintype.linearCombination_apply]; exact hr) i
  obtain ⟨K, hK, hφ⟩ := LinearMap.exists_antilipschitzWith φ hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ x ∈ Submodule.span ℤ (Set.range c), x ≠ 0 → (K : ℝ)⁻¹ ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    have hφn : φ (fun i => (n i : ℝ)) = ∑ i, n i • c i := by
      simp only [φ, Fintype.linearCombination_apply]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ (n i) (c i)
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hx0
      simp [hcon]
    have h1 : (1 : ℝ) ≤ ‖(fun i => (n i : ℝ))‖ := by
      calc (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
        _ = ‖(n i : ℝ)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖(fun i => (n i : ℝ))‖ := norm_le_pi_norm (fun i => (n i : ℝ)) i
    have h2 := hφ.le_mul_dist (fun i => (n i : ℝ)) 0
    rw [dist_zero_right, map_zero, dist_zero_right, hφn] at h2
    rw [inv_eq_one_div, div_le_iff₀ hKpos]
    nlinarith
  have hε : (0 : ℝ) < (K : ℝ)⁻¹ := inv_pos.mpr hKpos
  apply discreteTopology_of_isOpen_singleton_zero
  refine isOpen_induced_iff.mpr ⟨Metric.ball 0 (K : ℝ)⁻¹, Metric.isOpen_ball, ?_⟩
  ext y
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hy : (y : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    exact absurd (key y y.2 hy) (not_le.mpr h)
  · intro h
    rw [h]
    simpa using hε

/- English proof (translation)
Establish `h1 : (Set.range fun i => (b i : E)) = L.subtype '' Set.range b` using `Set.range_comp L.subtype b`. Rewrite using `[h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem span_range_coe_basis' {E : Type*} [AddCommGroup E] (L : Submodule ℤ E) {ι : Type*}
    (b : Basis ι ℤ L) : span ℤ (Set.range (fun i => (b i : E))) = L := by
  have h1 : (Set.range fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp L.subtype b
  rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `E _ _ _ L N hL hsat`. Take `⟨hNL, hsat'⟩` from `hsat`. Use `haveI := hL`. Use `haveI : DiscreteTopology N := discreteTopology_of_le hNL`. Set `W : Submodule ℝ E` to `Submodule.span ℝ (N : Set E)`.

Set `P : E →L[ℝ] E` to `Wᗮ.starProjection`. Establish `hPmem : ∀ x : E, P x ∈ Wᗮ` using `fun x => by show Wᗮ.starProjection x ∈ Wᗮ`. Rewrite using `[Submodule.starProjection_apply]`. Conclude with `Submodule.coe_mem _`. Establish `hPsub : ∀ x : E, x - P x ∈ W` using `fun x => by`.

Establish `h` using `Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x`. Rewrite `h` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `horth : ∀ u ∈ W, ∀ w ∈ Wᗮ, inner ℝ u w = 0`. Introduce `u hu w hw`. Use `first`.

Consider the case `exact (Submodule.mem_orthogonal W w).1 hw u hu`. Consider the case `exact (Submodule.mem_orthogonal w).1 hw u hu`. Consider the case `exact Submodule.inner_right_of_mem_orthogonal hu hw`. Establish `hPW : ∀ x ∈ W, P x = 0`. Introduce `x hx`.

Establish `h2 : P x ∈ W`. Establish `h` using `W.sub_mem hx (hPsub x)`. Rewrite `h` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Conclude with `inner_self_eq_zero.mp (horth _ h2 _ (hPmem x))`. Establish `hNW : ∀ x ∈ N, x ∈ W` using `fun x hx => Submodule.subset_span hx`.

Establish `hker : ∀ x ∈ L, P x = 0 → x ∈ N`. Introduce `x hx h0`. Apply `hsat' x hx` to reduce the goal to its premises. Establish `h` using `hPsub x`. Rewrite `h` using `[h0, sub_zero]`. Then use the resulting hypothesis.

Use `set Q := quot L N with hQdef`. Establish `hQmem : ∀ y : E, y ∈ Q ↔ ∃ x ∈ L, P x = y`. Introduce `y`. Use `show y ∈ L.map _ ↔ _`. Rewrite using `[Submodule.mem_map]`.

Both sides reduce to the same expression. Use `haveI : Module.Finite ℤ Q := by show Module.Finite ℤ (L.map _) first`. Consider the case `exact Module.Finite.map L _`. Consider the case `exact Module.Finite.iff_fg.mpr (Submodule.FG.map _ (Module.Finite.iff_fg.mp inferInstance))`. Use `haveI : Module.IsTorsionFree ℤ Q := Module.IsTorsionFree.mk fun r hr x y hxy => by`.

Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h : ((r • x : Q) : E) = ((r • y : Q) : E)` using `congrArg Subtype.val hxy`. Rewrite `h` using `[Submodule.coe_smul, Submodule.coe_smul]`. Establish `h' : (r : ℝ) • (x : E) = (r : ℝ) • (y : E)`.

Rewrite using `[Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]`. Conclude with `h`. Conclude with `smul_right_injective E (Int.cast_ne_zero.mpr hr0) h'`. Use `haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'`. Set `eQ` to `Module.Free.chooseBasis ℤ Q`.

Set `bN` to `Module.Free.chooseBasis ℤ N`. Establish `hlift : ∀ j, ∃ x ∈ L, P x = (eQ j : E)` using `fun j => (hQmem _).1 (eQ j).2`. Use `choose ℓ hℓL hℓP using hlift`. Set `v : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → L` to `Sum.elim (fun i => ⟨(bN i : E), hNL (bN i).2⟩) (fun j => ⟨ℓ j, hℓL j⟩)`. Establish `hvE : ∀ k, ((v k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k`.

Introduce `k`. Apply the tactic sequence `cases k <;> rfl`. Establish `hli : LinearIndependent ℤ v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`.

Establish `hgE : ∑ i, g (Sum.inl i) • (bN i : E) + ∑ j, g (Sum.inr j) • ℓ j = 0`. Establish `h` using `congrArg (fun z : L => (z : E)) hg`. Simplify `h` using `[Fintype.sum_sum_type, v]`. Establish `hPg : ∑ j, g (Sum.inr j) • (eQ j : E) = 0`. Establish `h` using `congrArg P hgE`.

Establish `h1 : ∀ i, P (g (Sum.inl i) • (bN i : E)) = 0` using `fun i => by`. Rewrite using `[map_zsmul, hPW _ (hNW _ (bN i).2), smul_zero]`. Establish `h2 : ∀ j, P (g (Sum.inr j) • ℓ j) = g (Sum.inr j) • (eQ j : E)` using `fun j => by`. Rewrite using `[map_zsmul, hℓP]`. Rewrite `h` using `[map_add, map_sum, map_sum, map_zero, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const_zero, zero_add, Finset.sum_congr rfl (fun j _ => h2 j)]`.

Conclude with `h`. Establish `hQz : ∀ j, g (Sum.inr j) = 0`. Establish `h : ∑ j, g (Sum.inr j) • eQ j = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hPg`.

Conclude with `Fintype.linearIndependent_iff.1 eQ.linearIndependent _ h`. Establish `hNz : ∀ i, g (Sum.inl i) = 0`. Establish `h0 : ∑ i, g (Sum.inl i) • (bN i : E) = 0`. Establish `h` using `hgE`. Simplify using `only [hQz, zero_smul, Finset.sum_const_zero, add_zero] at h`.

Conclude with `h`. Establish `h : ∑ i, g (Sum.inl i) • bN i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h0`. Conclude with `Fintype.linearIndependent_iff.1 bN.linearIndependent _ h`.

Introduce `k`. Consider the cases of `k with`. Consider the case `inl i => exact hNz i`. Consider the case `inr j => exact hQz j`. Establish `hsp : ⊤ ≤ Submodule.span ℤ (Set.range v)`.

Introduce and unpack `⟨x, hx⟩ -`. Establish `hPx : P x ∈ Q` using `(hQmem _).2 ⟨x, hx, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : Module.Free.ChooseBasisIndex ℤ Q → ℤ, ∑ j, r j • (eQ j : E) = P x := by`. Establish `h2` using `congrArg (fun z : Q => (z : E)) (eQ.sum_repr ⟨P x, hPx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h2`.

Conclude with `⟨_, h2⟩`. Establish `hy : x - ∑ j, r j • ℓ j ∈ N`. Apply `hker` to reduce the goal to its premises. Conclude with `L.sub_mem hx (L.sum_mem fun j _ => L.smul_mem _ (hℓL j))`. Rewrite using `[map_sub, map_sum, ← hr]`.

Simplify using `only [map_zsmul, hℓP]`. Conclude with `sub_self _`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : Module.Free.ChooseBasisIndex ℤ N → ℤ, ∑ i, s i • (bN i : E) = x - ∑ j, r j • ℓ j := by`. Establish `h2` using `congrArg (fun z : N => (z : E)) (bN.sum_repr ⟨_, hy⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h2`.

Conclude with `⟨_, h2⟩`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨Sum.elim s r, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, v, Submodule.coe_mk]`.

Rewrite using `[hs]`. Normalize the expressions using the abelian group laws. Set `cB` to `Module.Basis.mk hli hsp`. Establish `hcB : ∀ k, ((cB k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k`. Introduce `k`.

Rewrite using `[Module.Basis.mk_apply]`. Conclude with `hvE k`. Establish `hindR : LinearIndependent ℝ (Sum.elim (fun i => (bN i : E)) ℓ)`. Establish `h` using `linearIndependent_coe_basis''' L cB`. Establish `he : (fun k => ((cB k : L) : E)) = Sum.elim (fun i => (bN i : E)) ℓ` using `funext hcB`.

Rewrite `h` using `[he]`. Then use the resulting hypothesis. Establish `hWspan : W = Submodule.span ℝ (Set.range fun i => (bN i : E))` using `by show Submodule.span ℝ (N : Set E) = _`. Rewrite using `[← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (bN i : E)), span_range_coe_basis' N bN]`. Establish `heQW : ∀ j, (eQ j : E) ∈ Wᗮ` using `fun j => by`. Rewrite using `[← hℓP j]`.

Conclude with `hPmem _`. Establish `heQ : LinearIndependent ℝ (fun j => (eQ j : E))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Establish `hmem : ∑ j, a j • ℓ j ∈ W`.

Establish `h1 : P (∑ j, a j • ℓ j) = 0`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, hℓP]`. Conclude with `ha`. Establish `h` using `hPsub (∑ j, a j • ℓ j)`.

Rewrite `h` using `[h1, sub_zero]`. Then use the resulting hypothesis. Rewrite `hmem` using `[hWspan, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨β, hβ⟩` from `hmem`. Establish `hrel : ∑ k, (Sum.elim (fun i => -β i) a k) • Sum.elim (fun i => (bN i : E)) ℓ k = 0`. Rewrite using `[Fintype.sum_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[hβ]`. Conclude with `neg_add_cancel _`. Introduce `j`. Conclude with `Fintype.linearIndependent_iff.1 hindR _ hrel (Sum.inr j)`.

Use `haveI hQd : DiscreteTopology Q := by`. Establish `h` using `discreteTopology_span_range_of_linearIndependent (fun j => (eQ j : E)) heQ`. Rewrite `h` using `[span_range_coe_basis' Q eQ]`. Then use the resulting hypothesis. Establish `hrk : rk L = rk N + rk Q`. Unfold `rk`.

Rewrite using `[Module.finrank_eq_card_basis cB, Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis eQ, Fintype.card_sum]`. Establish `hα : ∀ j, ∃ α : Module.Free.ChooseBasisIndex ℤ N → ℝ, ∑ i, α i • (bN i : E) = ℓ j - (eQ j : E)`. Introduce `j`. Establish `h` using `hPsub (ℓ j)`. Rewrite `h` using `[hℓP, hWspan, Submodule.mem_span_range_iff_exists_fun]`.

Conclude with `h`. Use `choose α hα using hα`. Set `v2 : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → E` to `Sum.elim (fun i => (bN i : E)) (fun j => (eQ j : E))`. Set `M : Matrix (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q) (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q) ℝ` to `Matrix.fromBlocks 1 (Matrix.of fun i j => α j i) 0 1`. Establish `hcomb : (fun k => ((cB k : L) : E)) = fun k => ∑ k', M k' k • v2 k'`.

Use function extensionality and compare the values at `k`. Rewrite using `[hcB, Fintype.sum_sum_type]`. Consider the cases of `k with`. Consider the case `inl i0`. Simplify using `only [M, v2, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Consider the case `inr j0`. Simplify using `only [M, v2, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[hα, sub_add_cancel]`. Establish `hdetM : M.det = 1`. Simplify using `only [M]`.

Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]`. Establish `hgram : Matrix.gram ℝ v2 = Matrix.fromBlocks (Matrix.gram ℝ fun i => (bN i : E)) 0 0 (Matrix.gram ℝ fun j => (eQ j : E))`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with i | j <;> rcases b with i' | j' <;>`. Simplify using `only [Matrix.gram_apply, v2, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]`.

Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `exact horth _ (hNW _ (bN i).2) _ (heQW j')`. Consider the case `(rw [real_inner_comm]; exact horth _ (hNW _ (bN i').2) _ (heQW j))`. Establish `hdet : (Matrix.gram ℝ fun k => ((cB k : L) : E)).det = (Matrix.gram ℝ fun i => (bN i : E)).det * (Matrix.gram ℝ fun j => (eQ j : E)).det`.

Rewrite using `[hcomb, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetM, hgram, Matrix.det_fromBlocks_zero₂₁]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcovL : covol L = Real.sqrt (Matrix.gram ℝ fun k => ((cB k : L) : E)).det` using `covol_eq_gram E L _ cB`. Establish `hcovN : covol N = Real.sqrt (Matrix.gram ℝ fun i => (bN i : E)).det` using `covol_eq_gram E N _ bN`. Establish `hcovQ : covol Q = Real.sqrt (Matrix.gram ℝ fun j => (eQ j : E)).det` using `covol_eq_gram E Q _ eQ`.

Establish `hposN : 0 < (Matrix.gram ℝ fun i => (bN i : E)).det` using `(Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis''' N bN)).det_pos`. Establish `hposQ : 0 < (Matrix.gram ℝ fun j => (eQ j : E)).det` using `(Matrix.posDef_gram_of_linearIndependent heQ).det_pos`. Use `⟨hQd, hrk, ?_⟩` and prove the remaining obligations. Unfold `deg`. Rewrite using `[hcovL, hcovN, hcovQ, hdet, Real.sqrt_mul hposN.le, Real.log_mul (Real.sqrt_pos.2 hposN).ne' (Real.sqrt_pos.2 hposQ).ne']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem degree_quotient : DegQuot := by
  intro E _ _ _ L N hL hsat
  classical
  obtain ⟨hNL, hsat'⟩ := hsat
  haveI := hL
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  let W : Submodule ℝ E := Submodule.span ℝ (N : Set E)
  let P : E →L[ℝ] E := Wᗮ.starProjection
  have hPmem : ∀ x : E, P x ∈ Wᗮ := fun x => by
    show Wᗮ.starProjection x ∈ Wᗮ
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  have hPsub : ∀ x : E, x - P x ∈ W := fun x => by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at h
  have horth : ∀ u ∈ W, ∀ w ∈ Wᗮ, inner ℝ u w = 0 := by
    intro u hu w hw
    first
      | exact (Submodule.mem_orthogonal W w).1 hw u hu
      | exact (Submodule.mem_orthogonal w).1 hw u hu
      | exact Submodule.inner_right_of_mem_orthogonal hu hw
  have hPW : ∀ x ∈ W, P x = 0 := by
    intro x hx
    have h2 : P x ∈ W := by
      have h := W.sub_mem hx (hPsub x)
      rwa [sub_sub_cancel] at h
    exact inner_self_eq_zero.mp (horth _ h2 _ (hPmem x))
  have hNW : ∀ x ∈ N, x ∈ W := fun x hx => Submodule.subset_span hx
  have hker : ∀ x ∈ L, P x = 0 → x ∈ N := by
    intro x hx h0
    apply hsat' x hx
    have h := hPsub x
    rwa [h0, sub_zero] at h
  set Q := quot L N with hQdef
  have hQmem : ∀ y : E, y ∈ Q ↔ ∃ x ∈ L, P x = y := by
    intro y
    show y ∈ L.map _ ↔ _
    rw [Submodule.mem_map]
    rfl
  haveI : Module.Finite ℤ Q := by
    show Module.Finite ℤ (L.map _)
    first
      | exact Module.Finite.map L _
      | exact Module.Finite.iff_fg.mpr (Submodule.FG.map _ (Module.Finite.iff_fg.mp inferInstance))
  haveI : Module.IsTorsionFree ℤ Q := Module.IsTorsionFree.mk fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    apply Subtype.ext
    have h : ((r • x : Q) : E) = ((r • y : Q) : E) := congrArg Subtype.val hxy
    rw [Submodule.coe_smul, Submodule.coe_smul] at h
    have h' : (r : ℝ) • (x : E) = (r : ℝ) • (y : E) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact h
    exact smul_right_injective E (Int.cast_ne_zero.mpr hr0) h'
  haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let eQ := Module.Free.chooseBasis ℤ Q
  let bN := Module.Free.chooseBasis ℤ N
  have hlift : ∀ j, ∃ x ∈ L, P x = (eQ j : E) := fun j => (hQmem _).1 (eQ j).2
  choose ℓ hℓL hℓP using hlift
  let v : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → L :=
    Sum.elim (fun i => ⟨(bN i : E), hNL (bN i).2⟩) (fun j => ⟨ℓ j, hℓL j⟩)
  have hvE : ∀ k, ((v k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k := by
    intro k
    cases k <;> rfl
  have hli : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgE : ∑ i, g (Sum.inl i) • (bN i : E) + ∑ j, g (Sum.inr j) • ℓ j = 0 := by
      have h := congrArg (fun z : L => (z : E)) hg
      simpa [Fintype.sum_sum_type, v] using h
    have hPg : ∑ j, g (Sum.inr j) • (eQ j : E) = 0 := by
      have h := congrArg P hgE
      have h1 : ∀ i, P (g (Sum.inl i) • (bN i : E)) = 0 := fun i => by
        rw [map_zsmul, hPW _ (hNW _ (bN i).2), smul_zero]
      have h2 : ∀ j, P (g (Sum.inr j) • ℓ j) = g (Sum.inr j) • (eQ j : E) := fun j => by
        rw [map_zsmul, hℓP]
      rw [map_add, map_sum, map_sum, map_zero, Finset.sum_congr rfl (fun i _ => h1 i),
        Finset.sum_const_zero, zero_add, Finset.sum_congr rfl (fun j _ => h2 j)] at h
      exact h
    have hQz : ∀ j, g (Sum.inr j) = 0 := by
      have h : ∑ j, g (Sum.inr j) • eQ j = 0 := by
        apply Subtype.ext
        simpa using hPg
      exact Fintype.linearIndependent_iff.1 eQ.linearIndependent _ h
    have hNz : ∀ i, g (Sum.inl i) = 0 := by
      have h0 : ∑ i, g (Sum.inl i) • (bN i : E) = 0 := by
        have h := hgE
        simp only [hQz, zero_smul, Finset.sum_const_zero, add_zero] at h
        exact h
      have h : ∑ i, g (Sum.inl i) • bN i = 0 := by
        apply Subtype.ext
        simpa using h0
      exact Fintype.linearIndependent_iff.1 bN.linearIndependent _ h
    intro k
    cases k with
    | inl i => exact hNz i
    | inr j => exact hQz j
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    have hPx : P x ∈ Q := (hQmem _).2 ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r : Module.Free.ChooseBasisIndex ℤ Q → ℤ,
        ∑ j, r j • (eQ j : E) = P x := by
      have h2 := congrArg (fun z : Q => (z : E)) (eQ.sum_repr ⟨P x, hPx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact ⟨_, h2⟩
    have hy : x - ∑ j, r j • ℓ j ∈ N := by
      apply hker
      · exact L.sub_mem hx (L.sum_mem fun j _ => L.smul_mem _ (hℓL j))
      · rw [map_sub, map_sum, ← hr]
        simp only [map_zsmul, hℓP]
        exact sub_self _
    obtain ⟨s, hs⟩ : ∃ s : Module.Free.ChooseBasisIndex ℤ N → ℤ,
        ∑ i, s i • (bN i : E) = x - ∑ j, r j • ℓ j := by
      have h2 := congrArg (fun z : N => (z : E)) (bN.sum_repr ⟨_, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact ⟨_, h2⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨Sum.elim s r, ?_⟩
    apply Subtype.ext
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Submodule.coe_add,
      Submodule.coe_sum, Submodule.coe_smul, v, Submodule.coe_mk]
    rw [hs]
    abel
  let cB := Module.Basis.mk hli hsp
  have hcB : ∀ k, ((cB k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k := by
    intro k
    rw [Module.Basis.mk_apply]
    exact hvE k
  have hindR : LinearIndependent ℝ (Sum.elim (fun i => (bN i : E)) ℓ) := by
    have h := linearIndependent_coe_basis''' L cB
    have he : (fun k => ((cB k : L) : E)) = Sum.elim (fun i => (bN i : E)) ℓ := funext hcB
    rwa [he] at h
  have hWspan : W = Submodule.span ℝ (Set.range fun i => (bN i : E)) := by
    show Submodule.span ℝ (N : Set E) = _
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (bN i : E)),
      span_range_coe_basis' N bN]
  have heQW : ∀ j, (eQ j : E) ∈ Wᗮ := fun j => by
    rw [← hℓP j]
    exact hPmem _
  have heQ : LinearIndependent ℝ (fun j => (eQ j : E)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hmem : ∑ j, a j • ℓ j ∈ W := by
      have h1 : P (∑ j, a j • ℓ j) = 0 := by
        rw [map_sum]
        simp only [map_smul, hℓP]
        exact ha
      have h := hPsub (∑ j, a j • ℓ j)
      rwa [h1, sub_zero] at h
    rw [hWspan, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨β, hβ⟩ := hmem
    have hrel : ∑ k, (Sum.elim (fun i => -β i) a k) • Sum.elim (fun i => (bN i : E)) ℓ k = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
      rw [hβ]
      exact neg_add_cancel _
    intro j
    exact Fintype.linearIndependent_iff.1 hindR _ hrel (Sum.inr j)
  haveI hQd : DiscreteTopology Q := by
    have h := discreteTopology_span_range_of_linearIndependent (fun j => (eQ j : E)) heQ
    rwa [span_range_coe_basis' Q eQ] at h
  have hrk : rk L = rk N + rk Q := by
    unfold rk
    rw [Module.finrank_eq_card_basis cB, Module.finrank_eq_card_basis bN,
      Module.finrank_eq_card_basis eQ, Fintype.card_sum]
  have hα : ∀ j, ∃ α : Module.Free.ChooseBasisIndex ℤ N → ℝ,
      ∑ i, α i • (bN i : E) = ℓ j - (eQ j : E) := by
    intro j
    have h := hPsub (ℓ j)
    rw [hℓP, hWspan, Submodule.mem_span_range_iff_exists_fun] at h
    exact h
  choose α hα using hα
  let v2 : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → E :=
    Sum.elim (fun i => (bN i : E)) (fun j => (eQ j : E))
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q)
      (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q) ℝ :=
    Matrix.fromBlocks 1 (Matrix.of fun i j => α j i) 0 1
  have hcomb : (fun k => ((cB k : L) : E)) = fun k => ∑ k', M k' k • v2 k' := by
    funext k
    rw [hcB, Fintype.sum_sum_type]
    cases k with
    | inl i0 =>
      simp only [M, v2, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Sum.elim_inl,
        Sum.elim_inr, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
        Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    | inr j0 =>
      simp only [M, v2, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Sum.elim_inl,
        Sum.elim_inr, Matrix.of_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hα, sub_add_cancel]
  have hdetM : M.det = 1 := by
    simp only [M]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
  have hgram : Matrix.gram ℝ v2 = Matrix.fromBlocks (Matrix.gram ℝ fun i => (bN i : E)) 0 0
      (Matrix.gram ℝ fun j => (eQ j : E)) := by
    ext a b
    rcases a with i | j <;> rcases b with i' | j' <;>
      simp only [Matrix.gram_apply, v2, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
    all_goals first
      | rfl
      | exact horth _ (hNW _ (bN i).2) _ (heQW j')
      | (rw [real_inner_comm]; exact horth _ (hNW _ (bN i').2) _ (heQW j))
  have hdet : (Matrix.gram ℝ fun k => ((cB k : L) : E)).det =
      (Matrix.gram ℝ fun i => (bN i : E)).det * (Matrix.gram ℝ fun j => (eQ j : E)).det := by
    rw [hcomb, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      hdetM, hgram, Matrix.det_fromBlocks_zero₂₁]
    ring
  have hcovL : covol L = Real.sqrt (Matrix.gram ℝ fun k => ((cB k : L) : E)).det :=
    covol_eq_gram E L _ cB
  have hcovN : covol N = Real.sqrt (Matrix.gram ℝ fun i => (bN i : E)).det :=
    covol_eq_gram E N _ bN
  have hcovQ : covol Q = Real.sqrt (Matrix.gram ℝ fun j => (eQ j : E)).det :=
    covol_eq_gram E Q _ eQ
  have hposN : 0 < (Matrix.gram ℝ fun i => (bN i : E)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis''' N bN)).det_pos
  have hposQ : 0 < (Matrix.gram ℝ fun j => (eQ j : E)).det :=
    (Matrix.posDef_gram_of_linearIndependent heQ).det_pos
  refine ⟨hQd, hrk, ?_⟩
  unfold deg
  rw [hcovL, hcovN, hcovQ, hdet, Real.sqrt_mul hposN.le,
    Real.log_mul (Real.sqrt_pos.2 hposN).ne' (Real.sqrt_pos.2 hposQ).ne']
  ring

end Formalism.F
