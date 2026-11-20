import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidtStatement

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.admitted

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

/- English proof (translation)
Set `t : Set H` to `Set.range fun k : KG ε => σ (toMK k) u`. Take `⟨b, hbt, hsp, hli⟩` from `exists_linearIndependent ℂ t`. Establish `hfin : b.Finite`. Assume the negation of the conclusion as `hinf`. Use `haveI : Infinite b := Set.infinite_coe_iff.2 hinf`.

Set `e : Fin (M + 1) ↪ b` to `Fin.valEmbedding.trans (Infinite.natEmbedding b)`. Use `choose k hk using fun i => hbt (e i).2`. Establish `hc : Continuous fun w : H => fun i : Fin (M + 1) => σ (toMK (k i)) w` using `continuous_pi fun i => (σ _).continuous`. Establish `ho` using `(isOpen_setOf_linearIndependent (𝕜 := ℂ) (E := H) (ι := Fin (M + 1))).preimage hc`. Establish `hu' : LinearIndependent ℂ fun i : Fin (M + 1) => σ (toMK (k i)) u`.

Use `hli.comp e e.injective` as an intermediate fact. Rewrite `this` using `[show (Subtype.val ∘ e : Fin (M + 1) → H) = _ from funext fun i => (hk i).symm]`. Then use the resulting hypothesis. Take `⟨w, hw, hwU⟩` from `mem_closure_iff.1 hu _ ho hu'`. Take `⟨S, hS, hM, hwS, hK⟩` from `hU w hwU`. Establish `h1 : LinearIndependent ℂ fun i : Fin (M + 1) => (⟨σ (toMK (k i)) w, hK _ (toMK_mem_K _) w hwS⟩ : S)` using `LinearIndependent.of_comp S.subtype hw`.

Establish `h2` using `h1.fintype_card_le_finrank`. Rewrite `h2` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Use `⟨Submodule.span ℂ t, hsp ▸ FiniteDimensional.span_of_finite ℂ hfin, Submodule.subset_span ⟨1, ?_⟩, fun g hg v hv => ?_⟩` and prove the remaining obligations. Conclude with `sigma_one hσ u`.

Use `(Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨g', rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k)` from `by rw [range_toMK]; exact hg`. Conclude with `Submodule.subset_span ⟨g' * k, sigma_mul hσ (K_le_UJ hg) (K_le_UJ (toMK_mem_K k)) u⟩`.
-/
theorem isKFin_of_mem_closure (hσ : IsURepOn (UJset ε) σ) {U : Set H} {M : ℕ}
    (hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S)
    {u : H} (hu : u ∈ closure U) : IsKFin ε σ u := by
  let t : Set H := Set.range fun k : KG ε => σ (toMK k) u
  obtain ⟨b, hbt, hsp, hli⟩ := exists_linearIndependent ℂ t
  have hfin : b.Finite := by
    by_contra hinf
    haveI : Infinite b := Set.infinite_coe_iff.2 hinf
    let e : Fin (M + 1) ↪ b := Fin.valEmbedding.trans (Infinite.natEmbedding b)
    choose k hk using fun i => hbt (e i).2
    have hc : Continuous fun w : H => fun i : Fin (M + 1) => σ (toMK (k i)) w :=
      continuous_pi fun i => (σ _).continuous
    have ho := (isOpen_setOf_linearIndependent (𝕜 := ℂ) (E := H) (ι := Fin (M + 1))).preimage hc
    have hu' : LinearIndependent ℂ fun i : Fin (M + 1) => σ (toMK (k i)) u := by
      have := hli.comp e e.injective
      rwa [show (Subtype.val ∘ e : Fin (M + 1) → H) = _ from funext fun i => (hk i).symm] at this
    obtain ⟨w, hw, hwU⟩ := mem_closure_iff.1 hu _ ho hu'
    obtain ⟨S, hS, hM, hwS, hK⟩ := hU w hwU
    have h1 : LinearIndependent ℂ fun i : Fin (M + 1) =>
        (⟨σ (toMK (k i)) w, hK _ (toMK_mem_K _) w hwS⟩ : S) :=
      LinearIndependent.of_comp S.subtype hw
    have h2 := h1.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨Submodule.span ℂ t, hsp ▸ FiniteDimensional.span_of_finite ℂ hfin, Submodule.subset_span ⟨1, ?_⟩,
    fun g hg v hv => ?_⟩
  · exact sigma_one hσ u
  · refine (Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
    exact Submodule.subset_span ⟨g' * k, sigma_mul hσ (K_le_UJ hg) (K_le_UJ (toMK_mem_K k)) u⟩

variable [CompleteSpace H]

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_word (isUnit_Jm ε) h.1 l hl`. Set `A : W →ₗ[ℂ] H` to `(smooth (Jm ε) σ).subtype ∘ₗ L ∘ₗ Submodule.inclusion hW`. Establish `hA : ∀ x : W, A x = Dw σ l x` using `fun x => hL _`. Use `⟨⟨A, A.continuous_of_seq_closed_graph fun s x z hs hz => h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_⟩, hA⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) atTop (𝓝 ⟪y, z⟫_ℂ)` using `tendsto_const_nhds.inner hz`.

Simplify using `only [hA, fun x : W => inner_Dw h.1 hl hy (hW _ x.2)] at h1 ⊢`. Conclude with `tendsto_nhds_unique h1 (tendsto_const_nhds.mul (tendsto_const_nhds.inner ((continuous_subtype_val.tendsto x).comp hs)))`.
-/
theorem exists_word_clm (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W] (hW : ∀ w ∈ W, Sm ε σ w)
    {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) : ∃ A : W →L[ℂ] H, ∀ w : W, A w = Dw σ l w := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) h.1 l hl
  let A : W →ₗ[ℂ] H := (smooth (Jm ε) σ).subtype ∘ₗ L ∘ₗ Submodule.inclusion hW
  have hA : ∀ x : W, A x = Dw σ l x := fun x => hL _
  refine ⟨⟨A, A.continuous_of_seq_closed_graph fun s x z hs hz =>
    h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_⟩, hA⟩
  have h1 : Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) atTop (𝓝 ⟪y, z⟫_ℂ) := tendsto_const_nhds.inner hz
  simp only [hA, fun x : W => inner_Dw h.1 hl hy (hW _ x.2)] at h1 ⊢
  exact tendsto_nhds_unique h1
    (tendsto_const_nhds.mul (tendsto_const_nhds.inner ((continuous_subtype_val.tendsto x).comp hs)))

/- English proof (translation)
Take `⟨S, C, hS, hC, hts⟩` from `GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt n ε H σ h`. Use `choose A hA using fun l : {l // l ∈ S} => exists_word_clm h W hW (hS l.1 l.2)`. Use `haveI : Finite {l // l ∈ S} := (List.finite_toSet S).to_subtype`. Take `⟨B, hB⟩` from `(Set.finite_range fun l => ‖A l‖ ^ 2).bddAbove`. Establish `hB' : ∀ l, ‖A l‖ ^ 2 ≤ |B|` using `fun l => (hB ⟨l, rfl⟩).trans (le_abs_self B)`.

Take `⟨w, b, -⟩` from `exists_hilbertBasis ℂ W`. Establish `hfin : Finite w`. Assume the negation of the conclusion as `hinf`. Use `haveI : Infinite w := not_finite_iff_infinite.1 hinf`. Take `⟨m, hm⟩` from `exists_nat_gt (C * |B|)`.

Set `e : Fin m ↪ w` to `Fin.valEmbedding.trans (Infinite.natEmbedding w)`. Establish `ho : Orthonormal ℂ fun j => b (e j)` using `b.orthonormal.comp e e.injective`. Establish `key` using `hts (Fin m) (fun j => b (e j)) (fun j => b (e j)) |B| (abs_nonneg B) (fun j => hW _ (b (e j)).2) (fun l hl z => by`. Establish `e1 : ∑ j, z j • Dw σ l (b (e j) : H) = A ⟨l, hl⟩ (∑ j, z j • b (e j))`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_smul, hA]`. Establish `e2 : ‖∑ j, z j • b (e j)‖ ^ 2 = ∑ j, ‖z j‖ ^ 2`. Use `ho.inner_sum z z Finset.univ` as an intermediate fact. Rewrite `this` using `[inner_self_eq_norm_sq_to_K]`. Simplify using `only [RCLike.conj_mul] at this`.

Conclude with `this` after adjusting the coercions. Rewrite using `[e1, ← e2]`. Combine the equalities or inequalities in the displayed calculation. Establish `hn : ∀ j, ‖(b (e j) : H)‖ = 1` using `fun j => ho.1 j`. Simplify using `only [inner_self_eq_norm_sq_to_K, hn] at key`.

Simplify using `at key`. Establish `h0 : 0 ≤ C * |B|` using `mul_nonneg hC (abs_nonneg B)`. Use the polynomial consequences of the given equalities and inequalities. Use `haveI := Fintype.ofFinite w`. Conclude with `b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite`.
-/
theorem finiteDimensional_of_smooth (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W]
    (hW : ∀ w ∈ W, Sm ε σ w) : FiniteDimensional ℂ W := by
  obtain ⟨S, C, hS, hC, hts⟩ := GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt n ε H σ h
  choose A hA using fun l : {l // l ∈ S} => exists_word_clm h W hW (hS l.1 l.2)
  haveI : Finite {l // l ∈ S} := (List.finite_toSet S).to_subtype
  obtain ⟨B, hB⟩ := (Set.finite_range fun l => ‖A l‖ ^ 2).bddAbove
  have hB' : ∀ l, ‖A l‖ ^ 2 ≤ |B| := fun l => (hB ⟨l, rfl⟩).trans (le_abs_self B)
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ W
  have hfin : Finite w := by
    by_contra hinf
    haveI : Infinite w := not_finite_iff_infinite.1 hinf
    obtain ⟨m, hm⟩ := exists_nat_gt (C * |B|)
    let e : Fin m ↪ w := Fin.valEmbedding.trans (Infinite.natEmbedding w)
    have ho : Orthonormal ℂ fun j => b (e j) := b.orthonormal.comp e e.injective
    have key := hts (Fin m) (fun j => b (e j)) (fun j => b (e j)) |B| (abs_nonneg B) (fun j => hW _ (b (e j)).2)
      (fun l hl z => by
        have e1 : ∑ j, z j • Dw σ l (b (e j) : H) = A ⟨l, hl⟩ (∑ j, z j • b (e j)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hA]
        have e2 : ‖∑ j, z j • b (e j)‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
          have := ho.inner_sum z z Finset.univ
          rw [inner_self_eq_norm_sq_to_K] at this
          simp only [RCLike.conj_mul] at this
          exact_mod_cast this
        rw [e1, ← e2]
        calc _ ≤ (‖A ⟨l, hl⟩‖ * ‖∑ j, z j • b (e j)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((A _).le_opNorm _) 2
          _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hB' _) (sq_nonneg _))
    have hn : ∀ j, ‖(b (e j) : H)‖ = 1 := fun j => ho.1 j
    simp only [inner_self_eq_norm_sq_to_K, hn] at key
    simp at key
    have h0 : 0 ≤ C * |B| := mul_nonneg hC (abs_nonneg B)
    nlinarith
  haveI := Fintype.ofFinite w
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

end GlobalTheory.TypeSum.admitted

namespace GlobalTheory.TypeSum

/- English proof (translation)
Introduce `n ε H _ _ _ σ h U M hU`. Use `haveI : CompleteSpace U.topologicalClosure := U.isClosed_topologicalClosure.completeSpace_coe`. Use `haveI := admitted.finiteDimensional_of_smooth h U.topologicalClosure fun w hw => h.2.2.1 w (admitted.isKFin_of_mem_closure h.1 (U := U) hU hw)`. Conclude with `Submodule.finiteDimensional_of_le U.le_topologicalClosure`.
-/
theorem finiteDimensional_of_bounded_orbits : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ),
    (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) →
      FiniteDimensional ℂ U := by
  intro n ε H _ _ _ σ h U M hU
  haveI : CompleteSpace U.topologicalClosure := U.isClosed_topologicalClosure.completeSpace_coe
  haveI := admitted.finiteDimensional_of_smooth h U.topologicalClosure fun w hw =>
    h.2.2.1 w (admitted.isKFin_of_mem_closure h.1 (U := U) hU hw)
  exact Submodule.finiteDimensional_of_le U.le_topologicalClosure

end GlobalTheory.TypeSum
