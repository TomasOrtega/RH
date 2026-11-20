import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.NormProjectionSq

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

open NumberField.InfinitePlace Classical in
/- English proof (translation)
Establish `hne` using `ne_conj σ`. Establish `hcx : ∀ τ : E →+* ℂ, (mk τ).IsComplex` using `fun τ => IsTotallyComplex.isComplex _`. Set `wc : {w : InfinitePlace E // w.IsComplex}` to `⟨mk σ, hcx σ⟩`. Set `c' : ℂ` to `if (mk σ).embedding = σ then c else (starRingEnd ℂ) c`. Set `y : mixedEmbedding.mixedSpace E` to `(0, Pi.single wc c')`.

Set `B` to `mixedEmbedding.latticeBasis E`. Use `⟨fun i => B.repr y i, fun τ => ?_⟩` and prove the remaining obligations. Establish `hsum` using `B.sum_repr y`. Establish `hcoord : ∑ i, (B.repr y i : ℂ) * (mk τ).embedding (RingOfIntegers.basis E i : E) = y.2 ⟨mk τ, hcx τ⟩` using `by conv_rhs => rw [← hsum]`. Rewrite using `[Prod.snd_sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [B, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply, mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul]`. Establish `hy : y.2 ⟨mk τ, hcx τ⟩ = if mk τ = mk σ then c' else 0`. Simplify using `only [y]`. Distinguish the cases in `h : mk τ = mk σ`.

Rewrite using `[if_pos h]`. Establish `: (⟨mk τ, hcx τ⟩ : {w : InfinitePlace E // w.IsComplex}) = wc` using `Subtype.ext h`. Rewrite using `[this, Pi.single_eq_same]`. Rewrite using `[if_neg h, Pi.single_eq_of_ne]`. Introduce `h'`.

Conclude with `h (congrArg Subtype.val h')`. Establish `hemb` using `embedding_mk_eq τ`. Establish `hval : ∑ i, (B.repr y i : ℂ) * τ (RingOfIntegers.basis E i : E) = if (mk τ).embedding = τ then (if mk τ = mk σ then c' else 0) else (starRingEnd ℂ) (if mk τ = mk σ then c' else 0)`. Break down `hemb with h | h` into its components or cases. Rewrite using `[if_pos h, ← hy, ← hcoord, h]`.

Distinguish the cases in `h' : (mk τ).embedding = τ`. Rewrite using `[if_pos h', ← hy, ← hcoord, h']`. Rewrite using `[if_neg h', ← hy, ← hcoord, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h, map_mul, Complex.conj_ofReal, ComplexEmbedding.conjugate_coe_eq]`.

Simplify using the standard rewrite rules. Rewrite using `[hval]`. Distinguish the cases in `hτ : τ = σ`. Substitute `hτ` using the available equality. Simplify using `only [if_true, c']`.

Apply the tactic sequence `split_ifs with h1 <;> simp`. Distinguish the cases in `hτ' : τ = ComplexEmbedding.conjugate σ`. Substitute `hτ'` using the available equality. Establish `hm : mk (ComplexEmbedding.conjugate σ) = mk σ` using `mk_conjugate_eq σ`. Simplify using `only [if_neg hτ, if_true, hm, c']`.

Break down `embedding_mk_eq σ with h | h` into its components or cases. Establish `: (mk σ).embedding ≠ ComplexEmbedding.conjugate σ` using `by rw [h]; exact hne.symm`. Simplify using `[h, hm, this, hne, hne.symm]`. Simplify using `[h, hm, hne, hne.symm]`. Establish `hm : mk τ ≠ mk σ`.

Introduce `h`. Break down `mk_eq_iff.mp h with h | h` into its components or cases. Conclude with `hτ h`. Conclude with `hτ' (by rw [← h]; exact (ComplexEmbedding.involutive_conjugate (K := E) τ).symm)`. Simplify using `[hτ, hτ', hm]`.
-/
lemma emb_comb [IsCMField E] (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ τ : E →+* ℂ,
      ∑ i, (r i : ℂ) * τ (RingOfIntegers.basis E i : E) =
        if τ = σ then c else if τ = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c else 0 := by
  classical
  have hne := ne_conj σ
  have hcx : ∀ τ : E →+* ℂ, (mk τ).IsComplex := fun τ => IsTotallyComplex.isComplex _
  let wc : {w : InfinitePlace E // w.IsComplex} := ⟨mk σ, hcx σ⟩
  let c' : ℂ := if (mk σ).embedding = σ then c else (starRingEnd ℂ) c
  let y : mixedEmbedding.mixedSpace E := (0, Pi.single wc c')
  let B := mixedEmbedding.latticeBasis E
  refine ⟨fun i => B.repr y i, fun τ => ?_⟩
  have hsum := B.sum_repr y

  have hcoord : ∑ i, (B.repr y i : ℂ) * (mk τ).embedding (RingOfIntegers.basis E i : E) =
      y.2 ⟨mk τ, hcx τ⟩ := by
    conv_rhs => rw [← hsum]
    rw [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply,
      mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul]
  have hy : y.2 ⟨mk τ, hcx τ⟩ = if mk τ = mk σ then c' else 0 := by
    simp only [y]
    by_cases h : mk τ = mk σ
    · rw [if_pos h]
      have : (⟨mk τ, hcx τ⟩ : {w : InfinitePlace E // w.IsComplex}) = wc := Subtype.ext h
      rw [this, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne]
      intro h'; exact h (congrArg Subtype.val h')
  have hemb := embedding_mk_eq τ

  have hval : ∑ i, (B.repr y i : ℂ) * τ (RingOfIntegers.basis E i : E) =
      if (mk τ).embedding = τ then (if mk τ = mk σ then c' else 0)
      else (starRingEnd ℂ) (if mk τ = mk σ then c' else 0) := by
    rcases hemb with h | h
    · rw [if_pos h, ← hy, ← hcoord, h]
    · by_cases h' : (mk τ).embedding = τ
      · rw [if_pos h', ← hy, ← hcoord, h']
      · rw [if_neg h', ← hy, ← hcoord, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h, map_mul, Complex.conj_ofReal, ComplexEmbedding.conjugate_coe_eq]
        simp
  rw [hval]
  by_cases hτ : τ = σ
  · subst hτ
    simp only [if_true, c']
    split_ifs with h1 <;> simp
  · by_cases hτ' : τ = ComplexEmbedding.conjugate σ
    · subst hτ'
      have hm : mk (ComplexEmbedding.conjugate σ) = mk σ := mk_conjugate_eq σ
      simp only [if_neg hτ, if_true, hm, c']
      rcases embedding_mk_eq σ with h | h
      · have : (mk σ).embedding ≠ ComplexEmbedding.conjugate σ := by rw [h]; exact hne.symm
        simp [h, hm, this, hne, hne.symm]
      · simp [h, hm, hne, hne.symm]
    · have hm : mk τ ≠ mk σ := by
        intro h; rcases mk_eq_iff.mp h with h | h
        · exact hτ h
        · exact hτ' (by rw [← h]; exact (ComplexEmbedding.involutive_conjugate (K := E) τ).symm)
      simp [hτ, hτ', hm]

open Classical in

/- English proof (translation)
Take `⟨r, hr⟩` from `emb_comb σ c`. Use `⟨r, fun v => ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Rewrite using `[Mc_apply, WithLp.ofLp_sum, Finset.sum_apply]`. Use `hr j.1` as an intermediate fact.

Simplify using `only [PiLp.smul_apply, act_apply, Complex.real_smul]`. Rewrite using `[show (∑ i, (r i : ℂ) * (j.1 (RingOfIntegers.basis E i : E) * v j)) = (∑ i, (r i : ℂ) * j.1 (RingOfIntegers.basis E i : E)) * v j by`. Rewrite using `[Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma Mc_comb [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ v : Vsp dim,
      Mc σ c v = ∑ i, r i • act (RingOfIntegers.basis E i) v := by
  classical
  obtain ⟨r, hr⟩ := emb_comb σ c
  refine ⟨r, fun v => ?_⟩
  ext j
  rw [Mc_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have := hr j.1
  simp only [PiLp.smul_apply, act_apply, Complex.real_smul]
  rw [show (∑ i, (r i : ℂ) * (j.1 (RingOfIntegers.basis E i : E) * v j)) =
    (∑ i, (r i : ℂ) * j.1 (RingOfIntegers.basis E i : E)) * v j by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, this]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨r, hr⟩` from `Mc_comb (dim := dim) σ c`. Rewrite using `[hr]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hS _ _ hv)`.
-/
lemma Mc_mem [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (S : Submodule ℝ (Vsp dim))
    (hS : ∀ (α : 𝓞 E) v, v ∈ S → act α v ∈ S) (c : ℂ) {v : Vsp dim} (hv : v ∈ S) :
    Mc σ c v ∈ S := by
  obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
  rw [hr]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hS _ _ hv)

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
