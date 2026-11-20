import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)`. Rewrite `h` using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Use `h using 2` and compare the differences between its conclusion and the goal. Establish `: ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F)` using `by simp`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem valued_absNorm_lt_one_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  convert h using 2
  have : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) := by simp
  rw [this]
  rfl

/- English proof (translation)
Introduce `F _ _ v n K hK`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set q : ℕ := Ideal.absNorm v.asIdeal with hq`. Establish `hq0 : 0 < q` using `lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)`.

Use `choose g hg1 hg2 hg3 using fun k : ℕ => hcon (q ^ k) (pow_pos hq0 k)`. Establish `hlt : ‖(q : v.adicCompletion F)‖ < 1` using `Valued.toNormedField.norm_lt_one_iff.2 (valued_absNorm_lt_one_adicCompletion F v)`. Establish `hpow : Filter.Tendsto (fun k : ℕ => ‖((q ^ k : ℕ) : v.adicCompletion F)‖) Filter.atTop (nhds 0)`. Simplify using `using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt`. Establish `key : ∀ A : ℕ → Matrix (Fin n) (Fin n) (v.adicCompletion F), (∀ k i j, Valued.v (A k i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ Valued.v ((q ^ k : ℕ) : v.adicCompletion F)) → Filter.Tendsto A Filter.atTop (nhds 1)`.

Introduce `A hA`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Conclude with `squeeze_zero (fun _ => norm_nonneg _) (fun k => Valued.toNormedField.norm_le_iff.2 (hA k i j)) hpow`. Establish `hlim : Filter.Tendsto g Filter.atTop (nhds 1)`.

Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `Filter.Tendsto.prodMk_nhds (key _ hg1) ?_` and prove the remaining obligations. Conclude with `(MulOpposite.continuous_op.tendsto _).comp (key _ hg2)`. Take `⟨k, hk⟩` from `(hlim.eventually (hK.mem_nhds K.one_mem)).exists`. Conclude with `hg3 k hk`.
-/
theorem exists_nat_congruence_le_open_subgroup_GL :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (K : Subgroup (GL (Fin n) (v.adicCompletion F))), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) →
    ∃ M : ℕ, 0 < M ∧ ∀ g : GL (Fin n) (v.adicCompletion F),
      (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((M : v.adicCompletion F))) →
      (∀ i j, Valued.v (((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ Valued.v ((M : v.adicCompletion F))) → g ∈ K := by
  intro F _ _ v n K hK
  by_contra hcon
  push Not at hcon
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hq0 : 0 < q := lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
  choose g hg1 hg2 hg3 using fun k : ℕ => hcon (q ^ k) (pow_pos hq0 k)
  have hlt : ‖(q : v.adicCompletion F)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.2 (valued_absNorm_lt_one_adicCompletion F v)
  have hpow : Filter.Tendsto (fun k : ℕ => ‖((q ^ k : ℕ) : v.adicCompletion F)‖)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
  have key : ∀ A : ℕ → Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (∀ k i j, Valued.v (A k i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((q ^ k : ℕ) : v.adicCompletion F)) →
      Filter.Tendsto A Filter.atTop (nhds 1) := by
    intro A hA
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun k => Valued.toNormedField.norm_le_iff.2 (hA k i j)) hpow
  have hlim : Filter.Tendsto g Filter.atTop (nhds 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds (key _ hg1) ?_
    exact (MulOpposite.continuous_op.tendsto _).comp (key _ hg2)
  obtain ⟨k, hk⟩ := (hlim.eventually (hK.mem_nhds K.one_mem)).exists
  exact hg3 k hk

end GlobalTheory
