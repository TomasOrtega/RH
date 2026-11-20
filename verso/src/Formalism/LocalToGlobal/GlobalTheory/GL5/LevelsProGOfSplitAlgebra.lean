import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.ProGTransfer
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.SmallOrderPrimeLogSumBound
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Topology Filter
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ProGW

open Formalism.UG.P

/- English proof (translation)
Unfold `IsProGrp`. Use `⟨hc, fun N hN hNn => ?_⟩` and prove the remaining obligations. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp hc`. Use `haveI : Fact g.Prime := ⟨hg⟩`. Use `haveI := hNn`.

Use `haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN`. Establish `hP : IsPGroup g (H ⧸ N)`. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`.

Establish `ht : Tendsto (fun m : ℕ => x ^ (g ^ m)) atTop (𝓝 (1 : H))`. Rewrite using `[tendsto_subtype_rng]`. Simplify using `using hp x.1 x.2`. Take `⟨m, hm⟩` from `(ht.eventually (hN.mem_nhds N.one_mem)).exists`. Conclude with `⟨m, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hm⟩`.

Take `⟨n, hn⟩` from `IsPGroup.iff_card.mp hP`. Conclude with `⟨n, hn⟩`.
-/
theorem isProGrp_of_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : ℕ) (hg : g.Prime) (H : Subgroup G) (hc : IsCompact (H : Set G))
    (hp : ∀ x ∈ H, Tendsto (fun m : ℕ => x ^ (g ^ m)) atTop (𝓝 1)) : IsProGrp g H := by
  unfold IsProGrp
  refine ⟨hc, fun N hN hNn => ?_⟩
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hc
  haveI : Fact g.Prime := ⟨hg⟩
  haveI := hNn
  haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have hP : IsPGroup g (H ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have ht : Tendsto (fun m : ℕ => x ^ (g ^ m)) atTop (𝓝 (1 : H)) := by
        rw [tendsto_subtype_rng]
        simpa using hp x.1 x.2
      obtain ⟨m, hm⟩ := (ht.eventually (hN.mem_nhds N.one_mem)).exists
      exact ⟨m, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hm⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  exact ⟨n, hn⟩

/- English proof (translation)
Use `isProGrp_of_pow g hg (H.map f) ?_ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map]`. Conclude with `hc.image hf`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `(hf.tendsto 1).comp (hp x hx)` as an intermediate fact.

Simplify `this` using `[Function.comp_def, map_pow]`.
-/
theorem isProGrp_map {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] (g : ℕ) (hg : g.Prime) (f : G₁ →* G₂) (hf : Continuous f) (H : Subgroup G₁)
    (hc : IsCompact (H : Set G₁)) (hp : ∀ x ∈ H, Tendsto (fun m : ℕ => x ^ (g ^ m)) atTop (𝓝 1)) :
    IsProGrp g (H.map f) := by
  refine isProGrp_of_pow g hg (H.map f) ?_ ?_
  · rw [Subgroup.coe_map]
    exact hc.image hf
  · rintro _ ⟨x, hx, rfl⟩
    have := (hf.tendsto 1).comp (hp x hx)
    simpa [Function.comp_def, map_pow] using this

section Ring
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  [IsNoetherianRing R]

/- English proof (translation)
Establish `hcl : ∀ J : Ideal R, IsClosed (J : Set R)`. Introduce `J`. Take `⟨s, hs⟩` from `IsNoetherian.noetherian J`. Establish `hJ : (J : Set R) = Set.range (fun c : s → R => ∑ i, c i • (i : R))`. Use extensionality with `x`.

Establish `hr : Set.range ((↑) : s → R) = (s : Set R)` using `by simp`. Rewrite using `[SetLike.mem_coe, ← hs, ← hr, Submodule.mem_span_range_iff_exists_fun]`. Both sides reduce to the same expression. Rewrite using `[hJ]`. Conclude with `(isCompact_range (by fun_prop)).isClosed`.

Take `⟨W, hWV, hWo, hW0⟩` from `mem_nhds_iff.mp hV`. Establish `hK : IsCompact (Wᶜ)` using `hWo.isClosed_compl.isCompact`. Establish `hst : Wᶜ ∩ ⋂ n : ℕ, ((I ^ n : Ideal R) : Set R) = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`.

Introduce and unpack `⟨hxW, hx⟩`. Establish `hx0 : x ∈ (⨅ n : ℕ, I ^ n : Ideal R)`. Rewrite using `[Submodule.mem_iInf]`. Introduce `n`. Conclude with `Set.mem_iInter.mp hx n`.

Rewrite `hx0` using `[hI, Ideal.mem_bot]`. Conclude with `hxW (by rw [hx0]; exact hW0)`. Establish `hdir : Directed (· ⊇ ·) (fun n : ℕ => ((I ^ n : Ideal R) : Set R))`. Introduce `a b`. Use `⟨max a b, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (le_max_left a b))`. Conclude with `SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (le_max_right a b))`. Take `⟨n, hn⟩` from `hK.elim_directed_family_closed (fun n : ℕ => ((I ^ n : Ideal R) : Set R)) (fun n => hcl _) hst hdir`. Use `⟨n, fun x hx => hWV ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hxW`.

Establish `hm : x ∈ Wᶜ ∩ ((I ^ n : Ideal R) : Set R)` using `⟨hxW, hx⟩`. Rewrite `hm` using `[hn]`. Conclude with `hm`.
-/
theorem pow_subset_nhds (I : Ideal R) (hI : (⨅ n : ℕ, I ^ n) = ⊥) (V : Set R) (hV : V ∈ 𝓝 (0 : R)) :
    ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ V := by
  have hcl : ∀ J : Ideal R, IsClosed (J : Set R) := by
    intro J
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian J
    have hJ : (J : Set R) = Set.range (fun c : s → R => ∑ i, c i • (i : R)) := by
      ext x
      have hr : Set.range ((↑) : s → R) = (s : Set R) := by simp
      rw [SetLike.mem_coe, ← hs, ← hr, Submodule.mem_span_range_iff_exists_fun]
      rfl
    rw [hJ]
    exact (isCompact_range (by fun_prop)).isClosed
  obtain ⟨W, hWV, hWo, hW0⟩ := mem_nhds_iff.mp hV
  have hK : IsCompact (Wᶜ) := hWo.isClosed_compl.isCompact
  have hst : Wᶜ ∩ ⋂ n : ℕ, ((I ^ n : Ideal R) : Set R) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxW, hx⟩
    have hx0 : x ∈ (⨅ n : ℕ, I ^ n : Ideal R) := by
      rw [Submodule.mem_iInf]
      intro n
      exact Set.mem_iInter.mp hx n
    rw [hI, Ideal.mem_bot] at hx0
    exact hxW (by rw [hx0]; exact hW0)
  have hdir : Directed (· ⊇ ·) (fun n : ℕ => ((I ^ n : Ideal R) : Set R)) := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · exact SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (le_max_left a b))
    · exact SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (le_max_right a b))
  obtain ⟨n, hn⟩ := hK.elim_directed_family_closed (fun n : ℕ => ((I ^ n : Ideal R) : Set R))
    (fun n => hcl _) hst hdir
  refine ⟨n, fun x hx => hWV ?_⟩
  by_contra hxW
  have hm : x ∈ Wᶜ ∩ ((I ^ n : Ideal R) : Set R) := ⟨hxW, hx⟩
  rw [hn] at hm
  exact hm

/- English proof (translation)
Rewrite using `[← tendsto_sub_nhds_zero_iff]`. Introduce `U hU`. Take `⟨n, hn⟩` from `pow_subset_nhds I hI U hU`. Rewrite using `[Filter.mem_map, Filter.mem_atTop_sets]`. Conclude with `⟨n, fun m hm => hn (Ideal.pow_le_pow_right (by omega) (hx m))⟩`.
-/
theorem tendsto_of_mem_pow (I : Ideal R) (hI : (⨅ n : ℕ, I ^ n) = ⊥) (x : ℕ → R) (c : R)
    (hx : ∀ m, x m - c ∈ I ^ (m + 1)) : Tendsto x atTop (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff]
  intro U hU
  obtain ⟨n, hn⟩ := pow_subset_nhds I hI U hU
  rw [Filter.mem_map, Filter.mem_atTop_sets]
  exact ⟨n, fun m hm => hn (Ideal.pow_le_pow_right (by omega) (hx m))⟩

end Ring

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun l _ => J.mul_mem_left _ (hD l j)`.
-/
private lemma ent_mul_left_lemma_3 {R : Type} [CommRing R] {k : ℕ} (J : Ideal R)
    (M D : Matrix (Fin k) (Fin k) R) (hD : ∀ i j, D i j ∈ J) (i j : Fin k) : (M * D) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => J.mul_mem_left _ (hD l j)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun l _ => Ideal.mul_mem_mul (hD i l) (hE l j)`.
-/
private lemma ent_mul_mul_lemma_5 {R : Type} [CommRing R] {k : ℕ} (J K : Ideal R)
    (D E : Matrix (Fin k) (Fin k) R) (hD : ∀ i j, D i j ∈ J) (hE : ∀ i j, E i j ∈ K) (i j : Fin k) :
    (D * E) i j ∈ J * K := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => Ideal.mul_mem_mul (hD i l) (hE l j)

/- English proof (translation)
Rewrite using `[← geom_sum_mul B n]`. Conclude with `ent_mul_left_lemma_3 J _ _ hB i j`.
-/
private lemma ent_pow_sub_one_lemma_6 {R : Type} [CommRing R] {k : ℕ} (J : Ideal R)
    (B : Matrix (Fin k) (Fin k) R) (hB : ∀ i j, (B - 1) i j ∈ J) (n : ℕ) (i j : Fin k) :
    (B ^ n - 1) i j ∈ J := by
  rw [← geom_sum_mul B n]
  exact ent_mul_left_lemma_3 J _ _ hB i j

/- English proof (translation)
Proceed by induction on `m generalizing i j with`. Consider the case `zero => simpa using hA i j`. Consider the case `succ m ih`. Establish `hB : ∀ a b, (A ^ (g ^ m) - 1) a b ∈ I ^ (m + 1)` using `ih`. Establish `hE : ∀ a b, (∑ t ∈ Finset.range g, ((A ^ (g ^ m)) ^ t - 1)) a b ∈ I ^ (m + 1)`.

Introduce `a b`. Rewrite using `[Matrix.sum_apply]`. Conclude with `sum_mem fun t _ => ent_pow_sub_one_lemma_6 _ _ hB t a b`. Establish `hS : ∑ t ∈ Finset.range g, (A ^ (g ^ m)) ^ t = ∑ t ∈ Finset.range g, ((A ^ (g ^ m)) ^ t - 1) + g • (1 : Matrix (Fin k) (Fin k) R)`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sub_add_cancel]`.

Establish `hkey : A ^ (g ^ (m + 1)) - 1 = (∑ t ∈ Finset.range g, ((A ^ (g ^ m)) ^ t - 1)) * (A ^ (g ^ m) - 1) + g • (A ^ (g ^ m) - 1)`. Rewrite using `[pow_succ, pow_mul, ← geom_sum_mul (A ^ (g ^ m)) g, hS, add_mul, smul_mul_assoc, one_mul]`. Rewrite using `[hkey, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]`. Establish `h2 : I ^ (m + 1) * I ^ (m + 1) ≤ I ^ (m + 1 + 1)`. Rewrite using `[← pow_add]`.

Conclude with `Ideal.pow_le_pow_right (by omega)`. Use `add_mem (h2 (ent_mul_mul_lemma_5 _ _ _ _ hE hB i j)) ?_` and prove the remaining obligations. Rewrite using `[pow_succ' I (m + 1)]`. Conclude with `Ideal.mul_mem_mul hg (hB i j)`.
-/
theorem congPow {R : Type} [CommRing R] (I : Ideal R) (g k : ℕ) (hg : (g : R) ∈ I)
    (A : Matrix (Fin k) (Fin k) R) (hA : ∀ i j, (A - 1) i j ∈ I) (m : ℕ) (i j : Fin k) :
    (A ^ (g ^ m) - 1) i j ∈ I ^ (m + 1) := by
  induction m generalizing i j with
  | zero => simpa using hA i j
  | succ m ih =>
    have hB : ∀ a b, (A ^ (g ^ m) - 1) a b ∈ I ^ (m + 1) := ih
    have hE : ∀ a b, (∑ t ∈ Finset.range g, ((A ^ (g ^ m)) ^ t - 1)) a b ∈ I ^ (m + 1) := by
      intro a b
      rw [Matrix.sum_apply]
      exact sum_mem fun t _ => ent_pow_sub_one_lemma_6 _ _ hB t a b
    have hS : ∑ t ∈ Finset.range g, (A ^ (g ^ m)) ^ t =
        ∑ t ∈ Finset.range g, ((A ^ (g ^ m)) ^ t - 1) + g • (1 : Matrix (Fin k) (Fin k) R) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sub_add_cancel]
    have hkey : A ^ (g ^ (m + 1)) - 1 =
        (∑ t ∈ Finset.range g, ((A ^ (g ^ m)) ^ t - 1)) * (A ^ (g ^ m) - 1) + g • (A ^ (g ^ m) - 1) := by
      rw [pow_succ, pow_mul, ← geom_sum_mul (A ^ (g ^ m)) g, hS, add_mul, smul_mul_assoc, one_mul]
    rw [hkey, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    have h2 : I ^ (m + 1) * I ^ (m + 1) ≤ I ^ (m + 1 + 1) := by
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    refine add_mem (h2 (ent_mul_mul_lemma_5 _ _ _ _ hE hB i j)) ?_
    rw [pow_succ' I (m + 1)]
    exact Ideal.mul_mem_mul hg (hB i j)

/- English proof (translation)
Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff, map_one]`. Use `show Tendsto (fun m => ((f m : M), MulOpposite.op ((f m)⁻¹ : Mˣ).val)) atTop (𝓝 ((1 : M), MulOpposite.op (1 : M)))`. Conclude with `h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto (1 : M)).comp h2)`.
-/
theorem units_tendsto_one {M : Type} [Monoid M] [TopologicalSpace M] (f : ℕ → Mˣ)
    (h1 : Tendsto (fun m => (f m : M)) atTop (𝓝 1)) (h2 : Tendsto (fun m => ((f m)⁻¹ : Mˣ).val) atTop (𝓝 1)) :
    Tendsto f atTop (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff, map_one]
  show Tendsto (fun m => ((f m : M), MulOpposite.op ((f m)⁻¹ : Mˣ).val)) atTop
    (𝓝 ((1 : M), MulOpposite.op (1 : M)))
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto (1 : M)).comp h2)

section Iw

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))` using `Formalism.UG.P.glint_finite_residueField v`. Establish `h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))` using `Valued.isClosed_valuationSubring _`. Establish `h3 : CompleteSpace (v.adicCompletionIntegers F)` using `h2.completeSpace_coe`. Conclude with `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2 ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩`.
-/
theorem compactOv (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) := by
  have h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isClosed_valuationSubring _
  have h3 : CompleteSpace (v.adicCompletionIntegers F) := h2.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩

/- English proof (translation)
Introduce `F _ _ k v g hg hgv`. Use `haveI := compactOv v`. Use `set O := v.adicCompletionIntegers F`. Use `set 𝔪 := IsLocalRing.maximalIdeal O with h𝔪`. Establish `hmax : (g : O) ∈ 𝔪` using `Formalism.L2.G.Triv.natCast_mem_max v g hgv`.

Establish `hI : (⨅ n : ℕ, 𝔪 ^ n) = ⊥` using `Ideal.iInf_pow_eq_bot_of_isLocalRing 𝔪 (Ideal.IsMaximal.ne_top inferInstance)`. Set `S : Subgroup (GL (Fin k) O)` to `(Subgroup.closure (upperUni k (O ⧸ 𝔪))).comap (redGL 𝔪)`. Establish `hred : ∀ (a : GL (Fin k) O) (i j : Fin k), ((redGL 𝔪 a : GL (Fin k) (O ⧸ 𝔪)) : Matrix (Fin k) (Fin k) (O ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 ((a : Matrix (Fin k) (Fin k) O) i j)` using `fun a i j => rfl`. Establish `hmem : ∀ a : GL (Fin k) O, a ∈ S ↔ ∀ i j : Fin k, (j < i → (a : Matrix (Fin k) (Fin k) O) i j ∈ 𝔪) ∧ (a : Matrix (Fin k) (Fin k) O) i i - 1 ∈ 𝔪`. Introduce `a`.

Prove the components needed by the constructor for the conclusion. Introduce `ha i j`. Establish `h` using `Formalism.L2.G.Triv.closure_upperUni _ _ (Subgroup.mem_comap.1 ha) i j`. Rewrite `h` using `[hred, hred]`. Use `⟨fun hji => Ideal.Quotient.eq_zero_iff_mem.1 (h.1 hji), ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h.2, sub_self]`. Introduce `h`. Apply `Subgroup.mem_comap.2` to reduce the goal to its premises. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Introduce `i j`.

Rewrite using `[hred, hred]`. Use `⟨fun hji => Ideal.Quotient.eq_zero_iff_mem.2 ((h i j).1 hji), ?_⟩` and prove the remaining obligations. Use `Ideal.Quotient.eq_zero_iff_mem.2 (h i j).2` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hent : ∀ i j : Fin k, Continuous (fun a : GL (Fin k) O => (a : Matrix (Fin k) (Fin k) O) i j)` using `fun i j => Units.continuous_val.matrix_elem i j`.

Establish `hmcl : IsClosed (𝔪 : Set O)` using `(Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed`. Establish `hScl : IsClosed (S : Set (GL (Fin k) O))`. Establish `: (S : Set (GL (Fin k) O)) = ⋂ i : Fin k, ⋂ j : Fin k, ({a : GL (Fin k) O | j < i → (a : Matrix (Fin k) (Fin k) O) i j ∈ 𝔪} ∩ {a : GL (Fin k) O | (a : Matrix (Fin k) (Fin k) O) i i - 1 ∈ 𝔪})`. Use extensionality with `a`. Simplify using `only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]`.

Rewrite using `[this]`. Use `isClosed_iInter fun i => isClosed_iInter fun j => IsClosed.inter ?_ ?_` and prove the remaining obligations. Distinguish the cases in `hji : j < i`. Simplify using `only [hji, true_implies]`. Conclude with `hmcl.preimage (hent i j)`.

Simplify using `only [hji, false_implies, Set.setOf_true]`. Conclude with `isClosed_univ`. Conclude with `hmcl.preimage ((hent i i).sub continuous_const)`. Establish `: CompactSpace (Matrix (Fin k) (Fin k) O)` using `inferInstanceAs (CompactSpace (Fin k → Fin k → O))`. Establish `hcS : IsCompact (S : Set (GL (Fin k) O))` using `hScl.isCompact`.

Establish `hpow : ∀ a ∈ S, Tendsto (fun m : ℕ => a ^ (g ^ m)) atTop (𝓝 1)`. Introduce `a ha`. Take `⟨s, hs⟩ : ∃ s, k ≤ g ^ s` from `⟨k, (Nat.lt_pow_self hg.one_lt).le⟩`. Establish `hA : ∀ i j : Fin k, j ≤ i → ((a : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪`. Introduce `i j hji`.

Break down `hji.lt_or_eq with h | h` into its components or cases. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero]`. Conclude with `((hmem a).1 ha i j).1 h`. Substitute `h` using the available equality. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_eq]`.

Conclude with `((hmem a).1 ha j j).2`. Use `set B := a ^ (g ^ s) with hB`. Establish `hBv : (B : Matrix (Fin k) (Fin k) O) = (a : Matrix (Fin k) (Fin k) O) ^ (g ^ s)`. Rewrite using `[hB, Units.val_pow_eq_pow_val]`. Establish `hB1 : ∀ i j, ((B : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪`.

Introduce `i j`. Rewrite using `[hBv]`. Conclude with `Formalism.L2.G.Triv.unip_pow 𝔪 g hg hmax _ hA s hs i j`. Establish `hC : ∀ m (i j : Fin k), (((B ^ (g ^ m) : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪 ^ (m + 1)`. Introduce `m i j`.

Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `congPow 𝔪 g k hmax _ hB1 m i j`. Establish `e : ∀ m, a ^ (g ^ (m + s)) = B ^ (g ^ m)` using `fun m => by rw [hB, ← pow_mul, ← pow_add, add_comm]`. Rewrite using `[← Filter.tendsto_add_atTop_iff_nat s]`. Simplify using `only [e]`.

Use `units_tendsto_one _ ?_ ?_` and prove the remaining obligations. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Use `tendsto_of_mem_pow 𝔪 hI _ _ fun m => ?_` and prove the remaining obligations. Use `hC m i j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply]`. Then use the resulting hypothesis.

Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Use `tendsto_of_mem_pow 𝔪 hI _ _ fun m => ?_` and prove the remaining obligations. Use `set u := B ^ (g ^ m)`. Establish `hid : ((u⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) - 1 = -(((u⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) * ((u : Matrix (Fin k) (Fin k) O) - 1))`. Rewrite using `[mul_sub, Units.inv_mul, mul_one, neg_sub]`.

Establish `: (((u⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪 ^ (m + 1)`. Rewrite using `[hid, Matrix.neg_apply, Ideal.neg_mem_iff, Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hC m l j)`. Rewrite `this` using `[Matrix.sub_apply]`. Then use the resulting hypothesis. Establish `hφ : Continuous (algebraMap O (v.adicCompletion F))` using `continuous_subtype_val`.

Establish `hcont : Continuous (bc (n` using `Fin k) (algebraMap O (v.adicCompletion F))) := Continuous.units_map _ (continuous_id.matrix_map hφ)`. Conclude with `isProGrp_map g hg _ hcont S hcS hpow`.
-/
theorem iwProG : Formalism.L2.G.Triv.IwProG := by
  intro F _ _ k v g hg hgv
  haveI := compactOv v
  set O := v.adicCompletionIntegers F
  set 𝔪 := IsLocalRing.maximalIdeal O with h𝔪
  have hmax : (g : O) ∈ 𝔪 := Formalism.L2.G.Triv.natCast_mem_max v g hgv
  have hI : (⨅ n : ℕ, 𝔪 ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing 𝔪 (Ideal.IsMaximal.ne_top inferInstance)
  let S : Subgroup (GL (Fin k) O) := (Subgroup.closure (upperUni k (O ⧸ 𝔪))).comap (redGL 𝔪)
  have hred : ∀ (a : GL (Fin k) O) (i j : Fin k),
      ((redGL 𝔪 a : GL (Fin k) (O ⧸ 𝔪)) : Matrix (Fin k) (Fin k) (O ⧸ 𝔪)) i j =
        Ideal.Quotient.mk 𝔪 ((a : Matrix (Fin k) (Fin k) O) i j) := fun a i j => rfl
  have hmem : ∀ a : GL (Fin k) O, a ∈ S ↔ ∀ i j : Fin k,
      (j < i → (a : Matrix (Fin k) (Fin k) O) i j ∈ 𝔪) ∧ (a : Matrix (Fin k) (Fin k) O) i i - 1 ∈ 𝔪 := by
    intro a
    constructor
    · intro ha i j
      have h := Formalism.L2.G.Triv.closure_upperUni _ _ (Subgroup.mem_comap.1 ha) i j
      rw [hred, hred] at h
      refine ⟨fun hji => Ideal.Quotient.eq_zero_iff_mem.1 (h.1 hji), ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h.2, sub_self]
    · intro h
      apply Subgroup.mem_comap.2
      apply Subgroup.subset_closure
      intro i j
      rw [hred, hred]
      refine ⟨fun hji => Ideal.Quotient.eq_zero_iff_mem.2 ((h i j).1 hji), ?_⟩
      have := Ideal.Quotient.eq_zero_iff_mem.2 (h i j).2
      rwa [map_sub, map_one, sub_eq_zero] at this
  have hent : ∀ i j : Fin k, Continuous (fun a : GL (Fin k) O => (a : Matrix (Fin k) (Fin k) O) i j) :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hmcl : IsClosed (𝔪 : Set O) := (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed
  have hScl : IsClosed (S : Set (GL (Fin k) O)) := by
    have : (S : Set (GL (Fin k) O)) = ⋂ i : Fin k, ⋂ j : Fin k,
        ({a : GL (Fin k) O | j < i → (a : Matrix (Fin k) (Fin k) O) i j ∈ 𝔪} ∩
          {a : GL (Fin k) O | (a : Matrix (Fin k) (Fin k) O) i i - 1 ∈ 𝔪}) := by
      ext a
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => IsClosed.inter ?_ ?_
    · by_cases hji : j < i
      · simp only [hji, true_implies]; exact hmcl.preimage (hent i j)
      · simp only [hji, false_implies, Set.setOf_true]; exact isClosed_univ
    · exact hmcl.preimage ((hent i i).sub continuous_const)
  have : CompactSpace (Matrix (Fin k) (Fin k) O) := inferInstanceAs (CompactSpace (Fin k → Fin k → O))
  have hcS : IsCompact (S : Set (GL (Fin k) O)) := hScl.isCompact
  have hpow : ∀ a ∈ S, Tendsto (fun m : ℕ => a ^ (g ^ m)) atTop (𝓝 1) := by
    intro a ha
    obtain ⟨s, hs⟩ : ∃ s, k ≤ g ^ s := ⟨k, (Nat.lt_pow_self hg.one_lt).le⟩
    have hA : ∀ i j : Fin k, j ≤ i → ((a : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪 := by
      intro i j hji
      rcases hji.lt_or_eq with h | h
      · rw [Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero]
        exact ((hmem a).1 ha i j).1 h
      · subst h
        rw [Matrix.sub_apply, Matrix.one_apply_eq]
        exact ((hmem a).1 ha j j).2
    set B := a ^ (g ^ s) with hB
    have hBv : (B : Matrix (Fin k) (Fin k) O) = (a : Matrix (Fin k) (Fin k) O) ^ (g ^ s) := by
      rw [hB, Units.val_pow_eq_pow_val]
    have hB1 : ∀ i j, ((B : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪 := by
      intro i j; rw [hBv]; exact Formalism.L2.G.Triv.unip_pow 𝔪 g hg hmax _ hA s hs i j
    have hC : ∀ m (i j : Fin k), (((B ^ (g ^ m) : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪 ^ (m + 1) := by
      intro m i j
      rw [Units.val_pow_eq_pow_val]
      exact congPow 𝔪 g k hmax _ hB1 m i j
    have e : ∀ m, a ^ (g ^ (m + s)) = B ^ (g ^ m) := fun m => by rw [hB, ← pow_mul, ← pow_add, add_comm]
    rw [← Filter.tendsto_add_atTop_iff_nat s]
    simp only [e]
    refine units_tendsto_one _ ?_ ?_
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      refine tendsto_of_mem_pow 𝔪 hI _ _ fun m => ?_
      have := hC m i j
      rwa [Matrix.sub_apply] at this
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      refine tendsto_of_mem_pow 𝔪 hI _ _ fun m => ?_
      set u := B ^ (g ^ m)
      have hid : ((u⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) - 1 =
          -(((u⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) * ((u : Matrix (Fin k) (Fin k) O) - 1)) := by
        rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
      have : (((u⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) - 1) i j ∈ 𝔪 ^ (m + 1) := by
        rw [hid, Matrix.neg_apply, Ideal.neg_mem_iff, Matrix.mul_apply]
        exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hC m l j)
      rwa [Matrix.sub_apply] at this
  have hφ : Continuous (algebraMap O (v.adicCompletion F)) := continuous_subtype_val
  have hcont : Continuous (bc (n := Fin k) (algebraMap O (v.adicCompletion F))) :=
    Continuous.units_map _ (continuous_id.matrix_map hφ)
  exact isProGrp_map g hg _ hcont S hcS hpow

end Iw

open Formalism.UG.P

/- English proof (translation)
Unfold `IsProGrp at hP ⊢`. Take `⟨hPc, hPn⟩` from `hP`. Set `e : Uw ≃* P` to `{ toFun := fun x => ⟨θ x.1, h1 x.1 x.2⟩ invFun := fun p => ⟨ψ p, (h2 p p.2).1⟩ left_inv := fun x => Subtype.ext (h3 x.1 x.2) right_inv := fun p => Subtype.ext (h2 p p.2).2 map_mul' := fun x y => Subtype.ext (map_mul θ x.1 y.1) }`. Establish `hec : Continuous (e.symm : P → Uw)` using `by show Continuous (fun p : P => (⟨ψ p, (h2 p p.2).1⟩ : Uw))`. Conclude with `(hψ.comp continuous_subtype_val).subtype_mk _`.

Use `⟨?_, fun N hN hNn => ?_⟩` and prove the remaining obligations. Establish `hs : (Uw : Set G₁) = ψ '' (P : Set G₂)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨θ x, h1 x hx, h3 x hx⟩`. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `(h2 p hp).1`. Rewrite using `[hs]`. Conclude with `hPc.image hψ`.

Establish `hNo : IsOpen ((N.comap e.symm.toMonoidHom : Subgroup P) : Set P)`. Rewrite using `[Subgroup.coe_comap, MulEquiv.coe_toMonoidHom]`. Conclude with `hec.isOpen_preimage _ hN`. Take `⟨m, hm⟩` from `hPn (N.comap e.symm.toMonoidHom) hNo (hNn.comap _)`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hm]`. Conclude with `(Subgroup.index_comap_of_surjective N (f := e.symm.toMonoidHom) e.symm.surjective).symm`.
-/
theorem isProGrp_transfer {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    (g : ℕ) (θ : G₁ →* G₂) (hθ : Continuous θ) (ψ : G₂ → G₁) (hψ : Continuous ψ)
    (Uw : Subgroup G₁) (P : Subgroup G₂) (h1 : ∀ x ∈ Uw, θ x ∈ P) (h2 : ∀ p ∈ P, ψ p ∈ Uw ∧ θ (ψ p) = p)
    (h3 : ∀ x ∈ Uw, ψ (θ x) = x) (hP : IsProGrp g P) : IsProGrp g Uw := by
  unfold IsProGrp at hP ⊢
  obtain ⟨hPc, hPn⟩ := hP
  let e : Uw ≃* P :=
    { toFun := fun x => ⟨θ x.1, h1 x.1 x.2⟩
      invFun := fun p => ⟨ψ p, (h2 p p.2).1⟩
      left_inv := fun x => Subtype.ext (h3 x.1 x.2)
      right_inv := fun p => Subtype.ext (h2 p p.2).2
      map_mul' := fun x y => Subtype.ext (map_mul θ x.1 y.1) }
  have hec : Continuous (e.symm : P → Uw) := by
    show Continuous (fun p : P => (⟨ψ p, (h2 p p.2).1⟩ : Uw))
    exact (hψ.comp continuous_subtype_val).subtype_mk _
  refine ⟨?_, fun N hN hNn => ?_⟩
  · have hs : (Uw : Set G₁) = ψ '' (P : Set G₂) := by
      ext x
      constructor
      · intro hx
        exact ⟨θ x, h1 x hx, h3 x hx⟩
      · rintro ⟨p, hp, rfl⟩
        exact (h2 p hp).1
    rw [hs]
    exact hPc.image hψ
  · have hNo : IsOpen ((N.comap e.symm.toMonoidHom : Subgroup P) : Set P) := by
      rw [Subgroup.coe_comap, MulEquiv.coe_toMonoidHom]
      exact hec.isOpen_preimage _ hN
    obtain ⟨m, hm⟩ := hPn (N.comap e.symm.toMonoidHom) hNo (hNn.comap _)
    refine ⟨m, ?_⟩
    rw [← hm]
    exact (Subgroup.index_comap_of_surjective N (f := e.symm.toMonoidHom) e.symm.surjective).symm

section Lift
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def splitLift (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (u : GL n R) : GL n (R × R) :=
  ⟨pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ,
   pairMat ((u⁻¹ : GL n R) : Matrix n n R) (J₁ * (u : Matrix n n R) * J₁⁻¹)ᵀ,
   pairMat_mul_eq_one u.mul_inv
     (by rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ u.mul_inv, Matrix.transpose_one]),
   pairMat_mul_eq_one u.inv_mul
     (by rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ u.inv_mul, Matrix.transpose_one])⟩

/- English proof (translation)
Apply the tactic sequence `ext i j <;> simp [pairMat, Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum, Prod.ext_iff]`.
-/
private lemma pm_mul_lemma (X Y X' Y' : Matrix n n R) :
    pairMat X Y * pairMat X' Y' = pairMat (X * X') (Y * Y') := by
  ext i j <;> simp [pairMat, Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum, Prod.ext_iff]

/- English proof (translation)
Apply the tactic sequence `ext i j <;> simp [cT, swapR, pairMat, Prod.ext_iff]`.
-/
private lemma pm_cT_lemma_2 (X Y : Matrix n n R) : cT (swapR R) (pairMat X Y) = pairMat Yᵀ Xᵀ := by
  ext i j <;> simp [cT, swapR, pairMat, Prod.ext_iff]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `cT (swapR R) (pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ) * splitJ J₁ * pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ = splitJ J₁`. Establish `e1 : J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (u : Matrix n n R) = J₁`. Rewrite using `[Matrix.mul_assoc (J₁ * _) J₁⁻¹ J₁, Matrix.nonsing_inv_mul J₁ hJ, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Establish `hs : splitJ J₁ = pairMat J₁ J₁ᵀ` using `rfl`. Rewrite using `[hs, pm_cT_lemma_2, pm_mul_lemma, pm_mul_lemma, Matrix.transpose_transpose, e1]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Use `_ = J₁ᵀ := by rw [e1]`.
-/
theorem splitLift_mem (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (u : GL n R) :
    splitLift J₁ hJ u ∈ UJ (swapR R) (splitJ J₁) := by
  change cT (swapR R) (pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ) *
    splitJ J₁ * pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ = splitJ J₁
  have e1 : J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (u : Matrix n n R) = J₁ := by
    rw [Matrix.mul_assoc (J₁ * _) J₁⁻¹ J₁, Matrix.nonsing_inv_mul J₁ hJ, Matrix.mul_one, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  have hs : splitJ J₁ = pairMat J₁ J₁ᵀ := rfl
  rw [hs, pm_cT_lemma_2, pm_mul_lemma, pm_mul_lemma, Matrix.transpose_transpose, e1]
  congr 1
  calc (u : Matrix n n R)ᵀ * J₁ᵀ * (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ
      = (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (u : Matrix n n R))ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J₁ᵀ := by rw [e1]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[bc, splitLift, pairMat]`.
-/
theorem splitLift_fst (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (u : GL n R) :
    bc (RingHom.fst R R) (splitLift J₁ hJ u) = u := by
  apply Units.ext
  ext i j
  simp [bc, splitLift, pairMat]

/- English proof (translation)
Unfold `pairMat`. Conclude with `continuous_matrix fun i j => (hA.matrix_elem i j).prodMk (hB.matrix_elem i j)`.
-/
theorem continuous_pairMat [TopologicalSpace R] {X : Type} [TopologicalSpace X] {A B : X → Matrix n n R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => pairMat (A x) (B x) := by
  unfold pairMat
  exact continuous_matrix fun i j => (hA.matrix_elem i j).prodMk (hB.matrix_elem i j)

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Use `show Continuous fun u : GL n R => pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ`. Conclude with `continuous_pairMat Units.continuous_val (((continuous_const.matrix_mul Units.continuous_coe_inv).matrix_mul continuous_const).matrix_transpose)`. Use `show Continuous fun u : GL n R => pairMat ((u⁻¹ : GL n R) : Matrix n n R) (J₁ * (u : Matrix n n R) * J₁⁻¹)ᵀ`.

Conclude with `continuous_pairMat Units.continuous_coe_inv (((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const).matrix_transpose)`.
-/
theorem continuous_splitLift [TopologicalSpace R] [IsTopologicalRing R] (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) :
    Continuous (splitLift J₁ hJ) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun u : GL n R => pairMat (u : Matrix n n R) (J₁ * ((u⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ
    exact continuous_pairMat Units.continuous_val
      (((continuous_const.matrix_mul Units.continuous_coe_inv).matrix_mul continuous_const).matrix_transpose)
  · show Continuous fun u : GL n R => pairMat ((u⁻¹ : GL n R) : Matrix n n R) (J₁ * (u : Matrix n n R) * J₁⁻¹)ᵀ
    exact continuous_pairMat Units.continuous_coe_inv
      (((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const).matrix_transpose)

end Lift

/- English proof (translation)
Use `set K := v.adicCompletion F`. Use `letI : TopologicalSpace (E ⊗[F] K) := tensTopL (F := F) (E := E) K`. Establish `hsig : ∀ e : E, sigR σ K (inclE (F` using `F) K e) = inclE (F := F) K (σ e) := by`. Introduce `e`. Simplify using `[sigR, inclE, Algebra.TensorProduct.map_tmul]`.

Use `set J1 : Matrix (Fin k) (Fin k) K := (J.map ((s : E ⊗[F] K →+* K × K).comp (inclE (F := F) K))).map Prod.fst with hJ1def`. Establish `hJ' : J.map ((s : E ⊗[F] K →+* K × K).comp (inclE (F` using `F) K)) = splitJ J1 := by`. Use `Matrix.ext fun i j => Prod.ext rfl ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s (inclE (F := F) K (J i j))).2 = (s (inclE (F := F) K (J j i))).1`. Establish `hh : J i j = σ (J j i)` using `(congrFun (congrFun hJh i) j).symm`.

Rewrite using `[hh, ← hsig, hs]`. Both sides reduce to the same expression. Establish `hJ1 : IsUnit J1.det`. Establish `e : J1 = (RingHom.mapMatrix ((RingHom.fst K K).comp ((s : E ⊗[F] K →+* K × K).comp (inclE (F` using `F) K)))) J := by`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[e, ← RingHom.map_det]`. Conclude with `hdet.map _`. Use `set φ : E ⊗[F] K →+* K := (RingHom.fst K K).comp s.toRingHom with hφdef`. Set `θ : GL (Fin k) (E ⊗[F] K) →* GL (Fin k) K` to `(MulAut.conj h⁻¹).toMonoidHom.comp (bc φ)`.

Establish `hθ : ∀ x, θ x = h⁻¹ * bc φ x * h` using `fun x => by simp [θ, MulAut.conj_apply]`. Set `ψ : GL (Fin k) K → GL (Fin k) (E ⊗[F] K)` to `fun a => bc (s.symm : K × K →+* E ⊗[F] K) (splitLift J1 hJ1 (h * a * h⁻¹))`. Establish `hss : ∀ z : GL (Fin k) (E ⊗[F] K), bc (s.symm : K × K →+* E ⊗[F] K) (bc (s : E ⊗[F] K →+* K × K) z) = z` using `fun z => by apply Units.ext; ext i j; simp [bc]`. Establish `hφs : ∀ L : GL (Fin k) (K × K), bc φ (bc (s.symm : K × K →+* E ⊗[F] K) L) = bc (RingHom.fst K K) L` using `fun L => by apply Units.ext; ext i j; simp [bc, φ]`. Establish `hθψ : ∀ a, θ (ψ a) = a`.

Introduce `a`. Rewrite using `[hθ]`. Express the relevant statement in the definitionally equal form `h⁻¹ * bc φ (bc (s.symm : K × K →+* E ⊗[F] K) (splitLift J1 hJ1 (h * a * h⁻¹))) * h = a`. Rewrite using `[hφs, splitLift_fst]`. Use `group`.

Establish `hψU : ∀ a, ψ a ∈ UPts σ J K`. Introduce `a`. Establish `h1` using `splitLift_mem J1 hJ1 (h * a * h⁻¹)`. Rewrite `h1` using `[← hJ']`. Establish `hc : (s.symm : K × K →+* E ⊗[F] K).comp (swapR K) = (sigR σ K).comp (s.symm : K × K →+* E ⊗[F] K)` using `transport_symm_comp (sigR σ K) (swapR K) s (RingHom.ext hs)`.

Establish `h2` using `transport_bc_mem (swapR K) (sigR σ K) _ hc _ _ h1`. Establish `hJm : (J.map ((s : E ⊗[F] K →+* K × K).comp (inclE (F` using `F) K))).map (s.symm : K × K →+* E ⊗[F] K) = J.map (inclE (F := F) K) := by`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite `h2` using `[hJm]`.

Conclude with `h2`. Establish `hsJ : ∀ y ∈ UPts σ J K, bc (s : E ⊗[F] K →+* K × K) y ∈ UJ (swapR K) (splitJ J1)`. Introduce `y hy`. Rewrite using `[← hJ']`. Use `transport_bc_mem (sigR σ K) (swapR K) (s : E ⊗[F] K →+* K × K) (RingHom.ext hs) _ y hy` as an intermediate fact.

Rewrite `this` using `[Matrix.map_map]`. Then use the resulting hypothesis. Establish `hψθ : ∀ x ∈ UPts σ J K, ψ (θ x) = x`. Introduce `x hx`. Establish `e1 : bc φ (ψ (θ x)) = bc φ x`. Use `hθψ (θ x)` as an intermediate fact.

Rewrite `this` using `[hθ, hθ]`. Conclude with `mul_left_cancel (mul_right_cancel this)`. Establish `e2 : bc (s : E ⊗[F] K →+* K × K) (ψ (θ x)) = bc (s : E ⊗[F] K →+* K × K) x` using `split_injective J1 hJ1 _ _ (hsJ _ (hψU _)) (hsJ _ hx) (congrArg Units.val e1)`. Use `congrArg (bc (s.symm : K × K →+* E ⊗[F] K)) e2` as an intermediate fact. Rewrite `this` using `[hss, hss]`. Then use the resulting hypothesis.

Establish `hθc : Continuous θ`. Establish `hb : Continuous (bc (n` using `Fin k) φ) := Continuous.units_map _ (continuous_id.matrix_map (continuous_fst.comp hsc))`. Establish `: (θ : GL (Fin k) (E ⊗[F] K) → GL (Fin k) K) = fun x => h⁻¹ * bc φ x * h` using `funext hθ`. Rewrite using `[this]`. Conclude with `(continuous_const.mul hb).mul continuous_const`.

Establish `hψc : Continuous ψ`. Establish `hb : Continuous (bc (n` using `Fin k) (s.symm : K × K →+* E ⊗[F] K)) := Continuous.units_map _ (continuous_id.matrix_map hsic)`. Conclude with `hb.comp ((continuous_splitLift J1 hJ1).comp ((continuous_const.mul continuous_id).mul continuous_const))`. Use `isProGrp_transfer g θ hθc ψ hψc Uw P ?_ ?_ ?_ hP` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[hθ]`. Conclude with `(hiff x (hUw hx)).1 hx`. Introduce `p hp`. Establish `hm : ψ p ∈ Uw` using `(hiff (ψ p) (hψU p)).2 (by rw [← hθ, hθψ]; exact hp)`. Conclude with `⟨hm, hθψ p⟩`.

Introduce `x hx`. Conclude with `hψθ x (hUw hx)`.
-/
theorem proGTransfer_of_cont (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E) (hJh : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hs : ∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x))
    (hsc : letI := tensTopL (F := F) (E := E) (v.adicCompletion F); Continuous s)
    (hsic : letI := tensTopL (F := F) (E := E) (v.adicCompletion F); Continuous s.symm)
    (h : GL (Fin k) (v.adicCompletion F)) (P : Subgroup (GL (Fin k) (v.adicCompletion F)))
    (Uw : Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F))) (hUw : Uw ≤ UPts σ J (v.adicCompletion F))
    (hiff : ∀ x ∈ UPts σ J (v.adicCompletion F), x ∈ Uw ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) x * h ∈ P)
    (g : ℕ) (hP : IsProGrp g P) :
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F)
    IsProGrp g Uw := by
  set K := v.adicCompletion F
  letI : TopologicalSpace (E ⊗[F] K) := tensTopL (F := F) (E := E) K
  have hsig : ∀ e : E, sigR σ K (inclE (F := F) K e) = inclE (F := F) K (σ e) := by
    intro e
    simp [sigR, inclE, Algebra.TensorProduct.map_tmul]
  set J1 : Matrix (Fin k) (Fin k) K := (J.map ((s : E ⊗[F] K →+* K × K).comp (inclE (F := F) K))).map Prod.fst
    with hJ1def
  have hJ' : J.map ((s : E ⊗[F] K →+* K × K).comp (inclE (F := F) K)) = splitJ J1 := by
    refine Matrix.ext fun i j => Prod.ext rfl ?_
    change (s (inclE (F := F) K (J i j))).2 = (s (inclE (F := F) K (J j i))).1
    have hh : J i j = σ (J j i) := (congrFun (congrFun hJh i) j).symm
    rw [hh, ← hsig, hs]
    rfl
  have hJ1 : IsUnit J1.det := by
    have e : J1 = (RingHom.mapMatrix ((RingHom.fst K K).comp ((s : E ⊗[F] K →+* K × K).comp
        (inclE (F := F) K)))) J := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact hdet.map _
  set φ : E ⊗[F] K →+* K := (RingHom.fst K K).comp s.toRingHom with hφdef
  let θ : GL (Fin k) (E ⊗[F] K) →* GL (Fin k) K := (MulAut.conj h⁻¹).toMonoidHom.comp (bc φ)
  have hθ : ∀ x, θ x = h⁻¹ * bc φ x * h := fun x => by simp [θ, MulAut.conj_apply]
  let ψ : GL (Fin k) K → GL (Fin k) (E ⊗[F] K) :=
    fun a => bc (s.symm : K × K →+* E ⊗[F] K) (splitLift J1 hJ1 (h * a * h⁻¹))
  have hss : ∀ z : GL (Fin k) (E ⊗[F] K), bc (s.symm : K × K →+* E ⊗[F] K) (bc (s : E ⊗[F] K →+* K × K) z) = z :=
    fun z => by apply Units.ext; ext i j; simp [bc]
  have hφs : ∀ L : GL (Fin k) (K × K), bc φ (bc (s.symm : K × K →+* E ⊗[F] K) L) = bc (RingHom.fst K K) L :=
    fun L => by apply Units.ext; ext i j; simp [bc, φ]
  have hθψ : ∀ a, θ (ψ a) = a := by
    intro a
    rw [hθ]
    change h⁻¹ * bc φ (bc (s.symm : K × K →+* E ⊗[F] K) (splitLift J1 hJ1 (h * a * h⁻¹))) * h = a
    rw [hφs, splitLift_fst]
    group
  have hψU : ∀ a, ψ a ∈ UPts σ J K := by
    intro a
    have h1 := splitLift_mem J1 hJ1 (h * a * h⁻¹)
    rw [← hJ'] at h1
    have hc : (s.symm : K × K →+* E ⊗[F] K).comp (swapR K) = (sigR σ K).comp (s.symm : K × K →+* E ⊗[F] K) :=
      transport_symm_comp (sigR σ K) (swapR K) s (RingHom.ext hs)
    have h2 := transport_bc_mem (swapR K) (sigR σ K) _ hc _ _ h1
    have hJm : (J.map ((s : E ⊗[F] K →+* K × K).comp (inclE (F := F) K))).map
        (s.symm : K × K →+* E ⊗[F] K) = J.map (inclE (F := F) K) := by
      ext i j; simp
    rw [hJm] at h2
    exact h2
  have hsJ : ∀ y ∈ UPts σ J K, bc (s : E ⊗[F] K →+* K × K) y ∈ UJ (swapR K) (splitJ J1) := by
    intro y hy
    rw [← hJ']
    have := transport_bc_mem (sigR σ K) (swapR K) (s : E ⊗[F] K →+* K × K) (RingHom.ext hs) _ y hy
    rwa [Matrix.map_map] at this
  have hψθ : ∀ x ∈ UPts σ J K, ψ (θ x) = x := by
    intro x hx
    have e1 : bc φ (ψ (θ x)) = bc φ x := by
      have := hθψ (θ x)
      rw [hθ, hθ] at this
      exact mul_left_cancel (mul_right_cancel this)
    have e2 : bc (s : E ⊗[F] K →+* K × K) (ψ (θ x)) = bc (s : E ⊗[F] K →+* K × K) x :=
      split_injective J1 hJ1 _ _ (hsJ _ (hψU _)) (hsJ _ hx) (congrArg Units.val e1)
    have := congrArg (bc (s.symm : K × K →+* E ⊗[F] K)) e2
    rwa [hss, hss] at this
  have hθc : Continuous θ := by
    have hb : Continuous (bc (n := Fin k) φ) :=
      Continuous.units_map _ (continuous_id.matrix_map (continuous_fst.comp hsc))
    have : (θ : GL (Fin k) (E ⊗[F] K) → GL (Fin k) K) = fun x => h⁻¹ * bc φ x * h := funext hθ
    rw [this]; exact (continuous_const.mul hb).mul continuous_const
  have hψc : Continuous ψ := by
    have hb : Continuous (bc (n := Fin k) (s.symm : K × K →+* E ⊗[F] K)) :=
      Continuous.units_map _ (continuous_id.matrix_map hsic)
    exact hb.comp ((continuous_splitLift J1 hJ1).comp ((continuous_const.mul continuous_id).mul continuous_const))
  refine isProGrp_transfer g θ hθc ψ hψc Uw P ?_ ?_ ?_ hP
  · intro x hx; rw [hθ]; exact (hiff x (hUw hx)).1 hx
  · intro p hp
    have hm : ψ p ∈ Uw := (hiff (ψ p) (hψU p)).2 (by rw [← hθ, hθψ]; exact hp)
    exact ⟨hm, hθψ p⟩
  · intro x hx; exact hψθ x (hUw hx)

/- English proof (translation)
Use `letI : TopologicalSpace (E ⊗[F] v.adicCompletion F) := tensTopL (F := F) (E := E) (v.adicCompletion F)`. Use `letI : Algebra (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsModuleTopology (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (E ⊗[F] v.adicCompletion F) := IsModuleTopology.toContinuousAdd (R := v.adicCompletion F) (A := E ⊗[F] v.adicCompletion F)`. Set `sl : (E ⊗[F] v.adicCompletion F) ≃ₗ[v.adicCompletion F] (v.adicCompletion F × v.adicCompletion F)` to `{ s.toAddEquiv with map_smul' := fun r x => by show s (r • x) = r • s x`.

Rewrite using `[Algebra.smul_def, map_mul]`. Establish `h1 : s (algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) r) = (r, r)` using `halg r`. Rewrite using `[h1]`. Apply the tactic sequence `ext <;> simp }`. Conclude with `⟨IsModuleTopology.continuous_of_linearMap sl.toLinearMap, IsModuleTopology.continuous_of_linearMap sl.symm.toLinearMap⟩`.
-/
theorem split_cont (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F); Continuous s ∧ Continuous s.symm := by
  letI : TopologicalSpace (E ⊗[F] v.adicCompletion F) := tensTopL (F := F) (E := E) (v.adicCompletion F)
  letI : Algebra (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := ⟨rfl⟩
  haveI : ContinuousAdd (E ⊗[F] v.adicCompletion F) :=
    IsModuleTopology.toContinuousAdd (R := v.adicCompletion F) (A := E ⊗[F] v.adicCompletion F)
  let sl : (E ⊗[F] v.adicCompletion F) ≃ₗ[v.adicCompletion F] (v.adicCompletion F × v.adicCompletion F) :=
    { s.toAddEquiv with
      map_smul' := fun r x => by
        show s (r • x) = r • s x
        rw [Algebra.smul_def, map_mul]
        have h1 : s (algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) r) = (r, r) := halg r
        rw [h1]
        ext <;> simp }
  exact ⟨IsModuleTopology.continuous_of_linearMap sl.toLinearMap,
    IsModuleTopology.continuous_of_linearMap sl.symm.toLinearMap⟩

/- English proof (translation)
Unfold `Formalism.L2.G.Triv.ProGTransfer`. Introduce `F E _ _ _ _ _ k σ J hJh hdet v s hs halg h P Uw hUw hiff g hP`. Take `⟨h1, h2⟩` from `split_cont F E v s halg`. Conclude with `proGTransfer_of_cont F E k σ J hJh hdet v s hs h1 h2 h P Uw hUw hiff g hP`.
-/
theorem proGTransfer : Formalism.L2.G.Triv.ProGTransfer := by
  unfold Formalism.L2.G.Triv.ProGTransfer
  intro F E _ _ _ _ _ k σ J hJh hdet v s hs halg h P Uw hUw hiff g hP
  obtain ⟨h1, h2⟩ := split_cont F E v s halg
  exact proGTransfer_of_cont F E k σ J hJh hdet v s hs h1 h2 h P Uw hUw hiff g hP

section Link

def LocalEndHomeo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    Continuous τ ∧ ∃ τ' : v.adicCompletion F →+* v.adicCompletion F, Continuous τ' ∧ ∀ a, τ (τ' a) = a

/- English proof (translation)
Use `set K := v.adicCompletion F`. Use `letI : TopologicalSpace (E ⊗[F] K) := tensTopL (F := F) (E := E) K`. Use `letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩`. Use `haveI := IsModuleTopology.toContinuousAdd K (E ⊗[F] K)`.

Use `haveI := IsModuleTopology.toContinuousSMul K (E ⊗[F] K)`. Set `τ : K →+* K` to `(RingHom.fst K K).comp ((s : E ⊗[F] K →+* K × K).comp (algebraMap K (E ⊗[F] K)))`. Establish `hsig1 : ∀ a : K, sigR σ K (algebraMap K (E ⊗[F] K) a) = algebraMap K (E ⊗[F] K) a`. Introduce `a`. Express the relevant statement in the definitionally equal form `sigR σ K ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a`.

Simplify using `[sigR]`. Establish `hτ : ∀ a : K, s (algebraMap K (E ⊗[F] K) a) = (τ a, τ a)`. Introduce `a`. Establish `h1` using `hs (algebraMap K (E ⊗[F] K) a)`. Rewrite `h1` using `[hsig1]`.

Establish `h2 : (s (algebraMap K (E ⊗[F] K) a)).2 = (s (algebraMap K (E ⊗[F] K) a)).1` using `congrArg Prod.snd h1`. Conclude with `Prod.ext rfl h2`. Take `⟨hτc, τ', hτ'c, hττ'⟩` from `hE F v τ`. Prove the components needed by the constructor for the conclusion. Use `IsModuleTopology.continuous_of_ringHom (R := K) (s : E ⊗[F] K →+* K × K) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Continuous (fun a => s (algebraMap K (E ⊗[F] K) a))`. Establish `: (fun a => s (algebraMap K (E ⊗[F] K) a)) = fun a => (τ a, τ a)` using `funext hτ`. Rewrite using `[this]`. Conclude with `hτc.prodMk hτc`. Establish `hsym : ∀ c : K, s.symm (algebraMap K (K × K) c) = algebraMap K (E ⊗[F] K) (τ' c)`.

Introduce `c`. Rewrite using `[RingEquiv.symm_apply_eq, hτ, hττ']`. Both sides reduce to the same expression. Set `L : (K × K) →ₛₗ[τ'] E ⊗[F] K` to `{ toFun := s.symm map_add' := map_add s.symm map_smul' := fun c p => by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hsym] }`.

Conclude with `IsModuleTopology.continuous_of_linearMapₛₗ hτ'c L`.
-/
theorem split_cont_of_homeo (hE : LocalEndHomeo) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hs : ∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) :
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F); Continuous s ∧ Continuous s.symm := by
  set K := v.adicCompletion F
  letI : TopologicalSpace (E ⊗[F] K) := tensTopL (F := F) (E := E) K
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd K (E ⊗[F] K)
  haveI := IsModuleTopology.toContinuousSMul K (E ⊗[F] K)
  let τ : K →+* K := (RingHom.fst K K).comp ((s : E ⊗[F] K →+* K × K).comp (algebraMap K (E ⊗[F] K)))
  have hsig1 : ∀ a : K, sigR σ K (algebraMap K (E ⊗[F] K) a) = algebraMap K (E ⊗[F] K) a := by
    intro a
    change sigR σ K ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a
    simp [sigR]
  have hτ : ∀ a : K, s (algebraMap K (E ⊗[F] K) a) = (τ a, τ a) := by
    intro a
    have h1 := hs (algebraMap K (E ⊗[F] K) a)
    rw [hsig1] at h1
    have h2 : (s (algebraMap K (E ⊗[F] K) a)).2 = (s (algebraMap K (E ⊗[F] K) a)).1 := congrArg Prod.snd h1
    exact Prod.ext rfl h2
  obtain ⟨hτc, τ', hτ'c, hττ'⟩ := hE F v τ
  constructor
  · refine IsModuleTopology.continuous_of_ringHom (R := K) (s : E ⊗[F] K →+* K × K) ?_
    change Continuous (fun a => s (algebraMap K (E ⊗[F] K) a))
    have : (fun a => s (algebraMap K (E ⊗[F] K) a)) = fun a => (τ a, τ a) := funext hτ
    rw [this]
    exact hτc.prodMk hτc
  · have hsym : ∀ c : K, s.symm (algebraMap K (K × K) c) = algebraMap K (E ⊗[F] K) (τ' c) := by
      intro c
      rw [RingEquiv.symm_apply_eq, hτ, hττ']
      rfl
    let L : (K × K) →ₛₗ[τ'] E ⊗[F] K :=
      { toFun := s.symm
        map_add' := map_add s.symm
        map_smul' := fun c p => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, hsym] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ hτ'c L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `i v h` and use `by obtain ⟨hsc, hsic⟩ := split_cont_of_homeo hE F E sp.cm.sig v (L.splitG i v h) (L.splitG_sig i v h) exact proGTransfer_of_cont F E R.k sp.cm.sig sp.gram0 sp.baseGram_isHermitian (Formalism.L2.G.isUnit_det_gram0 sp) v (L.splitG i v h) (L.splitG_sig i v h) hsc hsic (L.frG i v h) …`.
-/
theorem colProG (hE : LocalEndHomeo) {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime) : L.ProG := fun i v h => by
  obtain ⟨hsc, hsic⟩ := split_cont_of_homeo hE F E sp.cm.sig v (L.splitG i v h) (L.splitG_sig i v h)
  exact proGTransfer_of_cont F E R.k sp.cm.sig sp.gram0 sp.baseGram_isHermitian (Formalism.L2.G.isUnit_det_gram0 sp) v
    (L.splitG i v h) (L.splitG_sig i v h) hsc hsic (L.frG i v h) (iwU F R.k v) (L.Uloc v) (L.Uloc_le v)
    (L.Uloc_g i v h) (gp i) (iwProG F R.k v (gp i) (hp i) h)

/- English proof (translation)
Introduce `D Lv u` and use `colProG hE (Lv u) D.host.g_prime`.
-/
theorem levels_pro_g_of_continuity (hE : LocalEndHomeo) : Link4p :=
  fun D Lv u => colProG hE (Lv u) D.host.g_prime

def SplitGAlg (D : D7) (Lv : LevelData D) : Prop :=
  ∀ (u : D.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (a : v.adicCompletion D.host.F),
    (Lv u).splitG i v h ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)

/- English proof (translation)
The claim follows from `Formalism.L2.G.Triv.proper_of_split_completion iwProG proGTransfer D Lv h`.
-/
theorem levels_pro_g_of_split_algebra (D : D7) (Lv : LevelData D) (h : SplitGAlg D Lv) : Formalism.MainNotions.StandardLattice.Conclusion4p D Lv :=
  Formalism.L2.G.Triv.proper_of_split_completion iwProG proGTransfer D Lv h

end Link

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ProGW

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
The claim follows from `ProGW.iwProG`.
-/
theorem iwahori_pro_g : Formalism.L2.G.Triv.IwProG := ProGW.iwProG

/- English proof (translation)
The claim follows from `ProGW.proGTransfer`.
-/
theorem pro_g_transfer_unitary : Formalism.L2.G.Triv.ProGTransfer := ProGW.proGTransfer

/- English proof (translation)
The claim follows from `ProGW.levels_pro_g_of_continuity hE`.
-/
theorem Link4p_of_localEndHomeo (hE : ProGW.LocalEndHomeo) : Link4p := ProGW.levels_pro_g_of_continuity hE

/- English proof (translation)
The claim follows from `ProGW.levels_pro_g_of_split_algebra D Lv h`.
-/
theorem levels_pro_g_of_split_algebra (D : Formalism.BasicNotions.D7) (Lv : Formalism.BasicNotions.LevelData D) (h : ProGW.SplitGAlg D Lv) :
    Formalism.MainNotions.StandardLattice.Conclusion4p D Lv := ProGW.levels_pro_g_of_split_algebra D Lv h

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
