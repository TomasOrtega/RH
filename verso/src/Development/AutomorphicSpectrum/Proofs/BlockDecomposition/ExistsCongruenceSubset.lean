import Mathlib

open ValuativeRel Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance`. Establish `h1 : 1 < a⁻¹` using `(one_lt_inv₀ (zero_lt_iff.2 ha0)).2 ha`. Take `⟨n, hn⟩` from `MulArchimedean.arch γ⁻¹ h1`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h2 : a ^ n ≤ γ`.

Rewrite `hn` using `[inv_pow]`. Conclude with `(inv_le_inv₀ (zero_lt_iff.2 hγ) (zero_lt_iff.2 (pow_ne_zero n ha0))).1 hn`. Conclude with `lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha n.lt_succ_self) h2`.
-/
theorem exists_pow_succ_lt {a γ : ValueGroupWithZero k} (ha0 : a ≠ 0) (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ (m + 1) < γ := by
  haveI : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h1 : 1 < a⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 ha0)).2 ha
  obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ h1
  refine ⟨n, ?_⟩
  have h2 : a ^ n ≤ γ := by
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.2 hγ) (zero_lt_iff.2 (pow_ne_zero n ha0))).1 hn
  exact lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha n.lt_succ_self) h2

/- English proof (translation)
Use `set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) - 1 with hA`. Use `set B : Matrix (Fin N) (Fin N) k := ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 with hB`. Establish `hAle : ∀ i j, valuation k (A i j) ≤ t` using `fun i j => by simpa [hA] using hg i j`. Establish `hrel : B = -A - A * B`. Establish `hgh : (g : Matrix (Fin N) (Fin N) k) * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hg' : (g : Matrix (Fin N) (Fin N) k) = A + 1` using `by simp [hA]`. Establish `hh' : ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = B + 1` using `by simp [hB]`. Rewrite `hgh` using `[hg', hh']`. Establish `: (A + 1) * (B + 1) = A * B + A + B + 1` using `by noncomm_ring`.

Rewrite `hgh` using `[this]`. Establish `h3 : A * B + A + B = 0` using `by simpa using hgh`. Rewrite using `[eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h3]`. Normalize the expressions using the abelian group laws. Use `show valuation k (B i j) ≤ t`.

Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_le]`. Take `⟨⟨i₀, j₀⟩, -, hmax⟩` from `Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N)) (fun p => valuation k (B p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩`. Use `set M := valuation k (B i₀ j₀) with hM`. Establish `hMt : t < M` using `lt_of_lt_of_le hcon (hmax (i, j) (Finset.mem_univ _))`.

Establish `hM0 : 0 < M` using `lt_of_le_of_lt zero_le' hMt`. Establish `hprod : valuation k ((A * B) i₀ j₀) ≤ t * M`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_le_mul' (hAle _ _) (hmax (l, j₀) (Finset.mem_univ _))`. Establish `htM : t * M < M`. Simplify using `using mul_lt_mul_of_pos_right ht hM0`. Establish `hent : B i₀ j₀ = -A i₀ j₀ - (A * B) i₀ j₀` using `by conv_lhs => rw [hrel]`. Simplify using the standard rewrite rules.

Establish `: M < M`. Combine the equalities or inequalities in the displayed calculation. Use `max_lt ?_ (lt_of_le_of_lt hprod htM)` and prove the remaining obligations. Rewrite using `[Valuation.map_neg]`. Conclude with `lt_of_le_of_lt (hAle _ _) hMt`.

Conclude with `lt_irrefl _ this`.
-/
theorem inv_mem_of_mem {N : ℕ} {t : ValueGroupWithZero k} (ht : t < 1) (g : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t) (i j : Fin N) :
    valuation k (((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) - 1 with hA
  set B : Matrix (Fin N) (Fin N) k := ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 with hB
  have hAle : ∀ i j, valuation k (A i j) ≤ t := fun i j => by simpa [hA] using hg i j
  have hrel : B = -A - A * B := by
    have hgh : (g : Matrix (Fin N) (Fin N) k) * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg' : (g : Matrix (Fin N) (Fin N) k) = A + 1 := by simp [hA]
    have hh' : ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = B + 1 := by simp [hB]
    rw [hg', hh'] at hgh
    have : (A + 1) * (B + 1) = A * B + A + B + 1 := by noncomm_ring
    rw [this] at hgh
    have h3 : A * B + A + B = 0 := by simpa using hgh
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h3]
    abel
  show valuation k (B i j) ≤ t
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => valuation k (B p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  set M := valuation k (B i₀ j₀) with hM
  have hMt : t < M := lt_of_lt_of_le hcon (hmax (i, j) (Finset.mem_univ _))
  have hM0 : 0 < M := lt_of_le_of_lt zero_le' hMt
  have hprod : valuation k ((A * B) i₀ j₀) ≤ t * M := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hAle _ _) (hmax (l, j₀) (Finset.mem_univ _))
  have htM : t * M < M := by
    simpa using mul_lt_mul_of_pos_right ht hM0
  have hent : B i₀ j₀ = -A i₀ j₀ - (A * B) i₀ j₀ := by
    conv_lhs => rw [hrel]
    simp
  have : M < M := by
    calc M = valuation k (-A i₀ j₀ - (A * B) i₀ j₀) := by rw [hM, ← hent]
      _ ≤ max (valuation k (-A i₀ j₀)) (valuation k ((A * B) i₀ j₀)) := Valuation.map_sub _ _ _
      _ < M := by
        refine max_lt ?_ (lt_of_le_of_lt hprod htM)
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt (hAle _ _) hMt
  exact lt_irrefl _ this

/- English proof (translation)
Introduce `k _ _ _ _ N ϖ hϖ0 hϖ1 _ U hU`. Use `set a := valuation k ϖ with ha`. Establish `ha0 : a ≠ 0` using `(Valuation.ne_zero_iff _).2 hϖ0`. Set `K : ℕ → Set (GL (Fin N) k)` to `fun m => {g | ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)}`. Establish `hanti : Antitone K` using `fun m n hmn g hg i j => (hg i j).trans (pow_le_pow_of_le_one zero_le' hϖ1.le (by omega))`.

Establish `hbasis : (⨅ m, 𝓟 (K m)).HasBasis (fun _ => True) K` using `hasBasis_iInf_principal hanti.directed_ge`. Establish `hent : ∀ (i j : Fin N) (c : GL (Fin N) k → k), (∀ m, ∀ g ∈ K m, valuation k (c g - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)) → Tendsto c (⨅ m, 𝓟 (K m)) (𝓝 ((1 : Matrix (Fin N) (Fin N) k) i j))`. Introduce `i j c hc`. Rewrite using `[(IsValuativeTopology.hasBasis_nhds' _).tendsto_right_iff]`. Introduce `γ hγ`.

Take `⟨m, hm⟩` from `exists_pow_succ_lt ha0 hϖ1 hγ`. Conclude with `hbasis.eventually_iff.2 ⟨m, trivial, fun g hg => lt_of_le_of_lt (hc m g hg) hm⟩`. Establish `hlim : Tendsto (id : GL (Fin N) k → GL (Fin N) k) (⨅ m, 𝓟 (K m)) (𝓝 1)`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `Tendsto.prodMk_nhds ?_ ?_` and prove the remaining obligations.

Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Conclude with `hent i j _ fun m g hg => hg i j`. Use `(MulOpposite.continuous_op.tendsto _).comp ?_` and prove the remaining obligations. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Conclude with `hent i j (fun g => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) fun m g hg => inv_mem_of_mem (pow_lt_one₀ zero_le' hϖ1 (by omega)) g hg i j`.

Take `⟨m, -, hm⟩` from `hbasis.mem_iff.1 (hlim hU)`. Use `⟨m + 1, by omega, fun g hg => hm fun i j => ?_⟩` and prove the remaining obligations. Simplify `hg i j` using `[ha, map_pow]`.
-/
theorem exists_congruence_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k), ϖ ≠ 0 →
    ValuativeRel.valuation k (ϖ) < 1 →
    (∀ x : k, ValuativeRel.valuation k (x) < 1 →
      ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) →
    ∀ U : Set (GL (Fin N) k), U ∈ nhds (1 : GL (Fin N) k) →
    ∃ m : ℕ, 1 ≤ m ∧ {g : GL (Fin N) k | ∀ i j,
      ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)} ⊆ U := by
  intro k _ _ _ _ N ϖ hϖ0 hϖ1 _ U hU
  set a := valuation k ϖ with ha
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  let K : ℕ → Set (GL (Fin N) k) := fun m => {g | ∀ i j,
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)}
  have hanti : Antitone K := fun m n hmn g hg i j =>
    (hg i j).trans (pow_le_pow_of_le_one zero_le' hϖ1.le (by omega))
  have hbasis : (⨅ m, 𝓟 (K m)).HasBasis (fun _ => True) K :=
    hasBasis_iInf_principal hanti.directed_ge
  have hent : ∀ (i j : Fin N) (c : GL (Fin N) k → k), (∀ m, ∀ g ∈ K m, valuation k (c g - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)) →
      Tendsto c (⨅ m, 𝓟 (K m)) (𝓝 ((1 : Matrix (Fin N) (Fin N) k) i j)) := by
    intro i j c hc
    rw [(IsValuativeTopology.hasBasis_nhds' _).tendsto_right_iff]
    intro γ hγ
    obtain ⟨m, hm⟩ := exists_pow_succ_lt ha0 hϖ1 hγ
    exact hbasis.eventually_iff.2 ⟨m, trivial, fun g hg => lt_of_le_of_lt (hc m g hg) hm⟩
  have hlim : Tendsto (id : GL (Fin N) k → GL (Fin N) k) (⨅ m, 𝓟 (K m)) (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ?_
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j _ fun m g hg => hg i j
    · refine (MulOpposite.continuous_op.tendsto _).comp ?_
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j (fun g => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) fun m g hg =>
        inv_mem_of_mem (pow_lt_one₀ zero_le' hϖ1 (by omega)) g hg i j
  obtain ⟨m, -, hm⟩ := hbasis.mem_iff.1 (hlim hU)
  refine ⟨m + 1, by omega, fun g hg => hm fun i j => ?_⟩
  simpa [ha, map_pow] using hg i j

end GlobalTheory.CompanionTheory.CongruenceBasis
