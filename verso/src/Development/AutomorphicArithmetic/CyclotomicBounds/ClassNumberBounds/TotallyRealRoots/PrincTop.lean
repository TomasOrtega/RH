import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[mem_princ, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]`.
-/
private theorem mem_princ_iff_norm {a : ℕ} {u : ℤ_[l]ˣ} :
    u ∈ princ l a ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-a : ℤ) := by
  rw [mem_princ, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Establish `h1 : Units.val '' s ∈ nhds ((1 : ℤ_[l]ˣ) : ℤ_[l])` using `Units.isOpenEmbedding_val.isOpenMap.image_mem_nhds hs`. Simplify using `only [Units.val_one] at h1`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.mp h1`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Take `⟨a, ha⟩` from `exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)`.

Use `⟨a, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hu' : (u : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) ε`. Rewrite using `[Metric.mem_ball, dist_eq_norm]`. Use `lt_of_le_of_lt (mem_princ_iff_norm.mp hu) ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]` and apply the resulting hypothesis.

Take `⟨v, hv, hvu⟩` from `hball hu'`. Rewrite using `[← Units.val_injective hvu]` and apply the resulting hypothesis.
-/
private theorem exists_princ_subset {s : Set ℤ_[l]ˣ} (hs : s ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ a, (princ l a : Set ℤ_[l]ˣ) ⊆ s := by
  have h1 : Units.val '' s ∈ nhds ((1 : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.isOpenEmbedding_val.isOpenMap.image_mem_nhds hs
  simp only [Units.val_one] at h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  refine ⟨a, fun u hu => ?_⟩
  have hu' : (u : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (mem_princ_iff_norm.mp hu) ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨v, hv, hvu⟩ := hball hu'
  rwa [← Units.val_injective hvu]

/- English proof (translation)
Establish `hr : ((l : ℝ) ^ (-a : ℤ)) ≠ 0` using `(zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _).ne'`. Establish `hset : (princ l a : Set ℤ_[l]ˣ) = Units.val ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-a : ℤ))`. Use extensionality with `u`. Simplify using `only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]`. Conclude with `mem_princ_iff_norm`.

Establish `hopen : IsOpen (princ l a : Set ℤ_[l]ˣ)`. Rewrite using `[hset]`. Conclude with `Units.continuous_val.isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hr)`. Conclude with `hopen`.
-/
theorem isOpen_princ (a : ℕ) : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
  have hr : ((l : ℝ) ^ (-a : ℤ)) ≠ 0 :=
    (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _).ne'
  have hset : (princ l a : Set ℤ_[l]ˣ) =
      Units.val ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-a : ℤ)) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    exact mem_princ_iff_norm
  have hopen : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
    rw [hset]
    exact Units.continuous_val.isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hr)
  exact hopen

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `exists_princ_subset (h.mem_nhds U.one_mem)`. Introduce and unpack `⟨a, ha⟩`. Conclude with `Subgroup.isOpen_mono ha (isOpen_princ a)`.
-/
theorem isOpen_iff_princ_le (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ ∃ a, princ l a ≤ U := by
  constructor
  · intro h
    exact exists_princ_subset (h.mem_nhds U.one_mem)
  · rintro ⟨a, ha⟩
    exact Subgroup.isOpen_mono ha (isOpen_princ a)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨U.isClosed_of_isOpen h, ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(isOpen_iff_princ_le U).mp h`. Use `haveI : (princ l a).FiniteIndex := Subgroup.finiteIndex_ker (redPow l a)`.

Conclude with `Subgroup.finiteIndex_of_le ha`. Introduce and unpack `⟨hc, hf⟩`. Conclude with `U.isOpen_of_isClosed_of_finiteIndex hc`.
-/
theorem isOpen_iff_isClosed_finiteIndex (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ IsClosed (U : Set ℤ_[l]ˣ) ∧ U.FiniteIndex := by
  constructor
  · intro h
    refine ⟨U.isClosed_of_isOpen h, ?_⟩
    obtain ⟨a, ha⟩ := (isOpen_iff_princ_le U).mp h
    haveI : (princ l a).FiniteIndex := Subgroup.finiteIndex_ker (redPow l a)
    exact Subgroup.finiteIndex_of_le ha
  · rintro ⟨hc, hf⟩
    exact U.isOpen_of_isClosed_of_finiteIndex hc

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, ← hU.closure_eq, mem_closure_iff_nhds]`. Introduce `t ht`. Establish `ht' : (fun y => x * y) ⁻¹' t ∈ nhds (1 : ℤ_[l]ˣ)`. Apply `(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using ht`.

Take `⟨b, hb⟩` from `exists_princ_subset ht'`. Take `⟨u, hu, hux⟩` from `h b`. Establish `hmem : x⁻¹ * u ∈ princ l b` using `by show x⁻¹ * u ∈ (redPow l b).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]`. Use `⟨u, ?_, hu⟩` and prove the remaining obligations.

Use `hb hmem` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_of_isClosed {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {x : ℤ_[l]ˣ}
    (h : ∀ b, ∃ u ∈ U, redPow l b u = redPow l b x) : x ∈ U := by
  rw [← SetLike.mem_coe, ← hU.closure_eq, mem_closure_iff_nhds]
  intro t ht
  have ht' : (fun y => x * y) ⁻¹' t ∈ nhds (1 : ℤ_[l]ˣ) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using ht
  obtain ⟨b, hb⟩ := exists_princ_subset ht'
  obtain ⟨u, hu, hux⟩ := h b
  have hmem : x⁻¹ * u ∈ princ l b := by
    show x⁻¹ * u ∈ (redPow l b).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
  refine ⟨u, ?_, hu⟩
  have := hb hmem
  simpa using this

end KStar.TotallyRealRoots
