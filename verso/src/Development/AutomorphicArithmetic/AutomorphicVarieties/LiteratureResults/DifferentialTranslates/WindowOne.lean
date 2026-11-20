import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Set Topology Filter

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Use `⟨fun n => Metric.closedBall (0:V) n \ Metric.thickening (1/((n:ℝ)+1)) Yᶜ, fun n => Metric.ball (0:V) ((n:ℝ)+1) \ Metric.cthickening (1/((n:ℝ)+2)) Yᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n`. Conclude with `(isCompact_closedBall _ _).diff Metric.isOpen_thickening`. Introduce `n x hx dsimp only at hx`. Assume the negation of the conclusion as `h`.

Conclude with `hx.2 (Metric.self_subset_thickening (by positivity) _ h)`. Introduce `n`. Conclude with `Metric.isOpen_ball.sdiff Metric.isClosed_cthickening`. Introduce `n x hx dsimp only at hx ⊢`. Use `⟨?_, fun h => hx.2 (Metric.cthickening_subset_thickening' (by positivity) (one_div_lt_one_div_of_lt (by positivity) (by linarith)) _ h)⟩` and prove the remaining obligations.

Establish `h1` using `hx.1`. Rewrite `h1` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `n x hx dsimp only at hx ⊢`.

Use `⟨?_, fun h => hx.2 (Metric.thickening_subset_cthickening _ _ ?_)⟩` and prove the remaining obligations. Establish `h1` using `hx.1`. Rewrite `h1` using `[Metric.mem_ball]`. Rewrite using `[Metric.mem_closedBall]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (((n+1 : ℕ) : ℝ) + 1) = (n:ℝ) + 2` using `by push_cast; ring`. Rewrite `h` using `[e]`. Conclude with `h`. Introduce `p hp`.

Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.mp hY p hp`. Take `⟨n, hn⟩` from `exists_nat_gt (max ‖p‖ (1/ε))`. Use `⟨n, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `(le_max_left _ _).trans hn.le`.

Rewrite using `[Metric.mem_thickening_iff]`. Introduce and unpack `⟨y, hy, hd⟩`. Apply `hy` to reduce the goal to its premises. Apply `hb` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, dist_comm]`.

Use `hd.trans ?_` and prove the remaining obligations. Establish `h1 : 1/ε < n` using `(le_max_right _ _).trans_lt hn`. Rewrite `h1` using `[div_lt_iff₀ hε]`. Rewrite using `[div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem exists_compact_open_exhaustion_of_isOpen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Set V) (hY : IsOpen Y) :
    ∃ K O : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ Y) ∧ (∀ n, IsOpen (O n)) ∧
      (∀ n, K n ⊆ O n) ∧ (∀ n, O n ⊆ K (n+1)) ∧ ∀ p ∈ Y, ∃ n, p ∈ K n := by
  refine ⟨fun n => Metric.closedBall (0:V) n \ Metric.thickening (1/((n:ℝ)+1)) Yᶜ,
    fun n => Metric.ball (0:V) ((n:ℝ)+1) \ Metric.cthickening (1/((n:ℝ)+2)) Yᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (isCompact_closedBall _ _).diff Metric.isOpen_thickening
  · intro n x hx
    dsimp only at hx
    by_contra h
    exact hx.2 (Metric.self_subset_thickening (by positivity) _ h)
  · intro n
    exact Metric.isOpen_ball.sdiff Metric.isClosed_cthickening
  · intro n x hx
    dsimp only at hx ⊢
    refine ⟨?_, fun h => hx.2 (Metric.cthickening_subset_thickening' (by positivity)
      (one_div_lt_one_div_of_lt (by positivity) (by linarith)) _ h)⟩
    have h1 := hx.1
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    linarith
  · intro n x hx
    dsimp only at hx ⊢
    refine ⟨?_, fun h => hx.2 (Metric.thickening_subset_cthickening _ _ ?_)⟩
    · have h1 := hx.1
      rw [Metric.mem_ball] at h1
      rw [Metric.mem_closedBall]
      push_cast
      linarith
    · have e : (((n+1 : ℕ) : ℝ) + 1) = (n:ℝ) + 2 := by push_cast; ring
      rw [e] at h
      exact h
  · intro p hp
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hY p hp
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖p‖ (1/ε))
    refine ⟨n, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_left _ _).trans hn.le
    · rw [Metric.mem_thickening_iff]
      rintro ⟨y, hy, hd⟩
      apply hy
      apply hb
      rw [Metric.mem_ball, dist_comm]
      refine hd.trans ?_
      have h1 : 1/ε < n := (le_max_right _ _).trans_lt hn
      rw [div_lt_iff₀ hε] at h1
      rw [div_lt_iff₀ (by positivity)]
      nlinarith

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hS hP`. Break down `isEmpty_or_nonempty S with hE | ⟨⟨s₀⟩⟩` into its components or cases. Conclude with `⟨fun _ => ∅, fun s => isEmptyElim s, fun s => isEmptyElim s, fun s => isEmptyElim s⟩`. Establish `hmul : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x)` using `fun a b x => by`. Rewrite using `[map_mul, ContinuousLinearMap.mul_apply]`.

Establish `hfin : ∀ K ⊆ G.Y, IsCompact K → {γ : Γ | ∃ p ∈ K, G.ρ γ p ∈ K}.Finite` using `fun K hK hKc => (hP K hK hKc s₀ s₀).subset (fun γ h => ⟨Subsingleton.elim _ _, h⟩)`. Establish `hball : ∀ p ∈ G.Y, ∃ r > 0, Metric.closedBall p r ⊆ G.Y`. Introduce `p hp`. Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.mp G.isOpen p hp`. Conclude with `⟨ε/2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hb⟩`.

Establish `hsat : ∀ C ⊆ G.Y, IsCompact C → ∀ p ∈ G.Y, (¬ ∃ γ, G.ρ γ p ∈ C) → ∀ᶠ x in 𝓝 p, ¬ ∃ γ, G.ρ γ x ∈ C`. Introduce `C hC hCc p hp hn`. Take `⟨r, hr, hrY⟩` from `hball p hp`. Establish `hF` using `hfin _ (Set.union_subset hrY hC) ((isCompact_closedBall p r).union hCc)`. Establish `h1 : ∀ᶠ x in 𝓝 p, x ∈ Metric.closedBall p r` using `Metric.closedBall_mem_nhds p hr`.

Establish `h2 : ∀ᶠ x in 𝓝 p, ∀ γ ∈ {γ : Γ | ∃ q ∈ Metric.closedBall p r ∪ C, G.ρ γ q ∈ Metric.closedBall p r ∪ C}, G.ρ γ x ∉ C`. Rewrite using `[Filter.eventually_all_finite hF]`. Introduce `γ _`. Establish `ho : IsOpen ((G.ρ γ) ⁻¹' C)ᶜ` using `(hCc.isClosed.preimage (G.ρ γ).continuous).isOpen_compl`. Conclude with `ho.mem_nhds (fun h => hn ⟨γ, h⟩)`.

Use `filter_upwards [h1, h2] with x hx1 hx2`. Introduce and unpack `⟨γ, hγ⟩`. Conclude with `hx2 γ ⟨x, Or.inl hx1, Or.inr hγ⟩ hγ`. Take `⟨K, O, hKc, hKY, hOo, hKO, hOK, hcov⟩` from `exists_compact_open_exhaustion_of_isOpen G.Y G.isOpen`. Establish `hmono : Monotone K` using `monotone_nat_of_le_succ (fun n => (hKO n).trans (hOK n))`.

Establish `hOY : ∀ n, O n ⊆ G.Y` using `fun n => (hOK n).trans (hKY (n+1))`. Establish `hmin : ∀ p ∈ G.Y, ∃ n γ, G.ρ γ p ∈ K n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ p ∈ K m`. Introduce `p hp`. Establish `hx : ∃ n, ∃ γ, G.ρ γ p ∈ K n`. Take `⟨n, hn⟩` from `hcov p hp`.

Conclude with `⟨n, 1, by rwa [map_one, ContinuousLinearMap.one_apply]⟩`. Take `⟨γ, hγ⟩` from `Nat.find_spec hx`. Conclude with `⟨Nat.find hx, γ, hγ, fun m hm => Nat.find_min hx hm⟩`. Set `W0 : Set V` to `⋃ n, {q | q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m}`. Use `⟨fun _ => W0, fun s => ⟨?_, ?_⟩, fun s p hp => ?_, fun s p hp => ?_⟩` and prove the remaining obligations.

Use `show IsOpen W0`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `q hq`. Take `⟨n, hqn⟩` from `Set.mem_iUnion.mp hq`. Establish `hq' : q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m` using `hqn`.

Establish `hA : ∀ᶠ x in 𝓝 q, x ∈ O n` using `(hOo n).mem_nhds hq'.1`. Establish `hB : ∀ᶠ x in 𝓝 q, ∀ m ∈ Set.Iio n, ¬ ∃ γ, G.ρ γ x ∈ K m`. Rewrite using `[Filter.eventually_all_finite (Set.finite_Iio n)]`. Introduce `m hm`. Conclude with `hsat (K m) (hKY m) (hKc m) q (hOY n hq'.1) (hq'.2 m hm)`.

Use `filter_upwards [hA, hB] with x hx1 hx2`. Conclude with `Set.mem_iUnion.mpr ⟨n, hx1, fun m hm => hx2 m hm⟩`. Use `show W0 ⊆ G.Y`. Conclude with `Set.iUnion_subset (fun n q hq => hOY n hq.1)`. Take `⟨n, γ, hγ, hm⟩` from `hmin p hp`.

Use `⟨γ⁻¹, ?_⟩` and prove the remaining obligations. Use `show G.ρ γ⁻¹⁻¹ p ∈ W0`. Rewrite using `[inv_inv]`. Conclude with `Set.mem_iUnion.mpr ⟨n, hKO n hγ, fun m hm' ⟨δ, hδ⟩ => hm m hm' ⟨δ * γ, by rw [hmul]; exact hδ⟩⟩`. Take `⟨n, γ, hγ, -⟩` from `hmin p hp`.

Take `⟨r, hr, hrY⟩` from `hball p hp`. Establish `hF` using `hfin _ (Set.union_subset hrY (hKY (n+2))) ((isCompact_closedBall p r).union (hKc (n+2)))`. Use `⟨Metric.closedBall p r ∩ (G.ρ γ) ⁻¹' (O n), Filter.inter_mem (Metric.closedBall_mem_nhds p hr) (((hOo n).preimage (G.ρ γ).continuous).mem_nhds (hKO n hγ)), ?_⟩` and prove the remaining obligations. Use `(hF.preimage (f := fun g : Γ => g⁻¹) (fun _ _ _ _ h => inv_injective h)).subset ?_` and prove the remaining obligations. Introduce and unpack `δ ⟨x, ⟨hx1, hx2⟩, hxW⟩`.

Take `⟨k, hk1, hk2⟩` from `Set.mem_iUnion.mp hxW`. Establish `hkn : k ≤ n + 1`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `hk2 (n+1) hlt ⟨γ * δ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmul, ← hmul δ δ⁻¹ x, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Conclude with `hOK n hx2`. Conclude with `⟨x, Or.inl hx1, Or.inr (hmono (by omega : k + 1 ≤ n + 2) (hOK k hk1))⟩`.
-/
theorem windowOne : WindowOne := by
  intro Γ V S _ _ _ _ d G hS hP
  rcases isEmpty_or_nonempty S with hE | ⟨⟨s₀⟩⟩
  · exact ⟨fun _ => ∅, fun s => isEmptyElim s, fun s => isEmptyElim s, fun s => isEmptyElim s⟩
  have hmul : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x) := fun a b x => by
    rw [map_mul, ContinuousLinearMap.mul_apply]
  have hfin : ∀ K ⊆ G.Y, IsCompact K → {γ : Γ | ∃ p ∈ K, G.ρ γ p ∈ K}.Finite := fun K hK hKc =>
    (hP K hK hKc s₀ s₀).subset (fun γ h => ⟨Subsingleton.elim _ _, h⟩)
  have hball : ∀ p ∈ G.Y, ∃ r > 0, Metric.closedBall p r ⊆ G.Y := by
    intro p hp
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp G.isOpen p hp
    exact ⟨ε/2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hb⟩
  have hsat : ∀ C ⊆ G.Y, IsCompact C → ∀ p ∈ G.Y, (¬ ∃ γ, G.ρ γ p ∈ C) →
      ∀ᶠ x in 𝓝 p, ¬ ∃ γ, G.ρ γ x ∈ C := by
    intro C hC hCc p hp hn
    obtain ⟨r, hr, hrY⟩ := hball p hp
    have hF := hfin _ (Set.union_subset hrY hC) ((isCompact_closedBall p r).union hCc)
    have h1 : ∀ᶠ x in 𝓝 p, x ∈ Metric.closedBall p r := Metric.closedBall_mem_nhds p hr
    have h2 : ∀ᶠ x in 𝓝 p, ∀ γ ∈ {γ : Γ | ∃ q ∈ Metric.closedBall p r ∪ C,
        G.ρ γ q ∈ Metric.closedBall p r ∪ C}, G.ρ γ x ∉ C := by
      rw [Filter.eventually_all_finite hF]
      intro γ _
      have ho : IsOpen ((G.ρ γ) ⁻¹' C)ᶜ := (hCc.isClosed.preimage (G.ρ γ).continuous).isOpen_compl
      exact ho.mem_nhds (fun h => hn ⟨γ, h⟩)
    filter_upwards [h1, h2] with x hx1 hx2
    rintro ⟨γ, hγ⟩
    exact hx2 γ ⟨x, Or.inl hx1, Or.inr hγ⟩ hγ
  obtain ⟨K, O, hKc, hKY, hOo, hKO, hOK, hcov⟩ := exists_compact_open_exhaustion_of_isOpen G.Y G.isOpen
  have hmono : Monotone K := monotone_nat_of_le_succ (fun n => (hKO n).trans (hOK n))
  have hOY : ∀ n, O n ⊆ G.Y := fun n => (hOK n).trans (hKY (n+1))
  have hmin : ∀ p ∈ G.Y, ∃ n γ, G.ρ γ p ∈ K n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ p ∈ K m := by
    intro p hp
    classical
    have hx : ∃ n, ∃ γ, G.ρ γ p ∈ K n := by
      obtain ⟨n, hn⟩ := hcov p hp
      exact ⟨n, 1, by rwa [map_one, ContinuousLinearMap.one_apply]⟩
    obtain ⟨γ, hγ⟩ := Nat.find_spec hx
    exact ⟨Nat.find hx, γ, hγ, fun m hm => Nat.find_min hx hm⟩
  let W0 : Set V := ⋃ n, {q | q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m}
  refine ⟨fun _ => W0, fun s => ⟨?_, ?_⟩, fun s p hp => ?_, fun s p hp => ?_⟩
  · show IsOpen W0
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨n, hqn⟩ := Set.mem_iUnion.mp hq
    have hq' : q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m := hqn
    have hA : ∀ᶠ x in 𝓝 q, x ∈ O n := (hOo n).mem_nhds hq'.1
    have hB : ∀ᶠ x in 𝓝 q, ∀ m ∈ Set.Iio n, ¬ ∃ γ, G.ρ γ x ∈ K m := by
      rw [Filter.eventually_all_finite (Set.finite_Iio n)]
      intro m hm
      exact hsat (K m) (hKY m) (hKc m) q (hOY n hq'.1) (hq'.2 m hm)
    filter_upwards [hA, hB] with x hx1 hx2
    exact Set.mem_iUnion.mpr ⟨n, hx1, fun m hm => hx2 m hm⟩
  · show W0 ⊆ G.Y
    exact Set.iUnion_subset (fun n q hq => hOY n hq.1)
  · obtain ⟨n, γ, hγ, hm⟩ := hmin p hp
    refine ⟨γ⁻¹, ?_⟩
    show G.ρ γ⁻¹⁻¹ p ∈ W0
    rw [inv_inv]
    exact Set.mem_iUnion.mpr ⟨n, hKO n hγ, fun m hm' ⟨δ, hδ⟩ => hm m hm' ⟨δ * γ, by rw [hmul]; exact hδ⟩⟩
  · obtain ⟨n, γ, hγ, -⟩ := hmin p hp
    obtain ⟨r, hr, hrY⟩ := hball p hp
    have hF := hfin _ (Set.union_subset hrY (hKY (n+2))) ((isCompact_closedBall p r).union (hKc (n+2)))
    refine ⟨Metric.closedBall p r ∩ (G.ρ γ) ⁻¹' (O n),
      Filter.inter_mem (Metric.closedBall_mem_nhds p hr)
        (((hOo n).preimage (G.ρ γ).continuous).mem_nhds (hKO n hγ)), ?_⟩
    refine (hF.preimage (f := fun g : Γ => g⁻¹) (fun _ _ _ _ h => inv_injective h)).subset ?_
    rintro δ ⟨x, ⟨hx1, hx2⟩, hxW⟩
    obtain ⟨k, hk1, hk2⟩ := Set.mem_iUnion.mp hxW
    have hkn : k ≤ n + 1 := by
      by_contra hlt
      push_neg at hlt
      refine hk2 (n+1) hlt ⟨γ * δ, ?_⟩
      rw [hmul, ← hmul δ δ⁻¹ x, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
      exact hOK n hx2
    exact ⟨x, Or.inl hx1, Or.inr (hmono (by omega : k + 1 ≤ n + 2) (hOK k hk1))⟩

end UpperTheory.V.Lit.Dr
