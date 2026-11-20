import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne

open Filter Topology ValuativeRel

noncomputable section

namespace GlobalTheory.LinSchurLatt

/- English proof (translation)
Establish `hre : ∀ m : ℕ, 1 / 2 ≤ (z ^ m).re`. Introduce `m`. Establish `h1` using `(Complex.abs_re_le_norm (z ^ m - 1)).trans (h m)`. Rewrite `h1` using `[Complex.sub_re, Complex.one_re]`. Combine the linear relations using `[(abs_le.1 h1).1]`.

Establish `hS : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ m ∈ Finset.range N, z ^ m‖`. Introduce `N`. Use `le_trans ?_ (Complex.re_le_norm _)` and prove the remaining obligations. Rewrite using `[Complex.re_sum]`. Combine the equalities or inequalities in the displayed calculation.

Assume the negation of the conclusion as `hz`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hz)`. Take `⟨N, hN⟩` from `exists_nat_gt (1 / ‖z - 1‖)`. Establish `e` using `geom_sum_mul z N`. Establish `h2 : ‖z - 1‖ * ((N : ℝ) / 2) ≤ 1 / 2`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hN` using `[div_lt_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eq_one_of_pow_near (z : ℂ) (h : ∀ m : ℕ, ‖z ^ m - 1‖ ≤ 1 / 2) : z = 1 := by
  have hre : ∀ m : ℕ, 1 / 2 ≤ (z ^ m).re := by
    intro m
    have h1 := (Complex.abs_re_le_norm (z ^ m - 1)).trans (h m)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_le.1 h1).1]
  have hS : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ m ∈ Finset.range N, z ^ m‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ m ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun m _ => hre m
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have e := geom_sum_mul z N
  have h2 : ‖z - 1‖ * ((N : ℝ) / 2) ≤ 1 / 2 := by
    calc ‖z - 1‖ * ((N : ℝ) / 2) ≤ ‖z - 1‖ * ‖∑ m ∈ Finset.range N, z ^ m‖ :=
          mul_le_mul_of_nonneg_left (hS N) hpos.le
      _ = ‖z ^ N - 1‖ := by rw [← e, norm_mul, mul_comm]
      _ ≤ 1 / 2 := h N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `(Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)`.
-/
theorem valuation_natCast_le_one (m : ℕ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)

/- English proof (translation)
Establish `hO : IsCompact {x : k | valuation k x ≤ 1}` using `IsNonarchimedeanLocalField.isCompact_closedBall k 1`. Establish `hU : {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} ∈ 𝓝 (0 : k)`. Establish `h1 : Metric.closedBall (ψ0 0) (1 / 2) ∈ 𝓝 (ψ0 0)` using `Metric.closedBall_mem_nhds _ (by norm_num)`. Use `filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with u hu`. Simplify `hu` using `[Metric.mem_closedBall, dist_eq_norm, AddChar.map_zero_eq_one]`.

Establish `hev : ∀ᶠ w in 𝓝 (0 : k), ∀ a ∈ {x : k | valuation k x ≤ 1}, a * w ∈ {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2}`. Use `hO.eventually_forall_of_forall_eventually fun a _ => ?_` and prove the remaining obligations. Establish `hcm : Continuous fun z : k × k => z.2 * z.1` using `continuous_snd.mul continuous_fst`. Establish `h0 : (fun z : k × k => z.2 * z.1) (0, a) = 0` using `by simp`. Conclude with `hcm.continuousAt.preimage_mem_nhds (by simpa using hU)`.

Use `filter_upwards [hev] with w hw o ho`. Apply `eq_one_of_pow_near` to reduce the goal to its premises. Introduce `m`. Establish `hmo : valuation k ((m : k) * o) ≤ 1`. Rewrite using `[map_mul]`.

Conclude with `mul_le_one' (valuation_natCast_le_one m) ho`. Establish `h1` using `hw _ hmo`. Establish `h2 : (m : k) * o * w = m • (o * w)` using `by rw [nsmul_eq_mul, mul_assoc]`. Rewrite `h1` using `[h2, AddChar.map_nsmul_eq_pow]`. Then use the resulting hypothesis.
-/
theorem ker_int_mem_nhds (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) :
    {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} ∈ 𝓝 (0 : k) := by
  have hO : IsCompact {x : k | valuation k x ≤ 1} := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hU : {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} ∈ 𝓝 (0 : k) := by
    have h1 : Metric.closedBall (ψ0 0) (1 / 2) ∈ 𝓝 (ψ0 0) := Metric.closedBall_mem_nhds _ (by norm_num)
    filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with u hu
    simpa [Metric.mem_closedBall, dist_eq_norm, AddChar.map_zero_eq_one] using hu
  have hev : ∀ᶠ w in 𝓝 (0 : k), ∀ a ∈ {x : k | valuation k x ≤ 1}, a * w ∈ {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have hcm : Continuous fun z : k × k => z.2 * z.1 := continuous_snd.mul continuous_fst
    have h0 : (fun z : k × k => z.2 * z.1) (0, a) = 0 := by simp
    exact hcm.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [hev] with w hw o ho
  apply eq_one_of_pow_near
  intro m
  have hmo : valuation k ((m : k) * o) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' (valuation_natCast_le_one m) ho
  have h1 := hw _ hmo
  have h2 : (m : k) * o * w = m • (o * w) := by rw [nsmul_eq_mul, mul_assoc]
  rwa [h2, AddChar.map_nsmul_eq_pow] at h1

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Apply `ht` to reduce the goal to its premises.

Establish `: t = 0` using `by simpa using h`. Rewrite using `[this, AddChar.map_zero_eq_one]`. Establish `hvu : valuation k u ≠ 0` using `by simpa using hu0`. Apply `ht` to reduce the goal to its premises. Establish `hle : valuation k (t / u) ≤ 1`.

Rewrite using `[map_div₀, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation. Use `hu (t / u) hle` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hu0]`. Then use the resulting hypothesis.
-/
theorem ker_int_lt {ψ0 : AddChar k ℂ} {t : k} (ht : ψ0 t ≠ 1) {u : k}
    (hu : ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1) : valuation k u < valuation k t := by
  by_contra h
  push_neg at h
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply ht
    have : t = 0 := by simpa using h
    rw [this, AddChar.map_zero_eq_one]
  have hvu : valuation k u ≠ 0 := by simpa using hu0
  apply ht
  have hle : valuation k (t / u) ≤ 1 := by
    rw [map_div₀, div_eq_mul_inv]
    calc valuation k t * (valuation k u)⁻¹ ≤ valuation k u * (valuation k u)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hvu
  have := hu (t / u) hle
  rwa [div_mul_cancel₀ _ hu0] at this

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `letI : (Valued.v (R := k)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Conclude with `NormedField.nhdsNE_neBot (0 : k)`.
-/
theorem nhdsNE_neBot' : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

/- English proof (translation)
Establish `: {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} = Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ}`. Use extensionality with `x`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ`.
-/
theorem isCompact_ball_mat (n d : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} := by
  have : {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} =
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

/- English proof (translation)
Establish `hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ 1}, c • x ∈ W`. Use `(isCompact_ball_mat n d 1).eventually_forall_of_forall_eventually fun y _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2` using `continuous_fst.smul continuous_snd`. Establish `h0 : (fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2) (0, y) = 0` using `by simp`. Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa using hW)`.

Use `haveI := nhdsNE_neBot' (k := k)`. Take `⟨c, hc1, hc2⟩` from `((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists`. Conclude with `⟨c, hc2, fun x hx => hc1 x hx⟩`.
-/
theorem exists_smul_int_mem' (n d : ℕ) (W : Set (Matrix (Fin n) (Fin d) k)) (hW : W ∈ 𝓝 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) k, (∀ i j, valuation k (x i j) ≤ 1) → c • x ∈ W := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ 1}, c • x ∈ W := by
    refine (isCompact_ball_mat n d 1).eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have h0 : (fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2) (0, y) = 0 := by simp
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  haveI := nhdsNE_neBot' (k := k)
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and
    (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

end GlobalTheory.LinSchurLatt

namespace GlobalTheory.LinSchurLatt

/- English proof (translation)
Introduce `k _ _ _ _ n d ψ0 hc hne`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, ψ0 t ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])`.

Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `ht (AddChar.map_zero_eq_one ψ0)`. Establish `hvt : valuation k t ≠ 0` using `by simpa using ht0`. Establish `hK` using `ker_int_mem_nhds ψ0 hc`.

Use `⟨fun s hs => ⟨?_, ?_⟩, fun W hW => ?_⟩` and prove the remaining obligations. Apply `AddSubgroup.isOpen_of_mem_nhds (g := 0)` to reduce the goal to its premises. Establish `hev : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ i j, s * Y i j ∈ {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1}`. Use `eventually_all.2 fun i => eventually_all.2 fun j => ?_` and prove the remaining obligations. Establish `hcont : Continuous fun Y : Matrix (Fin n) (Fin d) k => s * Y i j` using `continuous_const.mul (continuous_id.matrix_elem i j)`.

Conclude with `hcont.continuousAt.preimage_mem_nhds (by simpa using hK)`. Use `filter_upwards [hev] with Y hY`. Conclude with `GlobalTheory.LinSchur.mem_latt.2 fun i j o ho => hY i j o ho`. Establish `hsub : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ valuation k t * (valuation k s)⁻¹}`. Introduce `Y hY i j`.

Establish `h1` using `ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho`. Establish `hvs : valuation k s ≠ 0` using `by simpa using hs`. Rewrite `h1` using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (valuation k s), mul_assoc, mul_inv_cancel₀ hvs, mul_one]`.

Use `_ ≤ valuation k t * (valuation k s)⁻¹ := by gcongr`. Establish `hcl : IsClosed (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))`. Establish `e : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) = ⋂ i, ⋂ j, ⋂ o : {o : k // valuation k o ≤ 1}, {Y | ψ0 (o.1 * (s * Y i j)) = 1}`. Use extensionality with `Y`. Simplify using `only [SetLike.mem_coe, GlobalTheory.LinSchur.mem_latt, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]`.

Rewrite using `[e]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun o => isClosed_eq (hc.comp (continuous_const.mul (continuous_const.mul (continuous_id.matrix_elem i j)))) continuous_const`. Conclude with `(isCompact_ball_mat n d _).of_isClosed_subset hcl hsub`. Take `⟨c, hc0, hcW⟩` from `exists_smul_int_mem' n d W hW`. Use `⟨t / c, div_ne_zero ht0 hc0, fun Y hY => ?_⟩` and prove the remaining obligations.

Establish `hx : ∀ i j, valuation k ((c⁻¹ • Y) i j) ≤ 1`. Introduce `i j`. Establish `h1` using `ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho`. Establish `e : (c⁻¹ • Y) i j = (t / c * Y i j) * t⁻¹`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_mul, map_inv₀]`. Combine the equalities or inequalities in the displayed calculation. Use `hcW _ hx` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_inv_cancel₀ hc0, one_smul]`. Then use the resulting hypothesis.
-/
theorem latt_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  intro k _ _ _ _ n d ψ0 hc hne
  obtain ⟨t, ht⟩ : ∃ t, ψ0 t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ0)
  have hvt : valuation k t ≠ 0 := by simpa using ht0
  have hK := ker_int_mem_nhds ψ0 hc
  refine ⟨fun s hs => ⟨?_, ?_⟩, fun W hW => ?_⟩
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hev : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ i j,
        s * Y i j ∈ {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} := by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      have hcont : Continuous fun Y : Matrix (Fin n) (Fin d) k => s * Y i j :=
        continuous_const.mul (continuous_id.matrix_elem i j)
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    filter_upwards [hev] with Y hY
    exact GlobalTheory.LinSchur.mem_latt.2 fun i j o ho => hY i j o ho
  · have hsub : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆
        {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ valuation k t * (valuation k s)⁻¹} := by
      intro Y hY i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have hvs : valuation k s ≠ 0 := by simpa using hs
      rw [map_mul] at h1
      calc valuation k (Y i j) = valuation k s * valuation k (Y i j) * (valuation k s)⁻¹ := by
            rw [mul_comm (valuation k s), mul_assoc, mul_inv_cancel₀ hvs, mul_one]
        _ ≤ valuation k t * (valuation k s)⁻¹ := by gcongr
    have hcl : IsClosed (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) := by
      have e : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) =
          ⋂ i, ⋂ j, ⋂ o : {o : k // valuation k o ≤ 1}, {Y | ψ0 (o.1 * (s * Y i j)) = 1} := by
        ext Y
        simp only [SetLike.mem_coe, GlobalTheory.LinSchur.mem_latt, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
      rw [e]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun o =>
        isClosed_eq (hc.comp (continuous_const.mul (continuous_const.mul (continuous_id.matrix_elem i j))))
          continuous_const
    exact (isCompact_ball_mat n d _).of_isClosed_subset hcl hsub
  · obtain ⟨c, hc0, hcW⟩ := exists_smul_int_mem' n d W hW
    refine ⟨t / c, div_ne_zero ht0 hc0, fun Y hY => ?_⟩
    have hx : ∀ i j, valuation k ((c⁻¹ • Y) i j) ≤ 1 := by
      intro i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have e : (c⁻¹ • Y) i j = (t / c * Y i j) * t⁻¹ := by
        rw [Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [e, map_mul, map_inv₀]
      calc valuation k (t / c * Y i j) * (valuation k t)⁻¹ ≤ valuation k t * (valuation k t)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvt
    have := hcW _ hx
    rwa [smul_smul, mul_inv_cancel₀ hc0, one_smul] at this

end GlobalTheory.LinSchurLatt
