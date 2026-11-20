import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Establish `key : ∃ K0 : Subgroup H, K0.FiniteIndex ∧ ∀ (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)], K ≤ K0 → ∑ q : H ⧸ K, ρ q.out w = 0` using `by clear hfix`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w h`. Take `⟨x, m, rfl⟩` from `h`. Take `⟨K0, h0, h1⟩` from `hs m`.

Use `⟨K0, h0, fun K _ _ hK => ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub]`. Rewrite using `[Finset.sum_sub_distrib, sub_eq_zero, ← Equiv.sum_comp (Equiv.mulRight (x : H ⧸ K)) (fun q : H ⧸ K => ρ q.out m)]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `h2 : ((q * x).out)⁻¹ * (q.out * x) ∈ K`.

Rewrite using `[← QuotientGroup.eq]`. Simplify using the standard rewrite rules. Establish `h3` using `h1 _ (hK h2)`. Establish `h4 : q.out * x = (q * x).out * (((q * x).out)⁻¹ * (q.out * x))` using `by group`. Rewrite using `[Equiv.coe_mulRight, ← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]`.

Consider the case `zero => exact ⟨⊤, inferInstance, fun K _ _ _ => by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨K1, h1, h1'⟩` from `ha`. Take `⟨K2, h2, h2'⟩` from `hb`. Use `⟨K1 ⊓ K2, inferInstance, fun K _ _ hK => ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add]`. Rewrite using `[Finset.sum_add_distrib, h1' K (hK.trans inf_le_left), h2' K (hK.trans inf_le_right), add_zero]`. Consider the case `smul c a _ ha`. Take `⟨K1, h1, h1'⟩` from `ha`. Use `⟨K1, h1, fun K _ _ hK => ?_⟩` and prove the remaining obligations.

Simplify using `only [map_smul]`. Rewrite using `[← Finset.smul_sum, h1' K hK, smul_zero]`. Take `⟨K0, h0, h1⟩` from `key`. Use `haveI : Fintype (H ⧸ K0.normalCore) := Fintype.ofFinite _`. Establish `h2` using `h1 K0.normalCore K0.normalCore_le`.

Simplify using `only [hfix, Finset.sum_const, Finset.card_univ] at h2`. Rewrite `h2` using `[← Nat.cast_smul_eq_nsmul k, smul_eq_zero]`. Conclude with `h2.resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)`.
-/
private theorem UpperTheory.V.Hi.propCker_avg {H k M : Type} [Group H] [Field k] [CharZero k] [AddCommGroup M] [Module k M]
    (ρ : Representation k H M) (hs : ∀ m, ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ x ∈ K, ρ x m = m) {w : M}
    (hw : w ∈ Submodule.span k {w | ∃ x m, w = ρ x m - m}) (hfix : ∀ x, ρ x w = w) : w = 0 := by
  have key : ∃ K0 : Subgroup H, K0.FiniteIndex ∧ ∀ (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)], K ≤ K0 →
      ∑ q : H ⧸ K, ρ q.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨x, m, rfl⟩ := h
      obtain ⟨K0, h0, h1⟩ := hs m
      refine ⟨K0, h0, fun K _ _ hK => ?_⟩
      simp only [map_sub]
      rw [Finset.sum_sub_distrib, sub_eq_zero,
        ← Equiv.sum_comp (Equiv.mulRight (x : H ⧸ K)) (fun q : H ⧸ K => ρ q.out m)]
      refine Finset.sum_congr rfl fun q _ => ?_
      have h2 : ((q * x).out)⁻¹ * (q.out * x) ∈ K := by
        rw [← QuotientGroup.eq]
        simp
      have h3 := h1 _ (hK h2)
      have h4 : q.out * x = (q * x).out * (((q * x).out)⁻¹ * (q.out * x)) := by group
      rw [Equiv.coe_mulRight, ← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]
    | zero => exact ⟨⊤, inferInstance, fun K _ _ _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨K1, h1, h1'⟩ := ha
      obtain ⟨K2, h2, h2'⟩ := hb
      refine ⟨K1 ⊓ K2, inferInstance, fun K _ _ hK => ?_⟩
      simp only [map_add]
      rw [Finset.sum_add_distrib, h1' K (hK.trans inf_le_left), h2' K (hK.trans inf_le_right), add_zero]
    | smul c a _ ha =>
      obtain ⟨K1, h1, h1'⟩ := ha
      refine ⟨K1, h1, fun K _ _ hK => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, h1' K hK, smul_zero]
  obtain ⟨K0, h0, h1⟩ := key
  haveI : Fintype (H ⧸ K0.normalCore) := Fintype.ofFinite _
  have h2 := h1 K0.normalCore K0.normalCore_le
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_zero] at h2
  exact h2.resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/- English proof (translation)
Introduce `G _ I k M _ _ _ _ π hsm v hv`. Establish `mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w` using `fun g h w => by`. Rewrite using `[map_mul π g h, Module.End.mul_apply]`. Establish `hz : ∀ j : ℕ, I.z ^ j ∈ I.P` using `fun j => pow_mem I.z_mem j`. Establish `hpow : ∀ j : ℕ, (I.uOp π I.z ^ j) v = I.uOp π (I.z ^ j) v`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simpa using (uOpMul G I k M π 1 1 (one_mem _) (one_mem _) v hv).2.2.1.symm`. Consider the case `succ j ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, pow_succ', (uOpMul G I k M π _ _ I.z_mem (hz j) v hv).2.1]`.

Simplify using `only [hpow]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Set `ρ : Representation k I.N M` to `π.comp I.N.subtype`. Set `J : Submodule k M` to `Submodule.span k {w | ∃ x m, w = ρ x m - m}`.

Establish `key : ∃ j0 : ℕ, ∀ j ≥ j0, π (I.z ^ j) v ∈ J` using `by clear hv hpow`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem w h`. Take `⟨x, hx, m, rfl⟩` from `h`. Take `⟨j0, h0⟩` from `I.exh x hx`.

Use `⟨j0, fun j hj => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le' hj`. Establish `h1` using `I.P_N _ (hz d) _ h0`. Use `Submodule.subset_span ⟨⟨_, h1⟩, π (I.z ^ (d + j0)) m, ?_⟩` and prove the remaining obligations. Use `show _ = π _ _ - _`.

Rewrite using `[map_sub, mul, mul]`. Use `congr 3`. Simplify using `only [Subgroup.subtype_apply]`. Use `group`. Consider the case `zero => exact ⟨0, fun j _ => by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨j1, h1⟩` from `ha`. Take `⟨j2, h2⟩` from `hb`. Use `⟨max j1 j2, fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`.

Conclude with `add_mem (h1 j (le_of_max_le_left hj)) (h2 j (le_of_max_le_right hj))`. Consider the case `smul c a _ ha`. Take `⟨j1, h1⟩` from `ha`. Use `⟨j1, fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`.

Conclude with `Submodule.smul_mem _ _ (h1 j hj)`. Take `⟨j, hj⟩` from `key`. Establish `hj` using `hj j le_rfl`. Use `⟨j, propCker_avg ρ ?_ ?_ ?_⟩` and prove the remaining obligations. Introduce `m`.

Take `⟨c, hc, -⟩` from `hsm m`. Conclude with `⟨(I.Nconj (I.z ^ c)).subgroupOf I.N, ⟨I.fin_N _ (hz c)⟩, fun x hx => hc x hx⟩`. Establish `hfin : ((I.Nconj (I.z ^ j)).subgroupOf I.N).FiniteIndex` using `⟨I.fin_N _ (hz j)⟩ haveI : Fintype (I.N ⧸ (I.Nconj (I.z ^ j)).subgroupOf I.N) := Fintype.ofFinite _`. Rewrite using `[Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations.

Establish `h1 : ρ q.out (π (I.z ^ j) v) - π (I.z ^ j) v ∈ J` using `Submodule.subset_span ⟨_, _, rfl⟩`. Establish `h2` using `add_mem h1 hj`. Rewrite `h2` using `[sub_add_cancel]`. Rewrite using `[← mul]`. Conclude with `h2`.

Introduce `x`. Conclude with `(uOpMul G I k M π _ 1 (hz j) (one_mem _) v hv).1 x x.2`. Introduce and unpack `⟨j, hj⟩`. Establish `h1` using `propCp G I k M π _ (hz j) v hv`. Rewrite `h1` using `[hj, zero_sub, neg_mem_iff, Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 (I.fin_N _ (hz j)))]`.

Establish `stab : ∀ t ∈ I.Tf, ∀ w ∈ I.jacKer π, π t w ∈ I.jacKer π`. Introduce `t ht w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w h`. Take `⟨x, hx, m, rfl⟩` from `h`.

Use `Submodule.subset_span ⟨_, I.Tf_Nf t ht x hx, π t m, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, mul, mul]`. Use `congr 3`. Use `group`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ ha`. Establish `h2` using `stab _ (inv_mem (I.P_le _ (hz j))) _ h1`.

Rewrite `h2` using `[mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Hi.propCker :
    ∀ (G : Type) [Group G] (I : Iwa G) (k M : Type) [Field k] [CharZero k] [AddCommGroup M] [Module k M] (π : Representation k G M), I.Smooth π → ∀ v ∈ fixd π I.N, v ∈ I.jacKer π ↔ ∃ j : ℕ, (I.uOp π I.z ^ j) v = 0 := by
  intro G _ I k M _ _ _ _ π hsm v hv
  have mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  have hz : ∀ j : ℕ, I.z ^ j ∈ I.P := fun j => pow_mem I.z_mem j
  have hpow : ∀ j : ℕ, (I.uOp π I.z ^ j) v = I.uOp π (I.z ^ j) v := by
    intro j
    induction j with
    | zero => simpa using (uOpMul G I k M π 1 1 (one_mem _) (one_mem _) v hv).2.2.1.symm
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ',
        (uOpMul G I k M π _ _ I.z_mem (hz j) v hv).2.1]
  simp only [hpow]
  constructor
  · intro h
    let ρ : Representation k I.N M := π.comp I.N.subtype
    let J : Submodule k M := Submodule.span k {w | ∃ x m, w = ρ x m - m}
    have key : ∃ j0 : ℕ, ∀ j ≥ j0, π (I.z ^ j) v ∈ J := by
      clear hv hpow
      induction h using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, hx, m, rfl⟩ := h
        obtain ⟨j0, h0⟩ := I.exh x hx
        refine ⟨j0, fun j hj => ?_⟩
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hj
        have h1 := I.P_N _ (hz d) _ h0
        refine Submodule.subset_span ⟨⟨_, h1⟩, π (I.z ^ (d + j0)) m, ?_⟩
        show _ = π _ _ - _
        rw [map_sub, mul, mul]
        congr 3
        simp only [Subgroup.subtype_apply]
        group
      | zero => exact ⟨0, fun j _ => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨j1, h1⟩ := ha
        obtain ⟨j2, h2⟩ := hb
        refine ⟨max j1 j2, fun j hj => ?_⟩
        rw [map_add]
        exact add_mem (h1 j (le_of_max_le_left hj)) (h2 j (le_of_max_le_right hj))
      | smul c a _ ha =>
        obtain ⟨j1, h1⟩ := ha
        refine ⟨j1, fun j hj => ?_⟩
        rw [map_smul]
        exact Submodule.smul_mem _ _ (h1 j hj)
    obtain ⟨j, hj⟩ := key
    have hj := hj j le_rfl
    refine ⟨j, propCker_avg ρ ?_ ?_ ?_⟩
    · intro m
      obtain ⟨c, hc, -⟩ := hsm m
      exact ⟨(I.Nconj (I.z ^ c)).subgroupOf I.N, ⟨I.fin_N _ (hz c)⟩, fun x hx => hc x hx⟩
    · have hfin : ((I.Nconj (I.z ^ j)).subgroupOf I.N).FiniteIndex := ⟨I.fin_N _ (hz j)⟩
      haveI : Fintype (I.N ⧸ (I.Nconj (I.z ^ j)).subgroupOf I.N) := Fintype.ofFinite _
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun q _ => ?_
      have h1 : ρ q.out (π (I.z ^ j) v) - π (I.z ^ j) v ∈ J := Submodule.subset_span ⟨_, _, rfl⟩
      have h2 := add_mem h1 hj
      rw [sub_add_cancel] at h2
      rw [← mul]
      exact h2
    · intro x
      exact (uOpMul G I k M π _ 1 (hz j) (one_mem _) v hv).1 x x.2
  · rintro ⟨j, hj⟩
    have h1 := propCp G I k M π _ (hz j) v hv
    rw [hj, zero_sub, neg_mem_iff, Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 (I.fin_N _ (hz j)))] at h1
    have stab : ∀ t ∈ I.Tf, ∀ w ∈ I.jacKer π, π t w ∈ I.jacKer π := by
      intro t ht w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, hx, m, rfl⟩ := h
        refine Submodule.subset_span ⟨_, I.Tf_Nf t ht x hx, π t m, ?_⟩
        rw [map_sub, mul, mul]
        congr 3
        group
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
    have h2 := stab _ (inv_mem (I.P_le _ (hz j))) _ h1
    rwa [mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
