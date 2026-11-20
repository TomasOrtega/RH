import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open Module

section
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

omit [IsAlgClosed K] in
/- English proof (translation)
Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (S.domRestrict U)`. Rewrite `h1` using `[LinearMap.range_domRestrict]`. Establish `h2 : LinearMap.ker (S.domRestrict U) ≠ ⊥` using `(Submodule.ne_bot_iff _).mpr ⟨⟨v, hv⟩, by simpa using hS, fun h => hv0 (congrArg Subtype.val h)⟩`. Establish `h3 : finrank K (LinearMap.ker (S.domRestrict U)) ≠ 0` using `fun h => h2 (Submodule.finrank_eq_zero.mp h)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem finrank_map_lt (U : Submodule K M) (S : Module.End K M) (v : M) (hv : v ∈ U) (hv0 : v ≠ 0)
    (hS : S v = 0) : finrank K (U.map S) < finrank K U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (S.domRestrict U)
  rw [LinearMap.range_domRestrict] at h1
  have h2 : LinearMap.ker (S.domRestrict U) ≠ ⊥ := (Submodule.ne_bot_iff _).mpr
    ⟨⟨v, hv⟩, by simpa using hS, fun h => hv0 (congrArg Subtype.val h)⟩
  have h3 : finrank K (LinearMap.ker (S.domRestrict U)) ≠ 0 := fun h => h2 (Submodule.finrank_eq_zero.mp h)
  omega

end

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by simpa using hy))`.
-/
private theorem sub_le_one' {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by simpa using hy))

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by simpa using hy))`.
-/
private theorem sub_lt_one' {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by simpa using hy))

private def bdd {I : Type} (V : Submodule K (I → K)) : Submodule K V where
  carrier := {v | ∃ c : K, c ≠ 0 ∧ ∀ n, ‖(c • v).1 n‖ ≤ 1}
  zero_mem' := ⟨1, one_ne_zero, fun n => by simp⟩
  add_mem' := by
    have key : ∀ (c e x : K), e ≠ 0 → ‖c‖ ≤ ‖e‖ → ‖e * x‖ ≤ 1 → ‖c * x‖ ≤ 1 := by
      intro c e x _ hce hx
      rw [norm_mul] at hx ⊢
      exact (mul_le_mul_of_nonneg_right hce (norm_nonneg _)).trans hx
    rintro v w ⟨c, hc, hv⟩ ⟨e, he, hw⟩
    rcases le_total ‖c‖ ‖e‖ with h | h
    · refine ⟨c, hc, fun n => ?_⟩
      have : (c • (v + w)).1 n = c * v.1 n + c * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv n) (key c e _ he h (hw n)))
    · refine ⟨e, he, fun n => ?_⟩
      have : (e • (v + w)).1 n = e * v.1 n + e * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key e c _ hc h (hv n)) (hw n))
  smul_mem' := by
    rintro s v ⟨c, hc, hv⟩
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, fun n => by simp [hs]⟩
    · refine ⟨c / s, div_ne_zero hc hs, fun n => ?_⟩
      rw [smul_smul, div_mul_cancel₀ c hs]
      exact hv n

omit [IsUltrametricDist K] in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hk : ∀ k : ℕ, ∀ n, ‖(c ^ k • v).1 n‖ ≤ 1`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hv`. Consider the case `succ k ih`. Use `hT _ ih` as an intermediate fact. Rewrite `this` using `[map_smul, hc, smul_smul, ← pow_succ]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, v.1 n ≠ 0 := by`.

Assume the negation of the conclusion as `h'`. Use `push Not at h'`. Conclude with `hv0 (Subtype.ext (funext h'))`. Establish `hpos : 0 < ‖v.1 n‖` using `norm_pos_iff.mpr hn`. Take `⟨k, hk'⟩` from `pow_unbounded_of_one_lt (‖v.1 n‖⁻¹) h`.

Establish `h1` using `hk k n`. Establish `h2 : (c ^ k • v).1 n = c ^ k * v.1 n` using `by simp`. Rewrite `h1` using `[h2, norm_mul, norm_pow]`. Establish `h3` using `mul_lt_mul_of_pos_right hk' hpos`. Rewrite `h3` using `[inv_mul_cancel₀ hpos.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem eig_le_one {I : Type} {V : Submodule K (I → K)} (T : Module.End K V)
    (hT : ∀ v : V, (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T v).1 n‖ ≤ 1) (v : V) (hv0 : v ≠ 0) (hv : ∀ n, ‖v.1 n‖ ≤ 1)
    (c : K) (hc : T v = c • v) : ‖c‖ ≤ 1 := by
  by_contra h
  push Not at h
  have hk : ∀ k : ℕ, ∀ n, ‖(c ^ k • v).1 n‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have := hT _ ih
      rwa [map_smul, hc, smul_smul, ← pow_succ] at this
  obtain ⟨n, hn⟩ : ∃ n, v.1 n ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv0 (Subtype.ext (funext h'))
  have hpos : 0 < ‖v.1 n‖ := norm_pos_iff.mpr hn
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (‖v.1 n‖⁻¹) h
  have h1 := hk k n
  have h2 : (c ^ k • v).1 n = c ^ k * v.1 n := by simp
  rw [h2, norm_mul, norm_pow] at h1
  have h3 := mul_lt_mul_of_pos_right hk' hpos
  rw [inv_mul_cancel₀ hpos.ne'] at h3
  linarith

/- English proof (translation)
Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `U hd hb hT f hfU hf hf1 hfa`. Distinguish the cases in `h : ∀ j (c : K), ∀ v ∈ U, v ≠ 0 → T j v = c • v → ‖c - a j‖ < 1`.

Establish `hU : U ≠ ⊥`. Use `(Submodule.ne_bot_iff U).mpr ⟨f, hfU, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Take `⟨n, hn⟩` from `hf1`. Simplify using `at hn`.

Take `⟨v, hv, hv0, hve⟩` from `UpperTheory.V.LinAlg.simEig T hc _ U rfl hU hT`. Use `choose b hbv using hve`. Take `⟨c, hc0, hcv⟩` from `hb hv`. Use `⟨c • v, b, smul_ne_zero hc0 hv0, hcv, fun j => ?_, fun j => h j (b j) v hv hv0 (hbv j)⟩` and prove the remaining obligations. Rewrite using `[map_smul, hbv j, smul_comm]`.

Use `push Not at h`. Take `⟨j, c, v, hv, hv0, hcv, hca⟩` from `h`. Establish `hc1 : ‖c‖ ≤ 1`. Take `⟨e, he0, hev⟩` from `hb hv`. Use `eig_le_one (T j) (h1 j) (e • v) (smul_ne_zero he0 hv0) hev c ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hcv, smul_comm]`. Establish `hca1 : ‖c - a j‖ = 1` using `le_antisymm (sub_le_one' hc1 (ha j)) hca`. Set `S : Module.End K V` to `T j - c • 1`. Establish `hS : ∀ x, S x = T j x - c • x` using `fun x => by simp [S]`. Establish `hcomm : ∀ i x, T i (S x) = S (T i x)`.

Introduce `i x`. Establish `h3 : T j (T i x) = T i (T j x)`. Use `congrArg (fun S : Module.End K V => S x) (hc j i)` as an intermediate fact. Simplify using `using this`. Rewrite using `[hS, hS, map_sub, map_smul, h3]`.

Establish `hle : U.map S ≤ U`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[hS]`. Conclude with `U.sub_mem (hT j x hx) (U.smul_mem c hx)`. Establish `hSn : ∀ (x : V) n, (S x).1 n = (T j x).1 n - c * x.1 n` using `fun x n => by rw [hS]; simp`.

Use `ih _ (hd ▸ finrank_map_lt U S v hv hv0 (by rw [hS, hcv, sub_self])) (U.map S) rfl (hle.trans hb) ?_ (S f) ⟨f, hfU, rfl⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `i _ ⟨x, hx, rfl⟩`. Conclude with `⟨T i x, hT i x hx, (hcomm i x).symm⟩`. Introduce `n`. Rewrite using `[hSn]`.

Use `sub_le_one' (h1 j f hf n) ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hc1 (norm_nonneg _) (hf n)`. Take `⟨n, hn⟩` from `hf1`. Use `⟨n, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[hSn]`. Use `sub_le_one' (h1 j f hf n) ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hc1 (norm_nonneg _) (hf n)`. Assume the negation of the conclusion as `hlt push Not at hlt`.

Establish `h4` using `sub_lt_one' (hfa j n) hlt`. Establish `h5 : (T j f).1 n - a j * f.1 n - (S f).1 n = (c - a j) * f.1 n` using `by rw [hSn]; ring`. Rewrite `h4` using `[h5, norm_mul, hca1, hn]`. Simplify using `at h4`. Introduce `i n`.

Establish `hg : ∀ n, ‖(T i f - a i • f).1 n‖ < 1` using `fun n => by simpa using hfa i n`. Establish `h6 : (T i (S f)).1 n - a i * (S f).1 n = (S (T i f - a i • f)).1 n`. Rewrite using `[map_sub, map_smul, hcomm]`. Simplify using the standard rewrite rules. Rewrite using `[h6, hSn]`.

Use `sub_lt_one' (h2 j _ hg n) ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right hc1 (norm_nonneg _) (hg n)`.
-/
private theorem main [IsAlgClosed K] {I J : Type} (V : Submodule K (I → K)) [FiniteDimensional K V]
    (T : J → Module.End K V) (hc : ∀ i j, T i * T j = T j * T i)
    (h1 : ∀ j (v : V), (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T j v).1 n‖ ≤ 1)
    (h2 : ∀ j (v : V), (∀ n, ‖v.1 n‖ < 1) → ∀ n, ‖(T j v).1 n‖ < 1) (a : J → K) (ha : ∀ j, ‖a j‖ ≤ 1) :
    ∀ (d : ℕ) (U : Submodule K V), finrank K U = d → U ≤ bdd V → (∀ j, ∀ x ∈ U, T j x ∈ U) →
      ∀ f ∈ U, (∀ n, ‖f.1 n‖ ≤ 1) → (∃ n, ‖f.1 n‖ = 1) → (∀ j n, ‖(T j f).1 n - a j * f.1 n‖ < 1) →
      ∃ (h : V) (b : J → K), h ≠ 0 ∧ (∀ n, ‖h.1 n‖ ≤ 1) ∧ (∀ j, T j h = b j • h) ∧ ∀ j, ‖b j - a j‖ < 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hb hT f hfU hf hf1 hfa
    by_cases h : ∀ j (c : K), ∀ v ∈ U, v ≠ 0 → T j v = c • v → ‖c - a j‖ < 1
    · have hU : U ≠ ⊥ := by
        refine (Submodule.ne_bot_iff U).mpr ⟨f, hfU, ?_⟩
        rintro rfl
        obtain ⟨n, hn⟩ := hf1
        simp at hn
      obtain ⟨v, hv, hv0, hve⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl hU hT
      choose b hbv using hve
      obtain ⟨c, hc0, hcv⟩ := hb hv
      refine ⟨c • v, b, smul_ne_zero hc0 hv0, hcv, fun j => ?_, fun j => h j (b j) v hv hv0 (hbv j)⟩
      rw [map_smul, hbv j, smul_comm]
    · push Not at h
      obtain ⟨j, c, v, hv, hv0, hcv, hca⟩ := h
      have hc1 : ‖c‖ ≤ 1 := by
        obtain ⟨e, he0, hev⟩ := hb hv
        refine eig_le_one (T j) (h1 j) (e • v) (smul_ne_zero he0 hv0) hev c ?_
        rw [map_smul, hcv, smul_comm]
      have hca1 : ‖c - a j‖ = 1 := le_antisymm (sub_le_one' hc1 (ha j)) hca
      let S : Module.End K V := T j - c • 1
      have hS : ∀ x, S x = T j x - c • x := fun x => by simp [S]
      have hcomm : ∀ i x, T i (S x) = S (T i x) := by
        intro i x
        have h3 : T j (T i x) = T i (T j x) := by
          have := congrArg (fun S : Module.End K V => S x) (hc j i)
          simpa using this
        rw [hS, hS, map_sub, map_smul, h3]
      have hle : U.map S ≤ U := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hS]
        exact U.sub_mem (hT j x hx) (U.smul_mem c hx)
      have hSn : ∀ (x : V) n, (S x).1 n = (T j x).1 n - c * x.1 n := fun x n => by rw [hS]; simp
      refine ih _ (hd ▸ finrank_map_lt U S v hv hv0 (by rw [hS, hcv, sub_self])) (U.map S) rfl (hle.trans hb) ?_
        (S f) ⟨f, hfU, rfl⟩ ?_ ?_ ?_
      · rintro i _ ⟨x, hx, rfl⟩
        exact ⟨T i x, hT i x hx, (hcomm i x).symm⟩
      · intro n
        rw [hSn]
        refine sub_le_one' (h1 j f hf n) ?_
        rw [norm_mul]
        exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
      · obtain ⟨n, hn⟩ := hf1
        refine ⟨n, le_antisymm ?_ ?_⟩
        · rw [hSn]
          refine sub_le_one' (h1 j f hf n) ?_
          rw [norm_mul]
          exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
        · by_contra hlt
          push Not at hlt
          have h4 := sub_lt_one' (hfa j n) hlt
          have h5 : (T j f).1 n - a j * f.1 n - (S f).1 n = (c - a j) * f.1 n := by rw [hSn]; ring
          rw [h5, norm_mul, hca1, hn] at h4
          simp at h4
      · intro i n
        have hg : ∀ n, ‖(T i f - a i • f).1 n‖ < 1 := fun n => by simpa using hfa i n
        have h6 : (T i (S f)).1 n - a i * (S f).1 n = (S (T i f - a i • f)).1 n := by
          rw [map_sub, map_smul, hcomm]; simp
        rw [h6, hSn]
        refine sub_lt_one' (h2 j _ hg n) ?_
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right hc1 (norm_nonneg _) (hg n)

end

/- English proof (translation)
Introduce `l _ I J V hV T hc h1 h2 f a hf hf1 ha hfa`. Use `main V T hc h1 h2 a ha _ (bdd V) rfl le_rfl ?_ f ⟨1, one_ne_zero, by simpa using hf⟩ hf hf1 hfa` and prove the remaining obligations. Introduce and unpack `j x ⟨c, hc0, hx⟩`. Use `⟨c, hc0, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul]`.

Conclude with `h1 j _ hx`.
-/
theorem UpperTheory.V.Sd.delSerre :
    UpperTheory.V.Sd.DelSerre := by
  intro l _ I J V hV T hc h1 h2 f a hf hf1 ha hfa
  refine main V T hc h1 h2 a ha _ (bdd V) rfl le_rfl ?_ f ⟨1, one_ne_zero, by simpa using hf⟩ hf hf1 hfa
  rintro j x ⟨c, hc0, hx⟩
  refine ⟨c, hc0, ?_⟩
  rw [← map_smul]
  exact h1 j _ hx
