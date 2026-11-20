import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory.UnIntApprox

open Filter Topology

/- English proof (translation)
Set `ι` to `Fintype.equivFin n`. Take `⟨u, hu, hlim⟩` from `GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin (Fintype.card n)) _ K)) conjTranspose_one (by simp) (reindex ι ι g) (fun k => (1 + q ^ k)⁻¹)`. Set `_ : NormedField K` to `w.toNormedField`. Establish `hq1 : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw`. Establish `he : Tendsto (fun k : ℕ => (1 + q ^ k)⁻¹) atTop (𝓝 1)`.

Simplify using `using (hq1.const_add 1).inv₀ (by simp)`. Establish `he' : Tendsto (fun k : ℕ => star (1 + q ^ k)⁻¹) atTop (𝓝 0)`. Establish `h` using `hq1.mul he`. Rewrite `h` using `[zero_mul]`. Use `h.congr fun k => ?_` and prove the remaining obligations.

Establish `hk : q ^ k ≠ 0` using `pow_ne_zero _ hq0`. Rewrite using `[star_inv₀, star_add, star_one, star_pow, hq, inv_pow]`. Establish `: 1 + (q ^ k)⁻¹ = (q ^ k)⁻¹ * (1 + q ^ k)` using `by field_simp; ring`. Rewrite using `[this, mul_inv, inv_inv]`. Establish `h1` using `hlim w (tendsto_iff_norm_sub_tendsto_zero.1 he) (tendsto_zero_iff_norm_tendsto_zero.1 he')`.

Set `U : ℕ → Matrix n n K` to `fun k => (u k).submatrix ι ι`. Establish `hU : Tendsto U atTop (𝓝 g)`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Use `tendsto_iff_norm_sub_tendsto_zero.2 ?_` and prove the remaining obligations. Establish `h3` using `h1 (ι i) (ι j)`.

Simplify using `only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] at h3`. Conclude with `h3`. Establish `hinv : ContinuousAt Inv.inv g` using `continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg.ne_zero)`. Establish `ha : Tendsto (fun k => g⁻¹ * U k - 1) atTop (𝓝 0)`. Use `(hU.const_mul g⁻¹).sub_const 1` as an intermediate fact.

Rewrite `this` using `[nonsing_inv_mul _ hg, sub_self]`. Then use the resulting hypothesis. Establish `hb : Tendsto (fun k => (U k)⁻¹ * g - 1) atTop (𝓝 0)`. Use `((hinv.tendsto.comp hU).mul_const g).sub_const 1` as an intermediate fact. Rewrite `this` using `[nonsing_inv_mul _ hg, sub_self]`. Then use the resulting hypothesis. Establish `key : ∀ f : ℕ → Matrix n n K, Tendsto f atTop (𝓝 0) → ∀ᶠ k in atTop, ∀ i j, w (f k i j) ≤ 1`.

Introduce `f hf`. Use `eventually_all.2 fun i => eventually_all.2 fun j => ?_` and prove the remaining obligations. Use `tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hf i) j)` as an intermediate fact. Conclude with `this.eventually_le_const one_pos`. Take `⟨k, hk1, hk2⟩` from `((key _ ha).and (key _ hb)).exists`.

Use `⟨U k, ?_, hk1, hk2⟩` and prove the remaining obligations. Establish `h2 : (u k)ᴴ * u k = 1`. Use `hu k` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`. Conclude with `mul_eq_one_comm.1 this`.

Use `show ((u k).submatrix ι ι)ᴴ * (u k).submatrix ι ι = 1`. Rewrite using `[conjTranspose_submatrix, submatrix_mul_equiv, h2, submatrix_one_equiv]`.
-/
theorem exists_near {K : Type} [Field K] [CharZero K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (w : AbsoluteValue K ℝ) {q : K} (hq0 : q ≠ 0) (hq : star q = q⁻¹) (hw : w q < 1)
    (g : Matrix n n K) (hg : IsUnit g.det) :
    ∃ u : Matrix n n K, uᴴ * u = 1 ∧ (∀ i j, w ((g⁻¹ * u - 1) i j) ≤ 1) ∧
      ∀ i j, w ((u⁻¹ * g - 1) i j) ≤ 1 := by
  let ι := Fintype.equivFin n
  obtain ⟨u, hu, hlim⟩ := GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin (Fintype.card n)) _ K))
    conjTranspose_one (by simp) (reindex ι ι g) (fun k => (1 + q ^ k)⁻¹)
  let _ : NormedField K := w.toNormedField
  have hq1 : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw
  have he : Tendsto (fun k : ℕ => (1 + q ^ k)⁻¹) atTop (𝓝 1) := by
    simpa using (hq1.const_add 1).inv₀ (by simp)
  have he' : Tendsto (fun k : ℕ => star (1 + q ^ k)⁻¹) atTop (𝓝 0) := by
    have h := hq1.mul he
    rw [zero_mul] at h
    refine h.congr fun k => ?_
    have hk : q ^ k ≠ 0 := pow_ne_zero _ hq0
    rw [star_inv₀, star_add, star_one, star_pow, hq, inv_pow]
    have : 1 + (q ^ k)⁻¹ = (q ^ k)⁻¹ * (1 + q ^ k) := by field_simp; ring
    rw [this, mul_inv, inv_inv]
  have h1 := hlim w (tendsto_iff_norm_sub_tendsto_zero.1 he) (tendsto_zero_iff_norm_tendsto_zero.1 he')
  let U : ℕ → Matrix n n K := fun k => (u k).submatrix ι ι
  have hU : Tendsto U atTop (𝓝 g) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have h3 := h1 (ι i) (ι j)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] at h3
    exact h3
  have hinv : ContinuousAt Inv.inv g :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg.ne_zero)
  have ha : Tendsto (fun k => g⁻¹ * U k - 1) atTop (𝓝 0) := by
    have := (hU.const_mul g⁻¹).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have hb : Tendsto (fun k => (U k)⁻¹ * g - 1) atTop (𝓝 0) := by
    have := ((hinv.tendsto.comp hU).mul_const g).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have key : ∀ f : ℕ → Matrix n n K, Tendsto f atTop (𝓝 0) → ∀ᶠ k in atTop, ∀ i j, w (f k i j) ≤ 1 := by
    intro f hf
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have := tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hf i) j)
    exact this.eventually_le_const one_pos
  obtain ⟨k, hk1, hk2⟩ := ((key _ ha).and (key _ hb)).exists
  refine ⟨U k, ?_, hk1, hk2⟩
  have h2 : (u k)ᴴ * u k = 1 := by
    have := hu k
    rw [Matrix.mul_one] at this
    exact mul_eq_one_comm.1 this
  show ((u k).submatrix ι ι)ᴴ * (u k).submatrix ι ι = 1
  rw [conjTranspose_submatrix, submatrix_mul_equiv, h2, submatrix_one_equiv]

/- English proof (translation)
Introduce `K _ _ σ n _ _ 𝔭 α β hσ hα hβ hαβ g hg`. Set `_ : StarRing K` to `{ star := σ star_involutive := hσ star_mul := fun x y => by rw [map_mul, mul_comm] star_add := fun x y => map_add σ x y }`. Establish `hβ0 : (β : K) ≠ 0`. Introduce `h`. Apply `hβ` to reduce the goal to its premises.

Establish `: β = 0` using `by exact_mod_cast h`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `hα0 : (α : K) ≠ 0`. Introduce `h`.

Apply `hβ0` to reduce the goal to its premises. Rewrite using `[hαβ, h, map_zero]`. Establish `hq : star ((α : K) / β) = ((α : K) / β)⁻¹` using `by show σ _ = _`. Rewrite using `[map_div₀, ← hαβ, hαβ, hσ, inv_div]`. Establish `hw : NumberField.HeightOneSpectrum.adicAbv K 𝔭 ((α : K) / β) < 1`.

Rewrite using `[map_div₀, ← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding]`. Establish `h1` using `(FinitePlace.norm_lt_one_iff_mem K 𝔭 α).2 hα`. Establish `h2` using `(FinitePlace.norm_eq_one_iff_notMem K 𝔭 β).2 hβ`. Use `erw [h2]`. Rewrite using `[div_one]`.

Conclude with `h1`. Take `⟨u, hu, h1, h2⟩` from `exists_near _ (div_ne_zero hα0 hβ0) hq hw g hg`. Take `⟨s, hs, hsb⟩` from `GlobalTheory.UnApprox.exists_denom (J := (n × n) ⊕ (n × n)) 𝔭.ne_bot (Sum.elim (fun p => (g⁻¹ * u - 1) p.1 p.2) (fun p => (u⁻¹ * g - 1) p.1 p.2)) (by`. Introduce `v hv`. Establish `: v = 𝔭` using `by ext1`.

Conclude with `(𝔭.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 hv)).symm`. Substitute `this` using the available equality. Introduce and unpack `(p | p)`. Conclude with `h1 _ _`. Conclude with `h2 _ _)`.

Establish `key : ∀ (M : Matrix n n K) (i j : n), (∃ b : 𝓞 K, (s : K) * (M - 1) i j = b) → (s : K) * M i j ∈ (algebraMap (𝓞 K) K).range`. Introduce and unpack `M i j ⟨b, hb⟩`. Use `⟨b + if i = j then s else 0, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[Matrix.sub_apply, one_apply, mul_sub]`. Rewrite using `[map_add]`.

Use `split_ifs at hb ⊢`. Use `show (b : K) + s = _`. Take the linear combination `-hb`. Rewrite using `[map_zero] show (b : K) + 0 = _`. Take the linear combination `-hb`.

Use `⟨u, hu, s, fun h => 𝔭.isPrime.ne_top ?_, fun i j => key _ _ _ (hsb (Sum.inl (i, j))), fun i j => key _ _ _ (hsb (Sum.inr (i, j)))⟩` and prove the remaining obligations. Use `Ideal.isCoprime_iff_sup_eq.1 hs` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h)]`. Then use the resulting hypothesis.
-/
theorem exists_unitary_mul_integral :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ σ n _ _ 𝔭 α β hσ hα hβ hαβ g hg
  let _ : StarRing K :=
    { star := σ
      star_involutive := hσ
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hβ0 : (β : K) ≠ 0 := by
    intro h
    apply hβ
    have : β = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hα0 : (α : K) ≠ 0 := by
    intro h
    apply hβ0
    rw [hαβ, h, map_zero]
  have hq : star ((α : K) / β) = ((α : K) / β)⁻¹ := by
    show σ _ = _
    rw [map_div₀, ← hαβ, hαβ, hσ, inv_div]
  have hw : NumberField.HeightOneSpectrum.adicAbv K 𝔭 ((α : K) / β) < 1 := by
    rw [map_div₀, ← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding]
    have h1 := (FinitePlace.norm_lt_one_iff_mem K 𝔭 α).2 hα
    have h2 := (FinitePlace.norm_eq_one_iff_notMem K 𝔭 β).2 hβ
    erw [h2]
    rw [div_one]
    exact h1
  obtain ⟨u, hu, h1, h2⟩ := exists_near _ (div_ne_zero hα0 hβ0) hq hw g hg
  obtain ⟨s, hs, hsb⟩ := GlobalTheory.UnApprox.exists_denom (J := (n × n) ⊕ (n × n)) 𝔭.ne_bot
    (Sum.elim (fun p => (g⁻¹ * u - 1) p.1 p.2) (fun p => (u⁻¹ * g - 1) p.1 p.2)) (by
      intro v hv
      have : v = 𝔭 := by
        ext1
        exact (𝔭.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 hv)).symm
      subst this
      rintro (p | p)
      · exact h1 _ _
      · exact h2 _ _)
  have key : ∀ (M : Matrix n n K) (i j : n), (∃ b : 𝓞 K, (s : K) * (M - 1) i j = b) →
      (s : K) * M i j ∈ (algebraMap (𝓞 K) K).range := by
    rintro M i j ⟨b, hb⟩
    refine ⟨b + if i = j then s else 0, ?_⟩
    rw [Matrix.sub_apply, one_apply, mul_sub] at hb
    rw [map_add]
    split_ifs at hb ⊢
    · show (b : K) + s = _
      linear_combination -hb
    · rw [map_zero]
      show (b : K) + 0 = _
      linear_combination -hb
  refine ⟨u, hu, s, fun h => 𝔭.isPrime.ne_top ?_, fun i j => key _ _ _ (hsb (Sum.inl (i, j))),
    fun i j => key _ _ _ (hsb (Sum.inr (i, j)))⟩
  have := Ideal.isCoprime_iff_sup_eq.1 hs
  rwa [sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h)] at this

end GlobalTheory.UnIntApprox
