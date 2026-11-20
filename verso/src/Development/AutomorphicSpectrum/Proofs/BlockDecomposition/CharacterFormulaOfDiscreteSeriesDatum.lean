import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Hilb

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs.Hilb

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

/- English proof (translation)
Introduce `h`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem w_ne_zero (T : S7.KType ε (lowK ε lam)) : T.w ≠ 0 := by
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
Unfold `V1`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨v, hv⟩` from `(mem_datumV_iff hP T.w y).1 hy`.

Conclude with `⟨v, hv⟩`. Introduce and unpack `⟨v, rfl⟩`. Use `⟨⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_smooth hP T.w v⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `(mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩`.
-/
theorem mem_datum_space_iff_range (hP : IsPsiFor ε lam T Ψ) (x : L2 ε) :
    x ∈ V1 ε Ψ ↔ ∃ v : T.V, x = uniformisationL2 ε Ψ T.w v := by
  unfold V1
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w y).1 hy
    exact ⟨v, hv⟩
  · rintro ⟨v, rfl⟩
    refine ⟨⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_smooth hP T.w v⟩, ?_, rfl⟩
    exact (mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩

/- English proof (translation)
Establish `hker : ∀ k : S7.KG ε, ∀ v ∈ LinearMap.ker B, (T.τ k : T.V →L[ℂ] T.V) v ∈ LinearMap.ker B`. Introduce `k v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[show (T.τ k : T.V →L[ℂ] T.V) v = T.op k v from rfl, hB k v, hv, map_zero]`. Break down `T.irred (LinearMap.ker B) hker with h | h` into its components or cases.

Conclude with `LinearMap.ker_eq_bot.1 h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h) hB0`.
-/
theorem kmap_injective (B : T.V →ₗ[ℂ] L2 ε)
    (hB : ∀ (k : S7.KG ε) (v : T.V), B (T.op k v) = rreg ε (S7.toMK k) (B v)) (hB0 : B ≠ 0) :
    Function.Injective B := by
  have hker : ∀ k : S7.KG ε, ∀ v ∈ LinearMap.ker B,
      (T.τ k : T.V →L[ℂ] T.V) v ∈ LinearMap.ker B := by
    intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [show (T.τ k : T.V →L[ℂ] T.V) v = T.op k v from rfl, hB k v, hv, map_zero]
  rcases T.irred (LinearMap.ker B) hker with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hB0

/- English proof (translation)
Establish `hg' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g` using `hg`. Establish `h1 : g.conjTranspose * g = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff'.1 hg'.1`. Establish `hc : g * Jm ε = Jm ε * g` using `hg'.2`.

Establish `hU : inUJ ε g` using `by show g.conjTranspose * Jm ε * g = Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `hr : g ∈ Set.range (fun y : S7.UJ ε => S7.toM y)`. Rewrite using `[S7.range_toM ε]`. Conclude with `hU`.

Take `⟨y, hy⟩` from `hr`. Establish `hy' : S7.toM y = g` using `hy`. Use `⟨⟨y, ?_⟩, hy'⟩` and prove the remaining obligations. Use `show S7.toM y ∈ Kset ε`. Rewrite using `[hy']`.

Conclude with `hg`.
-/
private theorem exists_toMK_eq_of_mem_Kset {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    ∃ k : S7.KG ε, S7.toMK k = g := by
  have hg' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := hg
  have h1 : g.conjTranspose * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 hg'.1
  have hc : g * Jm ε = Jm ε * g := hg'.2
  have hU : inUJ ε g := by
    show g.conjTranspose * Jm ε * g = Jm ε
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hr : g ∈ Set.range (fun y : S7.UJ ε => S7.toM y) := by
    rw [S7.range_toM ε]
    exact hU
  obtain ⟨y, hy⟩ := hr
  have hy' : S7.toM y = g := hy
  refine ⟨⟨y, ?_⟩, hy'⟩
  show S7.toM y ∈ Kset ε
  rw [hy']
  exact hg

/- English proof (translation)
The claim follows from `k.2`.
-/
private theorem toMK_mem_Kset' (k : S7.KG ε) : S7.toMK k ∈ Formalism.REAL.Kset ε := k.2

/- English proof (translation)
Introduce `θ hθ`. Take `⟨k, hk⟩` from `exists_toMK_eq_of_mem_Kset hθ`. Establish `hAu` using `h θ hθ`. Rewrite `hAu`, the goal using `[← hk]`. Rewrite `hAu` using `[← hA k u]`.

Establish `hku : T.op k u = Complex.exp (↑(∑ a, μ a * θ a) * Complex.I) • u` using `hinj (by rw [hAu, map_smul])`. Rewrite using `[← hC k u, hku, map_smul]`.
-/
theorem isWtOn_transfer {A C : T.V →ₗ[ℂ] L2 ε}
    (hA : ∀ (k : S7.KG ε) (v : T.V), A (T.op k v) = rreg ε (S7.toMK k) (A v))
    (hC : ∀ (k : S7.KG ε) (v : T.V), C (T.op k v) = rreg ε (S7.toMK k) (C v))
    (hinj : Function.Injective A) {μ : Fin n → ℝ} {u : T.V}
    (h : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) μ (A u)) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) μ (C u) := by
  intro θ hθ
  obtain ⟨k, hk⟩ := exists_toMK_eq_of_mem_Kset hθ
  have hAu := h θ hθ
  rw [← hk] at hAu ⊢
  rw [← hA k u] at hAu
  have hku : T.op k u = Complex.exp (↑(∑ a, μ a * θ a) * Complex.I) • u :=
    hinj (by rw [hAu, map_smul])
  rw [← hC k u, hku, map_smul]

/- English proof (translation)
Establish `hinj` using `kmap_injective B hB hB0`. Establish `hw` using `w_ne_zero T`. Establish `hAapp : ∀ v, datumEmbeddingToL2 hP T.w v = uniformisationL2 ε Ψ T.w v` using `fun v => rfl`. Establish `hAeq : ∀ (k : S7.KG ε) (v : T.V), datumEmbeddingToL2 hP T.w (T.op k v) = rreg ε (S7.toMK k) (datumEmbeddingToL2 hP T.w v)`. Introduce `k v`.

Rewrite using `[hAapp, hAapp, rightRegular_datumEmbedding hP]`. Establish `hAinj : Function.Injective (datumEmbeddingToL2 hP T.w)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`. Conclude with `eq_zero_of_datumEmbedding_eq_zero hP hw hv`.

Take `⟨_, _, _, ⟨x, hxV, hx0, hxw⟩, hdom⟩` from `hD`. Use `⟨inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg y hy`. Take `⟨k, rfl⟩` from `exists_toMK_eq_of_mem_Kset hg`. Take `⟨v, rfl⟩` from `LinearMap.mem_range.1 hy`.

Conclude with `LinearMap.mem_range.2 ⟨T.op k v, hB k v⟩`. Introduce `S' hS' hstab`. Establish `hW : ∀ k : S7.KG ε, ∀ v ∈ S'.comap B, (T.τ k : T.V →L[ℂ] T.V) v ∈ S'.comap B`. Introduce `k v hv`. Use `show B (T.op k v) ∈ S'`.

Rewrite using `[hB]`. Conclude with `hstab _ (toMK_mem_Kset' k) (B v) hv`. Break down `T.irred (S'.comap B) hW with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Take `⟨v, rfl⟩` from `LinearMap.mem_range.1 (hS' hy)`. Establish `hv : v ∈ S'.comap B` using `hy`. Rewrite `hv` using `[h]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hv, map_zero]`.

Conclude with `Submodule.zero_mem _`. Use `right`. Apply `le_antisymm hS'` to reduce the goal to its premises. Introduce `y hy`. Take `⟨v, rfl⟩` from `LinearMap.mem_range.1 hy`.

Establish `hv : v ∈ S'.comap B` using `by rw [h]; trivial`. Conclude with `hv`. Take `⟨u, rfl⟩` from `(mem_datum_space_iff_range hP x).1 hxV`. Use `⟨B u, LinearMap.mem_range.2 ⟨u, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hx0` to reduce the goal to its premises. Establish `hu : u = 0` using `hinj (by rw [h0, map_zero])`. Rewrite using `[hu, ← hAapp, map_zero]`. Conclude with `isWtOn_transfer hAeq hB hAinj hxw`. Introduce `μ y hy hne hwt`.

Take `⟨u, rfl⟩` from `LinearMap.mem_range.1 hy`. Use `hdom μ (datumEmbeddingToL2 hP T.w u) ((mem_datum_space_iff_range hP _).2 ⟨u, rfl⟩) ?_ ?_` and prove the remaining obligations. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `hu : u = 0` using `hAinj (by rw [h0, map_zero])`.

Rewrite using `[hu, map_zero]`. Conclude with `isWtOn_transfer hB hAeq hinj hwt`.
-/
theorem isKTypeOf_range (hP : IsPsiFor ε lam T Ψ)
    (hD : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ)) (B : T.V →ₗ[ℂ] L2 ε)
    (hB : ∀ (k : S7.KG ε) (v : T.V), B (T.op k v) = rreg ε (S7.toMK k) (B v)) (hB0 : B ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (LinearMap.range B) := by
  have hinj := kmap_injective B hB hB0
  have hw := w_ne_zero T
  have hAapp : ∀ v, datumEmbeddingToL2 hP T.w v = uniformisationL2 ε Ψ T.w v := fun v => rfl
  have hAeq : ∀ (k : S7.KG ε) (v : T.V),
      datumEmbeddingToL2 hP T.w (T.op k v) = rreg ε (S7.toMK k) (datumEmbeddingToL2 hP T.w v) := by
    intro k v
    rw [hAapp, hAapp, rightRegular_datumEmbedding hP]
  have hAinj : Function.Injective (datumEmbeddingToL2 hP T.w) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact eq_zero_of_datumEmbedding_eq_zero hP hw hv
  obtain ⟨_, _, _, ⟨x, hxV, hx0, hxw⟩, hdom⟩ := hD
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro g hg y hy
    obtain ⟨k, rfl⟩ := exists_toMK_eq_of_mem_Kset hg
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
    exact LinearMap.mem_range.2 ⟨T.op k v, hB k v⟩
  · intro S' hS' hstab
    have hW : ∀ k : S7.KG ε, ∀ v ∈ S'.comap B, (T.τ k : T.V →L[ℂ] T.V) v ∈ S'.comap B := by
      intro k v hv
      show B (T.op k v) ∈ S'
      rw [hB]
      exact hstab _ (toMK_mem_Kset' k) (B v) hv
    rcases T.irred (S'.comap B) hW with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 (hS' hy)
      have hv : v ∈ S'.comap B := hy
      rw [h] at hv
      rw [(Submodule.mem_bot ℂ).1 hv, map_zero]
      exact Submodule.zero_mem _
    · right
      apply le_antisymm hS'
      intro y hy
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
      have hv : v ∈ S'.comap B := by rw [h]; trivial
      exact hv
  · obtain ⟨u, rfl⟩ := (mem_datum_space_iff_range hP x).1 hxV
    refine ⟨B u, LinearMap.mem_range.2 ⟨u, rfl⟩, ?_, ?_⟩
    · intro h0
      apply hx0
      have hu : u = 0 := hinj (by rw [h0, map_zero])
      rw [hu, ← hAapp, map_zero]
    · exact isWtOn_transfer hAeq hB hAinj hxw
  · intro μ y hy hne hwt
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy
    refine hdom μ (datumEmbeddingToL2 hP T.w u) ((mem_datum_space_iff_range hP _).2 ⟨u, rfl⟩) ?_ ?_
    · intro h0
      apply hne
      have hu : u = 0 := hAinj (by rw [h0, map_zero])
      rw [hu, map_zero]
    · exact isWtOn_transfer hB hAeq hinj hwt

/- English proof (translation)
Assume the negation of the conclusion as `hB0`. Establish `hK` using `isKTypeOf_range hP hD B hB hB0`. Establish `hle : LinearMap.range B ≤ Hlam ε Ψ T.w`. Introduce `y hy`. Take `⟨v, rfl⟩` from `LinearMap.mem_range.1 hy`.

Conclude with `hrange v`. Establish `heq` using `hU _ hle hK`. Apply `hB0` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hv : B v ∈ V1 ε Ψ`.

Rewrite using `[← heq]`. Conclude with `LinearMap.mem_range.2 ⟨v, rfl⟩`. Take `⟨u, hu⟩` from `(mem_datum_space_iff_range hP _).1 hv`. Establish `h0 : inner ℂ (B v) (B v) = 0`. Establish `h1` using `horth u v`.

Rewrite `h1` using `[← hu]`. Then use the resulting hypothesis. Rewrite using `[LinearMap.zero_apply]`. Conclude with `inner_self_eq_zero.1 h0`.
-/
theorem kmap_zero (hP : IsPsiFor ε lam T Ψ)
    (hD : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ))
    (hU : ∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
      Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ)
    (B : T.V →ₗ[ℂ] L2 ε) (hB : ∀ (k : S7.KG ε) (v : T.V), B (T.op k v) = rreg ε (S7.toMK k) (B v))
    (hrange : ∀ v, B v ∈ Hlam ε Ψ T.w)
    (horth : ∀ v v' : T.V, inner ℂ (B v') (uniformisationL2 ε Ψ T.w v) = 0) : B = 0 := by
  by_contra hB0
  have hK := isKTypeOf_range hP hD B hB hB0
  have hle : LinearMap.range B ≤ Hlam ε Ψ T.w := by
    intro y hy
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
    exact hrange v
  have heq := hU _ hle hK
  apply hB0
  refine LinearMap.ext fun v => ?_
  have hv : B v ∈ V1 ε Ψ := by
    rw [← heq]
    exact LinearMap.mem_range.2 ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := (mem_datum_space_iff_range hP _).1 hv
  have h0 : inner ℂ (B v) (B v) = 0 := by
    have h1 := horth u v
    rwa [← hu] at h1
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.1 h0

/- English proof (translation)
Establish `hv₀ : T.w ≠ 0` using `w_ne_zero T`. Take `⟨q, hq⟩` from `LinearMap.mem_range.1 (Submodule.starProjection_apply_mem (LinearMap.range (ffaJ hP T.w)) (rreg ε g (uniformisationL2 ε Ψ T.w v)))`. Establish `hxo : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ (LinearMap.range (ffaJ hP T.w))ᗮ`. Rewrite using `[← ffaJ_apply hP T.w q, hq]`. Conclude with `Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (ffaJ hP T.w)) _`.

Establish `hxj : ∀ w, inner ℂ (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) (uniformisationL2 ε Ψ T.w w) = 0` using `fun w => Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self (ffaJ hP T.w) w) hxo`. Establish `hfH : rreg ε g (uniformisationL2 ε Ψ T.w v) ∈ Hlam ε Ψ T.w` using `hst g hg _ (datumEmbedding_mem_Hlam hP v)`. Establish `hxH : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ Hlam ε Ψ T.w` using `Submodule.sub_mem _ hfH (datumEmbedding_mem_Hlam hP q)`. Establish `hRH : ∀ k : S7.KG ε, rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∈ Hlam ε Ψ T.w` using `fun k => hst _ (ffa_toMK_mem k) _ hxH`. Establish `horth : ∀ u v'' : T.V, inner ℂ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) v'') (uniformisationL2 ε Ψ T.w u) = 0`.

Introduce `u v''`. Establish `h0 : ∀ k : S7.KG ε, inner ℂ (uniformisationL2 ε Ψ T.w u) (rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q)) = 0`. Introduce `k`. Rewrite using `[← inv_inv k, ← ffa_rreg_adj, rightRegular_datumEmbedding hP]`. Conclude with `inner_eq_zero_symm.1 (hxj _)`.

Rewrite using `[← inner_conj_symm, ffaB_inner]`. Simplify using `only [h0, mul_zero, integral_zero, map_zero]`. Establish `hB0` using `kmap_zero hP hD hU (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q)) (ffaB_equiv T _ _) (ffaB_mem T _ _ (Hlam ε Ψ T.w) hRH) horth`. Establish `hBv : ∫ k, inner ℂ (T.op k (Ψ g v - q)) T.w • rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∂(dk ε) = 0`. Use `LinearMap.congr_fun hB0 T.w` as an intermediate fact.

Rewrite `this` using `[ffaB_apply, LinearMap.zero_apply]`. Then use the resulting hypothesis. Take `⟨yg, hyg⟩` from `ffa_UJ_lift hg`. Establish `hxae : ((rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun y => jfun Ψ T.w v (Formalism.MainNotions.S.umat y * g) - jfun Ψ T.w q (Formalism.MainNotions.S.umat y)`. Establish `e1` using `rreg_umat_ae ε yg (uniformisationL2 ε Ψ T.w v)`. Establish `e2` using `(measurePreserving_mul_right ε yg).quasiMeasurePreserving.ae_eq_comp (uniformisationL2_ae_eq_jfun hP T.w v)`.

Use `filter_upwards [Lp.coeFn_sub (rreg ε g (uniformisationL2 ε Ψ T.w v)) (uniformisationL2 ε Ψ T.w q), e1, e2, uniformisationL2_ae_eq_jfun hP T.w q] with y h0 h1 h2 h3`. Rewrite using `[h0, Pi.sub_apply, h3, ← hyg, h1]`. Use `congr 1`. Establish `hFc : ContinuousOn (fun y => jfun Ψ T.w v (y * g) - jfun Ψ T.w q y) (UJset ε)` using `((ffa_jfun_cont hP T.w v).comp (continuousOn_id.mul continuousOn_const) (fun y hy => rq_UJ_mul hy hg)).sub (ffa_jfun_cont hP T.w q)`. Establish `hev` using `ffa_eval hFc hxae _ (ffa_cont_coef T (Ψ g v - q) T.w) hBv`.

Establish `hΨk : ∀ (k : S7.KG ε) (h : Matrix (Fin n) (Fin n) ℂ), h ∈ UJset ε → Ψ (S7.toMK k * h) = T.op k * Ψ h`. Introduce `k h hh`. Establish `e` using `hP.1 k 1 h hh`. Rewrite `e` using `[show S7.toMK (1 : S7.KG ε) = 1 from rfl, mul_one, ffa_op_one, mul_one]`. Then use the resulting hypothesis. Establish `hΨk1 : ∀ k : S7.KG ε, Ψ (S7.toMK k) = T.op k`.

Introduce `k`. Establish `e` using `hΨk k 1 (ffa_toMK_mem (1 : S7.KG ε))`. Rewrite `e` using `[mul_one, hP.2.1, mul_one]`. Then use the resulting hypothesis. Establish `hint : ∀ k : S7.KG ε, inner ℂ (T.op k (Ψ g v - q)) T.w * (jfun Ψ T.w v (S7.toMK k * g) - jfun Ψ T.w q (S7.toMK k)) = ((‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 : ℝ) : ℂ)`. Introduce `k`.

Use `show inner ℂ (T.op k (Ψ g v - q)) T.w * (inner ℂ T.w (Ψ (S7.toMK k * g) v) - inner ℂ T.w (Ψ (S7.toMK k) q)) = _`. Rewrite using `[hΨk k g hg, hΨk1 k, ContinuousLinearMap.mul_apply, ← inner_sub_right, ← map_sub, ← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]`. Establish `hI : ∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) = 0`. Establish `e2 : ((∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = 0`. Rewrite using `[← integral_complex_ofReal]`.

Use `Eq.trans ?_ hev` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(hint k).symm`. Conclude with `e2` after adjusting the coercions.

Establish `hDz : Ψ g v - q = 0`. Establish `hk` using `kschur_coef T T.w (Ψ g v - q)`. Rewrite `hk` using `[hI, mul_zero]`. Establish `hv0 : ‖T.w‖ ^ 2 ≠ 0` using `pow_ne_zero 2 (norm_ne_zero_iff.2 hv₀)`. Establish `h2 : ‖Ψ g v - q‖ ^ 2 = 0`.

Break down `mul_eq_zero.1 hk.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hv0`. Conclude with `norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)`. Establish `hqv : q = Ψ g v` using `(sub_eq_zero.1 hDz).symm`.

Establish `hdec : rreg ε g (uniformisationL2 ε Ψ T.w v) = (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) + uniformisationL2 ε Ψ T.w q` using `(sub_add_cancel _ _).symm`. Rewrite using `[hdec, inner_add_right, inner_eq_zero_symm.1 (hxj v'), zero_add, hqv, ffa_form hP]`.
-/
theorem formulaF_of (hP : IsPsiFor ε lam T Ψ)
    (hD : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ))
    (hst : ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w)
    (hU : ∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
      Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v v' : T.V) :
    inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
      ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) := by
  have hv₀ : T.w ≠ 0 := w_ne_zero T
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1
    (Submodule.starProjection_apply_mem (LinearMap.range (ffaJ hP T.w)) (rreg ε g (uniformisationL2 ε Ψ T.w v)))
  have hxo : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ (LinearMap.range (ffaJ hP T.w))ᗮ := by
    rw [← ffaJ_apply hP T.w q, hq]
    exact Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (ffaJ hP T.w)) _
  have hxj : ∀ w, inner ℂ (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) (uniformisationL2 ε Ψ T.w w) = 0 := fun w =>
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self (ffaJ hP T.w) w) hxo
  have hfH : rreg ε g (uniformisationL2 ε Ψ T.w v) ∈ Hlam ε Ψ T.w := hst g hg _ (datumEmbedding_mem_Hlam hP v)
  have hxH : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ Hlam ε Ψ T.w :=
    Submodule.sub_mem _ hfH (datumEmbedding_mem_Hlam hP q)
  have hRH : ∀ k : S7.KG ε, rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∈ Hlam ε Ψ T.w :=
    fun k => hst _ (ffa_toMK_mem k) _ hxH
  have horth : ∀ u v'' : T.V, inner ℂ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) v'')
      (uniformisationL2 ε Ψ T.w u) = 0 := by
    intro u v''
    have h0 : ∀ k : S7.KG ε, inner ℂ (uniformisationL2 ε Ψ T.w u)
        (rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q)) = 0 := by
      intro k
      rw [← inv_inv k, ← ffa_rreg_adj, rightRegular_datumEmbedding hP]
      exact inner_eq_zero_symm.1 (hxj _)
    rw [← inner_conj_symm, ffaB_inner]
    simp only [h0, mul_zero, integral_zero, map_zero]
  have hB0 := kmap_zero hP hD hU (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q))
    (ffaB_equiv T _ _) (ffaB_mem T _ _ (Hlam ε Ψ T.w) hRH) horth
  have hBv : ∫ k, inner ℂ (T.op k (Ψ g v - q)) T.w •
      rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∂(dk ε) = 0 := by
    have := LinearMap.congr_fun hB0 T.w
    rwa [ffaB_apply, LinearMap.zero_apply] at this
  obtain ⟨yg, hyg⟩ := ffa_UJ_lift hg
  have hxae : ((rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun y => jfun Ψ T.w v (Formalism.MainNotions.S.umat y * g) - jfun Ψ T.w q (Formalism.MainNotions.S.umat y) := by
    have e1 := rreg_umat_ae ε yg (uniformisationL2 ε Ψ T.w v)
    have e2 := (measurePreserving_mul_right ε yg).quasiMeasurePreserving.ae_eq_comp (uniformisationL2_ae_eq_jfun hP T.w v)
    filter_upwards [Lp.coeFn_sub (rreg ε g (uniformisationL2 ε Ψ T.w v)) (uniformisationL2 ε Ψ T.w q), e1, e2, uniformisationL2_ae_eq_jfun hP T.w q]
      with y h0 h1 h2 h3
    rw [h0, Pi.sub_apply, h3, ← hyg, h1]
    congr 1
  have hFc : ContinuousOn (fun y => jfun Ψ T.w v (y * g) - jfun Ψ T.w q y) (UJset ε) :=
    ((ffa_jfun_cont hP T.w v).comp (continuousOn_id.mul continuousOn_const)
      (fun y hy => rq_UJ_mul hy hg)).sub (ffa_jfun_cont hP T.w q)
  have hev := ffa_eval hFc hxae _ (ffa_cont_coef T (Ψ g v - q) T.w) hBv
  have hΨk : ∀ (k : S7.KG ε) (h : Matrix (Fin n) (Fin n) ℂ), h ∈ UJset ε →
      Ψ (S7.toMK k * h) = T.op k * Ψ h := by
    intro k h hh
    have e := hP.1 k 1 h hh
    rwa [show S7.toMK (1 : S7.KG ε) = 1 from rfl, mul_one, ffa_op_one, mul_one] at e
  have hΨk1 : ∀ k : S7.KG ε, Ψ (S7.toMK k) = T.op k := by
    intro k
    have e := hΨk k 1 (ffa_toMK_mem (1 : S7.KG ε))
    rwa [mul_one, hP.2.1, mul_one] at e
  have hint : ∀ k : S7.KG ε, inner ℂ (T.op k (Ψ g v - q)) T.w *
      (jfun Ψ T.w v (S7.toMK k * g) - jfun Ψ T.w q (S7.toMK k)) =
        ((‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    show inner ℂ (T.op k (Ψ g v - q)) T.w *
      (inner ℂ T.w (Ψ (S7.toMK k * g) v) - inner ℂ T.w (Ψ (S7.toMK k) q)) = _
    rw [hΨk k g hg, hΨk1 k, ContinuousLinearMap.mul_apply, ← inner_sub_right, ← map_sub,
      ← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  have hI : ∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) = 0 := by
    have e2 : ((∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      refine Eq.trans ?_ hev
      congr 1
      funext k
      exact (hint k).symm
    exact_mod_cast e2
  have hDz : Ψ g v - q = 0 := by
    have hk := kschur_coef T T.w (Ψ g v - q)
    rw [hI, mul_zero] at hk
    have hv0 : ‖T.w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv₀)
    have h2 : ‖Ψ g v - q‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hk.symm with h | h
      · exact h
      · exact absurd h hv0
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hqv : q = Ψ g v := (sub_eq_zero.1 hDz).symm
  have hdec : rreg ε g (uniformisationL2 ε Ψ T.w v) =
      (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) + uniformisationL2 ε Ψ T.w q := (sub_add_cancel _ _).symm
  rw [hdec, inner_add_right, inner_eq_zero_symm.1 (hxj v'), zero_add, hqv, ffa_form hP]

/- English proof (translation)
Introduce `n ε lam T Ψ hP hst hU g hg v v'`. Conclude with `formulaF_of hP (hDatum n ε lam T Ψ hP) hst hU hg v v'`.
-/
theorem stepFormulaF (hDatum : StepDatum) : StepFormulaF := by
  intro n ε lam T Ψ hP hst hU g hg v v'
  exact formulaF_of hP (hDatum n ε lam T Ψ hP) hst hU hg v v'

end GlobalTheory.CompanionTheory.Hilb
