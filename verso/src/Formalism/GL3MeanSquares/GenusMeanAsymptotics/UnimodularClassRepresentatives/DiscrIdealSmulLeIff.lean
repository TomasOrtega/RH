import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MulEqZeroIff

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
/- English proof (translation)
Introduce `x hx y hy`. Establish `h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K)` using `Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩`. Establish `h2` using `Submodule.mul_mem_mul h1 (hLi x hx y hy)`. Rewrite `h2` using `[one_mul]`. Conclude with `h2`.
-/
theorem isIntegralLat_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (c : 𝓞 F) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (c : F) • h) L := by
  intro x hx y hy
  have h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩
  have h2 := Submodule.mul_mem_mul h1 (hLi x hx y hy)
  rw [one_mul] at h2
  exact h2

/- English proof (translation)
Establish `: Fact (IsFixF K F)` using `⟨hF⟩`. Take `⟨b, H, D, hb, hH, -⟩` from `localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭`. Establish `hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) = (algebraMap F K (c : F) • h) (b i) (b j)`. Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]`.

Both sides reduce to the same expression. Rewrite using `[integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk, Fintype.card_fin]`.
-/
theorem akCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]

/- English proof (translation)
Establish `: Fact (IsFixF K F)` using `⟨hF⟩`. Take `⟨b, H, D, hb, hH, -⟩` from `localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭`. Establish `hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) = (algebraMap F K (c : F) • h) (b i) (b j)`. Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]`.

Both sides reduce to the same expression. Rewrite using `[integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk, Fintype.card_fin]`.
-/
theorem nkCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V) * nkCount h L 𝔭 (k - vF 𝔭 c) n := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk,
    Fintype.card_fin]

omit [NumberField K] [StarRing K] [Algebra F K] in
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_mul, zero_add, pow_one]`. Conclude with `fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)`. Consider the case `succ m ih`.

Rewrite using `[show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]`. Conclude with `idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc`.
-/
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} {j : ℕ} (hc : c ∉ 𝔭 ^ (j + 1))
    (m : ℕ) : c ^ m ∉ 𝔭 ^ (m * j + 1) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_mul, zero_add, pow_one]
    exact fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)
  | succ m ih =>
    rw [show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]
    exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc

/- English proof (translation)
Establish `e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) = algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j)`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.det_smul, Fintype.card_fin]`. Use `congr 1`.

Simplify using `only [map_pow]`. Both sides reduce to the same expression.
-/
theorem gram_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 F) (x : Fin (finrank K V) → V) :
    (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V)) *
        (Matrix.of fun i j => h (x i) (x j)).det := by
  have e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) =
      algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j) := by
    ext i j
    rfl
  rw [e, Matrix.det_smul, Fintype.card_fin]
  congr 1
  simp only [map_pow]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hle`. Unfold `discrIdeal`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `z ⟨x, hx, ez⟩`.

Apply `idealPowerSpanBounds.mem_of_mul_mem h𝔭 (pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V))` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises. Conclude with `Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩`. Introduce `hle`. Unfold `discrIdeal`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `z ⟨x, hx, ez⟩`. Take `⟨g, -, hdet⟩` from `LocF.exists_gram hLi x hx`. Establish `hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Use `show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _`. Rewrite using `[ez, gram_smul, map_mul, hdet]`. Establish `h1 : g.det ∈ extP K 𝔭 ^ e` using `hle (Ideal.subset_span ⟨x, hx, hdet⟩)`. Establish `h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c)`. Apply `localizedQuotients.ι_mem_pow` to reduce the goal to its premises.

Rewrite using `[mul_comm, pow_mul]`. Conclude with `Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _`. Use `show z ∈ _`. Rewrite using `[hz, pow_add]`. Conclude with `Ideal.mul_mem_mul h2 h1`.
-/
theorem discrIdeal_smul_le_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    apply idealPowerSpanBounds.mem_of_mul_mem h𝔭 (pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V))
    apply hle
    exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      apply localizedQuotients.ι_mem_pow
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1

/- English proof (translation)
Establish `hD` using `LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi`. Establish `hE : extP K 𝔭 ≠ ⊤`. Introduce `e`. Apply `h𝔭.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← pow_one 𝔭, ← idealPowerSpanBounds.mem_pow_iff (K := K), pow_one, e]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e}`. Assume the negation of the conclusion as `hnb`. Rewrite `hnb` using `[not_bddAbove_iff]`. Apply `hD` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]`. Use `le_iInf fun k => ?_` and prove the remaining obligations. Take `⟨e, he, hke⟩` from `hnb k`. Conclude with `he.trans (Ideal.pow_le_pow_right hke.le)`. Establish `hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e}` using `Nat.sSup_mem ⟨0, by simp⟩ hb`.

Establish `hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e} (vd h L 𝔭 + finrank K V * vF 𝔭 c)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[add_comm]`. Conclude with `(discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem`. Introduce `e' he'`.

Distinguish the cases in `hlt : e' ≤ finrank K V * vF 𝔭 c`. Use linear arithmetic over natural numbers and integers. Take `⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e` from `⟨e' - finrank K V * vF 𝔭 c, by omega⟩`. Establish `h1 : e ≤ vd h L 𝔭` using `le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')`. Use linear arithmetic over natural numbers and integers.

Conclude with `hg.csSup_eq`.
-/
theorem vd_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    vd (algebraMap F K (c : F) • h) L 𝔭 = vd h L 𝔭 + finrank K V * vF 𝔭 c := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hE : extP K 𝔭 ≠ ⊤ := by
    intro e
    apply h𝔭.ne_top
    rw [Ideal.eq_top_iff_one, ← pow_one 𝔭, ← idealPowerSpanBounds.mem_pow_iff (K := K), pow_one, e]
    trivial
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} :=
    Nat.sSup_mem ⟨0, by simp⟩ hb
  have hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e}
      (vd h L 𝔭 + finrank K V * vF 𝔭 c) := by
    constructor
    · rw [add_comm]
      exact (discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem
    · intro e' he'
      by_cases hlt : e' ≤ finrank K V * vF 𝔭 c
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e := ⟨e' - finrank K V * vF 𝔭 c, by omega⟩
        have h1 : e ≤ vd h L 𝔭 := le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')
        omega
  exact hg.csSup_eq

end Formalism.HermitianLattices.Ext.L3.PinA
