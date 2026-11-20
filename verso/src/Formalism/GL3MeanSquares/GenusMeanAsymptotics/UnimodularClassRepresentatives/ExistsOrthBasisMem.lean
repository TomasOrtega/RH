import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanSingletonEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Take `⟨e, he, -⟩` from `orthBasisPos K hK V h hs hd`. Use `choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (e i)`. Establish `hb : ∀ i, e.unitsSMul (fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i))) i = (n i : K) • e i` using `fun i => by rw [Basis.unitsSMul_apply]; rfl`. Use `⟨e.unitsSMul fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i)), fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hb, Int.cast_smul_eq_zsmul]`.

Conclude with `hnx i`. Simplify using `only [hb, map_smulₛₗ, LinearMap.smul_apply, he i j hij, smul_zero]`.
-/
theorem exists_orth_basis_mem [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) :
    ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧ ∀ i j, i ≠ j → h (b i) (b j) = 0 := by
  obtain ⟨e, he, -⟩ := orthBasisPos K hK V h hs hd
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (e i)
  have hb : ∀ i, e.unitsSMul (fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i))) i =
      (n i : K) • e i := fun i => by rw [Basis.unitsSMul_apply]; rfl
  refine ⟨e.unitsSMul fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i)), fun i => ?_,
    fun i j hij => ?_⟩
  · rw [hb, Int.cast_smul_eq_zsmul]; exact hnx i
  · simp only [hb, map_smulₛₗ, LinearMap.smul_apply, he i j hij, smul_zero]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `j _ hj`. Simplify using `[ho j i hj]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem form_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V) :
    h x x = ∑ i, star (b.repr x i) * b.repr x i * h (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    simp [ho j i hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Rewrite using `[form_eq b ho x, map_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, mul_comm]`.
-/
theorem re_form_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (φ : K →+* ℂ) :
    (φ (h x x)).re = ∑ i, (φ (h (b i) (b i))).re * Complex.normSq (φ (b.repr x i)) := by
  rw [form_eq b ho x, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, mul_comm]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `: IsTotallyComplex K` using `hK.1`. Prove the components needed by the constructor for the conclusion. Introduce `hφ w`. Rewrite using `[← re_form_eq hK b ho]`. Conclude with `hφ _`.

Introduce `hw φ`. Establish `h1` using `hw ⟨InfinitePlace.mk φ, IsTotallyComplex.isComplex _⟩`. Rewrite `h1` using `[← re_form_eq hK b ho]`. Break down `InfinitePlace.embedding_mk_eq φ with h2 | h2` into its components or cases. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.

Rewrite `h1` using `[h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]`. Then use the resulting hypothesis.
-/
theorem forall_embedding_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (T : ℝ) :
    (∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) ↔ ∀ w : {w : InfinitePlace K // w.IsComplex},
      ∑ i, (w.1.embedding (h (b i) (b i))).re * Complex.normSq (w.1.embedding (b.repr x i)) ≤ T := by
  have : IsTotallyComplex K := hK.1
  constructor
  · intro hφ w
    rw [← re_form_eq hK b ho]
    exact hφ _
  · intro hw φ
    have h1 := hw ⟨InfinitePlace.mk φ, IsTotallyComplex.isComplex _⟩
    rw [← re_form_eq hK b ho] at h1
    rcases InfinitePlace.embedding_mk_eq φ with h2 | h2
    · rwa [h2] at h1
    · rwa [h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1

/- English proof (translation)
Unfold `gdet`. Rewrite using `[← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, ho i j hij]`.
-/
theorem gdet_eq_prod {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) : gdet h b = ∏ i, h (b i) (b i) := by
  unfold gdet
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, ho i j hij]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `h1 : star (h x x) = h x x` using `hs.eq x x`. Establish `h2 : (w.embedding (h x x)).im = 0`. Rewrite using `[← Complex.conj_eq_iff_im, ← hK.2.1, h1]`. Rewrite using `[← InfinitePlace.norm_embedding_eq, ← Complex.abs_re_eq_norm.2 h2, abs_of_pos (hd x hx w.embedding)]`.
-/
theorem place_form_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {x : V} (hx : x ≠ 0) (w : InfinitePlace K) :
    w (h x x) = (w.embedding (h x x)).re := by
  have h1 : star (h x x) = h x x := hs.eq x x
  have h2 : (w.embedding (h x x)).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← hK.2.1, h1]
  rw [← InfinitePlace.norm_embedding_eq, ← Complex.abs_re_eq_norm.2 h2,
    abs_of_pos (hd x hx w.embedding)]

open scoped Classical in
/- English proof (translation)
Establish `: IsTotallyComplex K` using `hK.1`. Rewrite using `[← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace K => IsTotallyComplex.isComplex w)).prod_comp]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[gdet_eq_prod b ho, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `place_form_eq hK hs hd (b.ne_zero i) _`.
-/
theorem prod_place_gdet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (b : Basis (Fin (finrank K V)) K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) :
    ∏ w : InfinitePlace K, w (gdet h b) =
      ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have : IsTotallyComplex K := hK.1
  rw [← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace K => IsTotallyComplex.isComplex w)).prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [gdet_eq_prod b ho, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact place_form_eq hK hs hd (b.ne_zero i) _

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Set.finite_range b).toFinset, by rw [Set.Finite.coe_toFinset]⟩ span_eq_top := by rw [eq_top_iff, ← b.span_eq] exact Submodule.span_mono Submodule.subset_span`.
-/
theorem isLattice_span [FiniteDimensional K V] (b : Basis (Fin (finrank K V)) K V) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range b)) where
  fg := ⟨(Set.finite_range b).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  span_eq_top := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span

end Formalism.HermitianLattices.Ext.L3.BallB
