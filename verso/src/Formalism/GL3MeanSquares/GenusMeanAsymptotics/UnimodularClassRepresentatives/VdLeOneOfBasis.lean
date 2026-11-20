import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormalise
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range e) span_eq_top := by rw [eq_top_iff, ← e.span_eq] exact Submodule.span_mono Submodule.subset_span`.
-/
theorem isLattice_spanO {N : ℕ} (e : Basis (Fin N) K V) : Submodule.IsLattice K (spanO e) where
  fg := Submodule.fg_span (Set.finite_range e)
  span_eq_top := by
    rw [eq_top_iff, ← e.span_eq]
    exact Submodule.span_mono Submodule.subset_span

/- English proof (translation)
Introduce `x hx y hy`. Establish `hH : ∀ i j, κ ((Matrix.diagonal fun i => ι (A' i)) i j) = h (e i) (e j)`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, hn]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, map_zero, ho i j hij]`. Use `form_eq h e hH ⟨x, hx⟩ ⟨y, hy⟩` as an intermediate fact. Conclude with `Submodule.mem_one.2 ⟨_, this.symm⟩`.
-/
theorem integral_spanO {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i))) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (spanO e) := by
  intro x hx y hy
  have hH : ∀ i j, κ ((Matrix.diagonal fun i => ι (A' i)) i j) = h (e i) (e j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, hn]
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero, ho i j hij]
  have := form_eq h e hH ⟨x, hx⟩ ⟨y, hy⟩
  exact Submodule.mem_one.2 ⟨_, this.symm⟩

/- English proof (translation)
Substitute `hN` using the available equality. Unfold `vd`. Use `csSup_le' fun E hE => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Apply `hprod` to reduce the goal to its premises.

Rewrite using `[← mem_pow_iff (K := K)]`. Apply `Ideal.pow_le_pow_right (by omega : 2 ≤ E)` to reduce the goal to its premises. Apply `hE` to reduce the goal to its premises. Use `Ideal.subset_span ⟨e, fun i => Submodule.subset_span ⟨i, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: (Matrix.of fun i j => h (e i) (e j)) = Matrix.diagonal fun i => κ (ι (A' i))`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.of_apply, hn]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Matrix.of_apply, ho i j hij]`.

Rewrite using `[this, Matrix.det_diagonal, map_prod, map_prod]`.
-/
theorem vd_le_one_of_basis {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (hN : finrank K V = N)
    (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i)))
    (hprod : ∏ i, A' i ∉ 𝔭 ^ 2) : vd h (spanO e) 𝔭 ≤ 1 := by
  subst hN
  unfold vd
  refine csSup_le' fun E hE => ?_
  by_contra hlt
  apply hprod
  rw [← mem_pow_iff (K := K)]
  apply Ideal.pow_le_pow_right (by omega : 2 ≤ E)
  apply hE
  refine Ideal.subset_span ⟨e, fun i => Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  have : (Matrix.of fun i j => h (e i) (e j)) = Matrix.diagonal fun i => κ (ι (A' i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Matrix.of_apply, hn]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.of_apply, ho i j hij]
  rw [this, Matrix.det_diagonal, map_prod, map_prod]

variable [FiniteDimensional K V]

/- English proof (translation)
Establish `hp` using `h𝔭.isPrime`. Establish `hp0` using `ne_bot h𝔭`. Establish `han` using `LocF.aniso_of_totPosDef hd`. Establish `hx0 : x₀ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx` using `[map_zero]`. Conclude with `κι_ne_zero (K := K) (ne_zero_of_notMem hn) hx.symm`. Establish `hm : 0 < finrank K V` using `Module.finrank_pos_iff_exists_ne_zero.2 ⟨x₀, hx0⟩`. Take `⟨r, hr⟩ : ∃ r, finrank K V = r + 1` from `⟨finrank K V - 1, by omega⟩`. Take `⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩` from `exists_family hK hF h𝔭 hs han hx hn r (by omega)`.

Establish `hof : ∀ i j, i ≠ j → h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) j) = 0`. Introduce `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Introduce `hij`. Conclude with `absurd rfl hij`.

Introduce `_`. Rewrite using `[Fin.cons_zero, Fin.cons_succ]`. Conclude with `hzy j`. Introduce `_`. Rewrite using `[Fin.cons_zero, Fin.cons_succ]`.

Conclude with `symm0 hs (hzy i)`. Introduce `hij`. Rewrite using `[Fin.cons_succ, Fin.cons_succ]`. Conclude with `ho i j fun hh => hij (by rw [hh])`. Establish `hnf : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) = κ (ι ((Fin.cons c a : Fin (r + 1) → 𝓞 F) i))`.

Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.cons_zero, Fin.cons_zero]`. Conclude with `hnz`. Rewrite using `[Fin.cons_succ, Fin.cons_succ]`.

Conclude with `hny i`. Establish `hP : ∏ i, (Fin.cons c a : Fin (r + 1) → 𝓞 F) i ∉ 𝔭 ^ 2`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Establish `hc2' : c ∉ 𝔭 ^ (1 + 1)` using `by simpa using hc2`.

Establish `hprod' : (∏ i, a i) ∉ 𝔭 ^ (0 + 1)` using `by simpa using hprod`. Use `mul_notMem hp hp0 hc2' hprod'` as an intermediate fact. Simplify using `using this`. Establish `hne : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) ≠ 0`. Introduce `i`.

Rewrite using `[hnf]`. Use `κι_ne_zero fun h0 => hP ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) h0]`. Conclude with `zero_mem _`. Take `⟨e, he⟩` from `GramDeterminantPositive.exists_basis_of_ortho h _ hr hof hne`.

Use `⟨spanO e, isLattice_spanO e, integral_spanO e _ (fun i j hij => by rw [he, he]; exact hof i j hij) (fun i => by rw [he]; exact hnf i), ?_, vd_le_one_of_basis hr e _ (fun i j hij => by rw [he, he]; exact hof i j hij) (fun i => by rw [he]; exact hnf i) hP⟩` and prove the remaining obligations. Break down `hx₀ with rfl | ⟨i, hi⟩` into its components or cases. Conclude with `Submodule.subset_span ⟨0, by rw [he, Fin.cons_zero]⟩`. Conclude with `Submodule.subset_span ⟨i.succ, by rw [he, Fin.cons_succ, hi]⟩`.
-/
theorem exists_lattice (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  have han := LocF.aniso_of_totPosDef hd
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact κι_ne_zero (K := K) (ne_zero_of_notMem hn) hx.symm
  have hm : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x₀, hx0⟩
  obtain ⟨r, hr⟩ : ∃ r, finrank K V = r + 1 := ⟨finrank K V - 1, by omega⟩
  obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ :=
    exists_family hK hF h𝔭 hs han hx hn r (by omega)
  have hof : ∀ i j, i ≠ j → h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) j) = 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact absurd rfl hij
    · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact hzy j
    · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (hzy i)
    · intro hij
      rw [Fin.cons_succ, Fin.cons_succ]
      exact ho i j fun hh => hij (by rw [hh])
  have hnf : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) =
      κ (ι ((Fin.cons c a : Fin (r + 1) → 𝓞 F) i)) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, Fin.cons_zero]; exact hnz
    · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
  have hP : ∏ i, (Fin.cons c a : Fin (r + 1) → 𝓞 F) i ∉ 𝔭 ^ 2 := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hc2' : c ∉ 𝔭 ^ (1 + 1) := by simpa using hc2
    have hprod' : (∏ i, a i) ∉ 𝔭 ^ (0 + 1) := by simpa using hprod
    have := mul_notMem hp hp0 hc2' hprod'
    simpa using this
  have hne : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) ≠ 0 := by
    intro i
    rw [hnf]
    refine κι_ne_zero fun h0 => hP ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    exact zero_mem _
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h _ hr hof hne
  refine ⟨spanO e, isLattice_spanO e,
    integral_spanO e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
      (fun i => by rw [he]; exact hnf i), ?_,
    vd_le_one_of_basis hr e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
      (fun i => by rw [he]; exact hnf i) hP⟩
  rcases hx₀ with rfl | ⟨i, hi⟩
  · exact Submodule.subset_span ⟨0, by rw [he, Fin.cons_zero]⟩
  · exact Submodule.subset_span ⟨i.succ, by rw [he, Fin.cons_succ, hi]⟩

end Formalism.HermitianLattices.Ext.L3.Cell
