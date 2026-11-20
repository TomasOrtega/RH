import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `ρ hρ Δ hl`. Take `⟨σ, hσ, c, d, c', d', h1, h2, e1, e2⟩` from `hl.exists_eq_icc`. Establish `hlen : (Segment.single ρ hρ).len = 1` using `rfl`. Establish `hfst : (Segment.single ρ hρ).first = ρ` using `Segment.first_ofFirst _ _ _ _`. Rewrite `hl` using `[e1, e2, Segment.linked_icc]`.

Rewrite `hlen`, `hfst` using `[e1]`. Simplify using `only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst] at hlen hfst`. Establish `hdc : d = c` using `by omega`. Substitute `hdc e2 hfst` using the available equality. Simplify using `only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst, IrrGL.nu_nu]`.

Break down `hl with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩` into its components or cases. Use `left`. Take `rfl : c' = d + 1` from `by omega`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `right`. Take `rfl : d = d' + 1` from `by omega`. Rewrite using `[show (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) by`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linkP : LinkP k := by
  intro ρ hρ Δ hl
  obtain ⟨σ, hσ, c, d, c', d', h1, h2, e1, e2⟩ := hl.exists_eq_icc
  have hlen : (Segment.single ρ hρ).len = 1 := rfl
  have hfst : (Segment.single ρ hρ).first = ρ := Segment.first_ofFirst _ _ _ _
  rw [e1, e2, Segment.linked_icc] at hl
  rw [e1] at hlen hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst] at hlen hfst
  have hdc : d = c := by omega
  subst hdc e2 hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst, IrrGL.nu_nu]
  rcases hl with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · left
    obtain rfl : c' = d + 1 := by omega
    congr 1
    push_cast
    ring
  · right
    obtain rfl : d = d' + 1 := by omega
    rw [show (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    congr 1
    push_cast
    ring

private def Above (a b : IrrGL k) : Prop := 0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ)

/- English proof (translation)
Establish `hsub : (Segment.icc ρ hρ n n le_rfl).carrier ⊆ (Segment.icc ρ hρ 0 0 le_rfl).carrier`. Introduce `x hx`. Rewrite `hx`, the goal using `[Segment.mem_icc]`. Take `⟨a, ha1, ha2, rfl⟩` from `hx`. Take `rfl : a = n` from `le_antisymm ha2 ha1`.

Use `⟨0, le_rfl, le_rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Simplify using `[IrrGL.nu_zero]`. Use `Segment.icc_subset_icc.mp hsub` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem eq_zero_of_nu_eq_of_isCusp {ρ : IrrGL k} (hρ : ρ.IsCusp) (n : ℤ) (h : ρ.nu (n : ℂ) = ρ) : n = 0 := by
  have hsub : (Segment.icc ρ hρ n n le_rfl).carrier ⊆ (Segment.icc ρ hρ 0 0 le_rfl).carrier := by
    intro x hx
    rw [Segment.mem_icc] at hx ⊢
    obtain ⟨a, ha1, ha2, rfl⟩ := hx
    obtain rfl : a = n := le_antisymm ha2 ha1
    refine ⟨0, le_rfl, le_rfl, ?_⟩
    rw [h]
    simp [IrrGL.nu_zero]
  have := Segment.icc_subset_icc.mp hsub
  omega

/- English proof (translation)
Introduce `l hl hc`. Take `⟨ρ₀, h₀⟩` from `List.exists_mem_of_ne_nil l hl`. Use `set f : ℕ → IrrGL k := fun m => ρ₀.nu (-(m : ℂ)) with hf`. Establish `hinj : Function.Injective f`. Introduce `m m' hmm`.

Establish `h1 : (f m).nu (m : ℂ) = (f m').nu (m : ℂ)` using `by rw [hmm]`. Simplify using `only [hf, IrrGL.nu_nu, neg_add_cancel, IrrGL.nu_zero] at h1`. Establish `h2 : ρ₀.nu (((m : ℤ) - m' : ℤ) : ℂ) = ρ₀` using `by conv_rhs => rw [h1]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `eq_zero_of_nu_eq_of_isCusp (hc ρ₀ h₀) _ h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hfin : {m : ℕ | f m ∈ l}.Finite`. Use `((l.toFinset.finite_toSet).preimage hinj.injOn).subset ?_` and prove the remaining obligations.

Introduce `m hm`. Simplify using `using hm`. Establish `h0 : (0 : ℕ) ∈ hfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset]`. Use `show f 0 ∈ l`.

Simplify `h₀` using `[hf, IrrGL.nu_zero]`. Use `set M := hfin.toFinset.max' ⟨0, h0⟩ with hMdef`. Establish `hM : f M ∈ l`. Establish `hm` using `hfin.toFinset.max'_mem ⟨0, h0⟩`. Rewrite `hm` using `[Set.Finite.mem_toFinset]`.

Conclude with `hm`. Use `⟨f M, hM, fun ρ' hρ' j hj heq => ?_⟩` and prove the remaining obligations. Establish `hρ'eq : ρ' = f (M + j)`. Establish `h3 : (f M).nu (-(j : ℂ)) = ρ'`. Rewrite using `[heq, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]`.

Rewrite using `[← h3]`. Simplify using `only [hf, IrrGL.nu_nu]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmem : M + j ∈ hfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset]`. Use `show f (M + j) ∈ l`. Rewrite using `[← hρ'eq]`. Conclude with `hρ'`.

Use `hfin.toFinset.le_max' _ hmem` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem minP : MinP k := by
  classical
  intro l hl hc
  obtain ⟨ρ₀, h₀⟩ := List.exists_mem_of_ne_nil l hl
  set f : ℕ → IrrGL k := fun m => ρ₀.nu (-(m : ℂ)) with hf
  have hinj : Function.Injective f := by
    intro m m' hmm
    have h1 : (f m).nu (m : ℂ) = (f m').nu (m : ℂ) := by rw [hmm]
    simp only [hf, IrrGL.nu_nu, neg_add_cancel, IrrGL.nu_zero] at h1
    have h2 : ρ₀.nu (((m : ℤ) - m' : ℤ) : ℂ) = ρ₀ := by
      conv_rhs => rw [h1]
      congr 1
      push_cast
      ring
    have := eq_zero_of_nu_eq_of_isCusp (hc ρ₀ h₀) _ h2
    omega
  have hfin : {m : ℕ | f m ∈ l}.Finite := by
    refine ((l.toFinset.finite_toSet).preimage hinj.injOn).subset ?_
    intro m hm
    simpa using hm
  have h0 : (0 : ℕ) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f 0 ∈ l
    simpa [hf, IrrGL.nu_zero] using h₀
  set M := hfin.toFinset.max' ⟨0, h0⟩ with hMdef
  have hM : f M ∈ l := by
    have hm := hfin.toFinset.max'_mem ⟨0, h0⟩
    rw [Set.Finite.mem_toFinset] at hm
    exact hm
  refine ⟨f M, hM, fun ρ' hρ' j hj heq => ?_⟩
  have hρ'eq : ρ' = f (M + j) := by
    have h3 : (f M).nu (-(j : ℂ)) = ρ' := by
      rw [heq, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
    rw [← h3]
    simp only [hf, IrrGL.nu_nu]
    congr 1
    push_cast
    ring
  have hmem : M + j ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f (M + j) ∈ l
    rw [← hρ'eq]
    exact hρ'
  have := hfin.toFinset.le_max' _ hmem
  omega

end PositivityTheory.Exh

end
