import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `ρ hρ Δ H`. Take `⟨σ, hσ, c, d, c', d', h, h', e1, rfl⟩` from `H.exists_eq_icc`. Establish `hfirst : ρ = σ.nu (c : ℂ)`. Use `congrArg Segment.first e1` as an intermediate fact. Simplify `this` using `[Segment.single, Segment.icc]`.

Establish `hlen : (1 : ℕ) = (d - c + 1).toNat`. Use `congrArg Segment.len e1` as an intermediate fact. Simplify `this` using `[Segment.single, Segment.icc]`. Establish `hdc : d = c` using `by omega`. Rewrite `H` using `[e1, Segment.linked_icc]`.

Establish `hinj : ∀ a b : ℤ, a = b → σ.nu (a : ℂ) = σ.nu (b : ℂ)` using `fun a b e => by rw [e]`. Establish `hF : (Segment.icc σ hσ c' d' h').first = σ.nu (c' : ℂ)` using `rfl`. Establish `hL : (Segment.icc σ hσ c' d' h').len = (d' - c' + 1).toNat` using `rfl`. Break down `H with ⟨h1, h2, -⟩ | ⟨h1, h2, h3⟩` into its components or cases. Use `left`.

Rewrite using `[hF, hfirst, IrrGL.nu_nu, show (c : ℂ) + 1 = ((c + 1 : ℤ) : ℂ) by push_cast; ring]`. Conclude with `hinj _ _ (by omega)`. Use `right`. Establish `ht : (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]`.

Rewrite using `[hF, hL, hfirst, IrrGL.nu_nu, ht, show (c' : ℂ) + ((d' - c' + 1 : ℤ) : ℂ) = ((c' + (d' - c' + 1) : ℤ) : ℂ) by push_cast; ring]`. Conclude with `hinj _ _ (by omega)`.
-/
theorem linkP : LinkP k := by
  intro ρ hρ Δ H
  obtain ⟨σ, hσ, c, d, c', d', h, h', e1, rfl⟩ := H.exists_eq_icc
  have hfirst : ρ = σ.nu (c : ℂ) := by
    have := congrArg Segment.first e1
    simpa [Segment.single, Segment.icc] using this
  have hlen : (1 : ℕ) = (d - c + 1).toNat := by
    have := congrArg Segment.len e1
    simpa [Segment.single, Segment.icc] using this
  have hdc : d = c := by omega
  rw [e1, Segment.linked_icc] at H
  have hinj : ∀ a b : ℤ, a = b → σ.nu (a : ℂ) = σ.nu (b : ℂ) := fun a b e => by rw [e]
  have hF : (Segment.icc σ hσ c' d' h').first = σ.nu (c' : ℂ) := rfl
  have hL : (Segment.icc σ hσ c' d' h').len = (d' - c' + 1).toNat := rfl
  rcases H with ⟨h1, h2, -⟩ | ⟨h1, h2, h3⟩
  · left
    rw [hF, hfirst, IrrGL.nu_nu, show (c : ℂ) + 1 = ((c + 1 : ℤ) : ℂ) by push_cast; ring]
    exact hinj _ _ (by omega)
  · right
    have ht : (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hF, hL, hfirst, IrrGL.nu_nu, ht, show (c' : ℂ) + ((d' - c' + 1 : ℤ) : ℂ) = ((c' + (d' - c' + 1) : ℤ) : ℂ) by push_cast; ring]
    exact hinj _ _ (by omega)

private def Above (a b : IrrGL k) : Prop := 0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ)

/- English proof (translation)
Proceed by induction on `H with`. Consider the case `single H => exact H`. Consider the case `tail _ H ih`. Take `⟨ha, i, hi, e⟩` from `ih`. Take `⟨-, j, hj, e'⟩` from `H`.

Conclude with `⟨ha, i + j, by omega, by rw [e, e', IrrGL.nu_nu, Nat.cast_add, add_comm]⟩`.
-/
private theorem above_transGen {a b : IrrGL k} (H : Relation.TransGen Above a b) :
    0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ) := by
  induction H with
  | single H => exact H
  | tail _ H ih =>
    obtain ⟨ha, i, hi, e⟩ := ih
    obtain ⟨-, j, hj, e'⟩ := H
    exact ⟨ha, i + j, by omega, by rw [e, e', IrrGL.nu_nu, Nat.cast_add, add_comm]⟩

/- English proof (translation)
Introduce `H` and use `by obtain ⟨ha, j, hj, e⟩ := above_transGen H have : a.nu ((0 : ℕ) : ℂ) = a.nu ((j : ℕ) : ℂ) := by simpa using e exact hj.ne ((IrrGL.nu_natCast_inj ha).1 this)`.
-/
private theorem not_above_transGen_self (a : IrrGL k) : ¬ Relation.TransGen Above a a := fun H => by
  obtain ⟨ha, j, hj, e⟩ := above_transGen H
  have : a.nu ((0 : ℕ) : ℂ) = a.nu ((j : ℕ) : ℂ) := by simpa using e
  exact hj.ne ((IrrGL.nu_natCast_inj ha).1 this)

/- English proof (translation)
Introduce `l hl hc`. Take `⟨l', hl', hp⟩` from `exists_list_pairwise_not_rel (not_above_transGen_self (k := k)) (l : Multiset (IrrGL k))`. Establish `hmem : ∀ x, x ∈ l' ↔ x ∈ l` using `fun x => by`. Rewrite using `[← Multiset.mem_coe, hl', Multiset.mem_coe]`. Consider the cases of `l' with`.

Consider the case `nil`. It suffices to derive a contradiction. Apply `hl` to reduce the goal to its premises. Use `congrArg Multiset.card hl'` as an intermediate fact. Simplify using `using this.symm`.

Consider the case `cons ρ t`. Establish `hρ : ρ ∈ l` using `(hmem ρ).1 (List.mem_cons_self ..)`. Use `⟨ρ, hρ, fun ρ' hρ' j hj e => ?_⟩` and prove the remaining obligations. Establish `hA : Above ρ ρ'` using `⟨(hc ρ hρ).1, j, hj, e⟩`. Break down `List.mem_cons.1 ((hmem ρ').2 hρ') with h0 | ht` into its components or cases.

Conclude with `not_above_transGen_self ρ (.single (h0 ▸ hA))`. Conclude with `(List.pairwise_cons.1 hp).1 ρ' ht hA`.
-/
theorem minP : MinP k := by
  intro l hl hc
  obtain ⟨l', hl', hp⟩ := exists_list_pairwise_not_rel (not_above_transGen_self (k := k)) (l : Multiset (IrrGL k))
  have hmem : ∀ x, x ∈ l' ↔ x ∈ l := fun x => by
    rw [← Multiset.mem_coe, hl', Multiset.mem_coe]
  cases l' with
  | nil =>
    exfalso
    apply hl
    have := congrArg Multiset.card hl'
    simpa using this.symm
  | cons ρ t =>
    have hρ : ρ ∈ l := (hmem ρ).1 (List.mem_cons_self ..)
    refine ⟨ρ, hρ, fun ρ' hρ' j hj e => ?_⟩
    have hA : Above ρ ρ' := ⟨(hc ρ hρ).1, j, hj, e⟩
    rcases List.mem_cons.1 ((hmem ρ').2 hρ') with h0 | ht
    · exact not_above_transGen_self ρ (.single (h0 ▸ hA))
    · exact (List.pairwise_cons.1 hp).1 ρ' ht hA

end CompanionTheory.Exh

end
