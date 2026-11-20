import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementD

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M

namespace LatticeBasis

variable {p : ℕ} [Fact p.Prime] {σ : Type}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f0, rfl⟩ m`. Simplify using `only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]`. Conclude with `PadicInt.norm_le_one (coeff m f0)`. Introduce `h`.

Establish `: (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p])`. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_coe, mem_coeffs_iff]`. Take `⟨m, _, rfl⟩` from `ha`. Conclude with `⟨⟨x.coeff m, h m⟩, rfl⟩`.

Rewrite `this` using `[← mem_range_map_iff_coeffs_subset]`. Simplify `this` using `[IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range]`.
-/
theorem mem_intPol_iff (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  constructor
  · rintro ⟨f0, rfl⟩ m
    simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
    exact PadicInt.norm_le_one (coeff m f0)
  · intro h
    have : (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
      intro a ha
      rw [Finset.mem_coe, mem_coeffs_iff] at ha
      obtain ⟨m, _, rfl⟩ := ha
      exact ⟨⟨x.coeff m, h m⟩, rfl⟩
    rw [← mem_range_map_iff_coeffs_subset] at this
    simpa [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range] using this

/- English proof (translation)
Take `⟨x, hxU, hx0⟩` from `(Submodule.ne_bot_iff U).mp hU`. Establish `hne : x.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hx0 (support_eq_empty.mp h)`.

Take `⟨m, hm, hmax⟩` from `Finset.exists_max_image x.support (fun m => ‖x.coeff m‖) hne`. Establish `ha : x.coeff m ≠ 0` using `mem_support_iff.mp hm`. Use `⟨(x.coeff m)⁻¹ • x, U.smul_mem _ hxU, m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul, inv_mul_cancel₀ ha]`. Rewrite using `[mem_intPol_iff]`.

Introduce `n`. Rewrite using `[coeff_smul, smul_eq_mul, norm_mul, norm_inv]`. Establish `hpos : 0 < ‖x.coeff m‖` using `norm_pos_iff.mpr ha`. Rewrite using `[inv_mul_le_iff₀ hpos, mul_one]`. Distinguish the cases in `hn : n ∈ x.support`.

Conclude with `hmax n hn`. Rewrite using `[notMem_support_iff.mp hn, norm_zero]`. Conclude with `hpos.le`.
-/
theorem exists_unit_coeff (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (hU : U ≠ ⊥) :
    ∃ x₀ ∈ U, ∃ m, x₀.coeff m = 1 ∧ x₀ ∈ IntPol p σ := by
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hne : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hx0 (support_eq_empty.mp h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image x.support (fun m => ‖x.coeff m‖) hne
  have ha : x.coeff m ≠ 0 := mem_support_iff.mp hm
  refine ⟨(x.coeff m)⁻¹ • x, U.smul_mem _ hxU, m, ?_, ?_⟩
  · rw [coeff_smul, smul_eq_mul, inv_mul_cancel₀ ha]
  · rw [mem_intPol_iff]
    intro n
    rw [coeff_smul, smul_eq_mul, norm_mul, norm_inv]
    have hpos : 0 < ‖x.coeff m‖ := norm_pos_iff.mpr ha
    rw [inv_mul_le_iff₀ hpos, mul_one]
    by_cases hn : n ∈ x.support
    · exact hmax n hn
    · rw [notMem_support_iff.mp hn, norm_zero]
      exact hpos.le

/- English proof (translation)
Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `U hfd hd`. Distinguish the cases in `hU : U = ⊥`. Substitute `hU` using the available equality.

Use `⟨0, Fin.elim0, linearIndependent_empty_type, by simp, fun i => i.elim0, ?_⟩` and prove the remaining obligations. Introduce `x hx _`. Conclude with `⟨Fin.elim0, fun i => i.elim0, by simpa using hx⟩`. Take `⟨x₀, hx₀U, m, hm1, hx₀I⟩` from `exists_unit_coeff U hU set U' : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) := U ⊓ LinearMap.ker (lcoeff ℚ_[p] m) with hU'`. Establish `hle : U' ≤ U` using `inf_le_left`.

Establish `hx₀U' : x₀ ∉ U'`. Introduce `h`. Establish `: x₀.coeff m = 0` using `by simpa using (Submodule.mem_inf.mp h).2`. Rewrite `this` using `[hm1]`. Conclude with `one_ne_zero this`.

Establish `hlt : U' < U` using `lt_of_le_of_ne hle (fun h => hx₀U' (h ▸ hx₀U))`. Establish `hfd' : FiniteDimensional ℚ_[p] U'` using `Submodule.finiteDimensional_of_le hle`. Establish `hrk : Module.finrank ℚ_[p] U' < d` using `hd ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨k, b, hli, hsp, hbI, hco⟩` from `ih _ hrk U' hfd' rfl`. Establish `hsplit : ∀ x ∈ U, x - x.coeff m • x₀ ∈ U'`.

Introduce `x hx`. Use `Submodule.mem_inf.mpr ⟨U.sub_mem hx (U.smul_mem _ hx₀U), ?_⟩` and prove the remaining obligations. Simplify using `[hm1]`. Use `⟨k + 1, Fin.cons x₀ b, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_finCons]`.

Conclude with `⟨hli, by rw [hsp]; exact hx₀U'⟩`. Rewrite using `[Fin.range_cons, Submodule.span_insert, hsp]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₀U) hle`. Introduce `x hx`.

Establish `: x = x.coeff m • x₀ + (x - x.coeff m • x₀)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (hsplit x hx)`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using hx₀I`. Simplify using `using hbI j`. Introduce `x hx hxI`. Establish `hc : ‖x.coeff m‖ ≤ 1` using `(mem_intPol_iff x).mp hxI m`. Establish `hI' : x - x.coeff m • x₀ ∈ IntPol p σ`.

Rewrite using `[mem_intPol_iff]`. Introduce `n`. Rewrite using `[coeff_sub, coeff_smul, smul_eq_mul, sub_eq_add_neg]`. Use `(Padic.nonarchimedean _ _).trans (max_le ((mem_intPol_iff x).mp hxI n) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`.

Conclude with `mul_le_one₀ hc (norm_nonneg _) ((mem_intPol_iff x₀).mp hx₀I n)`. Take `⟨c, hc1, hxc⟩` from `hco _ (hsplit x hx) hI'`. Use `⟨Fin.cons (x.coeff m) c, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using hc`. Simplify using `using hc1 j`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← hxc]`.

Normalize the expressions using the abelian group laws.
-/
theorem exists_family (d : ℕ) : ∀ (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    Module.finrank ℚ_[p] U = d →
    ∃ (k : ℕ) (b : Fin k → MvPolynomial σ ℚ_[p]), LinearIndependent ℚ_[p] b ∧
      Submodule.span ℚ_[p] (Set.range b) = U ∧ (∀ i, b i ∈ IntPol p σ) ∧
      ∀ x ∈ U, x ∈ IntPol p σ → ∃ c : Fin k → ℚ_[p], (∀ i, ‖c i‖ ≤ 1) ∧ x = ∑ i, c i • b i := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hfd hd
    by_cases hU : U = ⊥
    · subst hU
      refine ⟨0, Fin.elim0, linearIndependent_empty_type, by simp, fun i => i.elim0, ?_⟩
      intro x hx _
      exact ⟨Fin.elim0, fun i => i.elim0, by simpa using hx⟩
    · obtain ⟨x₀, hx₀U, m, hm1, hx₀I⟩ := exists_unit_coeff U hU
      set U' : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) := U ⊓ LinearMap.ker (lcoeff ℚ_[p] m) with hU'
      have hle : U' ≤ U := inf_le_left
      have hx₀U' : x₀ ∉ U' := by
        intro h
        have : x₀.coeff m = 0 := by simpa using (Submodule.mem_inf.mp h).2
        rw [hm1] at this
        exact one_ne_zero this
      have hlt : U' < U := lt_of_le_of_ne hle (fun h => hx₀U' (h ▸ hx₀U))
      have hfd' : FiniteDimensional ℚ_[p] U' := Submodule.finiteDimensional_of_le hle
      have hrk : Module.finrank ℚ_[p] U' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨k, b, hli, hsp, hbI, hco⟩ := ih _ hrk U' hfd' rfl
      have hsplit : ∀ x ∈ U, x - x.coeff m • x₀ ∈ U' := by
        intro x hx
        refine Submodule.mem_inf.mpr ⟨U.sub_mem hx (U.smul_mem _ hx₀U), ?_⟩
        simp [hm1]
      refine ⟨k + 1, Fin.cons x₀ b, ?_, ?_, ?_, ?_⟩
      · rw [linearIndependent_finCons]
        exact ⟨hli, by rw [hsp]; exact hx₀U'⟩
      · rw [Fin.range_cons, Submodule.span_insert, hsp]
        apply le_antisymm
        · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₀U) hle
        · intro x hx
          have : x = x.coeff m • x₀ + (x - x.coeff m • x₀) := by abel
          rw [this]
          exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (hsplit x hx)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx₀I
        · simpa using hbI j
      · intro x hx hxI
        have hc : ‖x.coeff m‖ ≤ 1 := (mem_intPol_iff x).mp hxI m
        have hI' : x - x.coeff m • x₀ ∈ IntPol p σ := by
          rw [mem_intPol_iff]
          intro n
          rw [coeff_sub, coeff_smul, smul_eq_mul, sub_eq_add_neg]
          refine (Padic.nonarchimedean _ _).trans (max_le ((mem_intPol_iff x).mp hxI n) ?_)
          rw [norm_neg, norm_mul]
          exact mul_le_one₀ hc (norm_nonneg _) ((mem_intPol_iff x₀).mp hx₀I n)
        obtain ⟨c, hc1, hxc⟩ := hco _ (hsplit x hx) hI'
        refine ⟨Fin.cons (x.coeff m) c, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hc
          · simpa using hc1 j
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hxc]
          abel

end LatticeBasis

/- English proof (translation)
Introduce `p _ σ U hfd`. Take `⟨k, b, hli, hsp, hbI, hco⟩` from `LatticeBasis.exists_family (p := p) (σ := σ) _ U hfd rfl`. Substitute `hsp` using the available equality. Use `⟨k, Module.Basis.span hli, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Rewrite using `[Module.Basis.span_apply]`. Conclude with `hbI i`. Introduce `x hx i`. Take `⟨c, hc1, hxc⟩` from `hco x.1 x.2 hx`. Establish `hx' : x = ∑ j, c j • Module.Basis.span hli j`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hxc]`. Simplify using `[Module.Basis.span_apply]`. Rewrite using `[hx', Module.Basis.repr_sum_self]`. Conclude with `hc1 i`.
-/
theorem lattice_basis_polynomial : LatBasisPol := by
  intro p _ σ U hfd
  obtain ⟨k, b, hli, hsp, hbI, hco⟩ := LatticeBasis.exists_family (p := p) (σ := σ) _ U hfd rfl
  subst hsp
  refine ⟨k, Module.Basis.span hli, ?_, ?_⟩
  · intro i
    rw [Module.Basis.span_apply]
    exact hbI i
  · intro x hx i
    obtain ⟨c, hc1, hxc⟩ := hco x.1 x.2 hx
    have hx' : x = ∑ j, c j • Module.Basis.span hli j := by
      apply Subtype.ext
      rw [hxc]
      simp [Module.Basis.span_apply]
    rw [hx', Module.Basis.repr_sum_self]
    exact hc1 i

end Formalism.InvariantFactorPaths.PW
