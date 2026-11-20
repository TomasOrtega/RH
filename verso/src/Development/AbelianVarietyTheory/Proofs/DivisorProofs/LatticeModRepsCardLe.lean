import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ r M Λ hM hfg`. Set `L : Submodule ℤ (Fin r → E)` to `Λ.restrictScalars ℤ`. Establish `hLfg : L.FG` using `hfg.restrictScalars`. Use `haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hLfg`. Use `haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'`.

Set `ι` to `Module.Free.ChooseBasisIndex ℤ L`. Set `b` to `Module.Free.chooseBasis ℤ L`. Establish `hli : LinearIndependent ℤ (fun i => (b i : Fin r → E))` using `b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)`. Establish `hliQ : LinearIndependent ℚ (fun i => (b i : Fin r → E))` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hli`. Establish `hcard : Fintype.card ι ≤ Module.finrank ℚ (Fin r → E)` using `hliQ.fintype_card_le_finrank`.

Establish `hfr : Module.finrank ℚ (Fin r → E) = r * Module.finrank ℚ E`. Simplify using `[Module.finrank_pi_fintype]`. Establish `heven : Module.finrank ℚ E = 2 * fdeg E`. Rewrite using `[fdeg, IsTotallyComplex.finrank E]`. Use linear arithmetic over natural numbers and integers.

Establish `hn : Fintype.card ι ≤ 2 * fdeg E * r`. Rewrite `hcard` using `[hfr, heven]`. Combine the linear relations using `[Nat.mul_comm r (2 * fdeg E)]`. Establish `hMpos : (0 : ℤ) < M` using `by exact_mod_cast hM`. Set `f : (ι → Fin M) → (Fin r → E)` to `fun c => ((∑ i, ((c i : ℕ) : ℤ) • b i : L) : Fin r → E)`.

Use `⟨Finset.univ.image f, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `t ht`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `(∑ i, ((c i : ℕ) : ℤ) • b i : L).2`.

Introduce `x hx`. Set `xl : L` to `⟨x, hx⟩`. Set `k` to `b.repr xl`. Set `c : ι → Fin M` to `fun i => ⟨(k i % M).toNat, by`. Use `Int.emod_nonneg (k i) hMpos.ne'` as an intermediate fact.

Use `Int.emod_lt_of_pos (k i) hMpos` as an intermediate fact. Use the proof step `omega⟩`. Use `⟨f c, Finset.mem_image_of_mem _ (Finset.mem_univ _), ((∑ i, (k i / M) • b i : L) : Fin r → E), (∑ i, (k i / M) • b i : L).2, ?_⟩` and prove the remaining obligations. Establish `hsum : xl = ∑ i, ((c i : ℕ) : ℤ) • b i + (M : ℤ) • ∑ i, (k i / M) • b i` using `by conv_lhs => rw [← b.sum_repr xl]`. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← add_smul]`. Use `congr 1`. Use `show k i = ((k i % M).toNat : ℤ) + M * (k i / M)`. Rewrite using `[Int.toNat_of_nonneg (Int.emod_nonneg _ hMpos.ne')]`.

Combine the linear relations using `[Int.mul_ediv_add_emod (k i) (M : ℤ)]`. Establish `h2` using `congrArg Subtype.val hsum`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Submodule.coe_add, Submodule.coe_smul, natCast_zsmul]`.
-/
theorem lattice_mod_reps_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E),
    T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  intro E _ _ _ r M Λ hM hfg
  classical
  let L : Submodule ℤ (Fin r → E) := Λ.restrictScalars ℤ
  have hLfg : L.FG := hfg.restrictScalars
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hLfg
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let b := Module.Free.chooseBasis ℤ L
  have hli : LinearIndependent ℤ (fun i => (b i : Fin r → E)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliQ : LinearIndependent ℚ (fun i => (b i : Fin r → E)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hcard : Fintype.card ι ≤ Module.finrank ℚ (Fin r → E) := hliQ.fintype_card_le_finrank
  have hfr : Module.finrank ℚ (Fin r → E) = r * Module.finrank ℚ E := by
    simp [Module.finrank_pi_fintype]
  have heven : Module.finrank ℚ E = 2 * fdeg E := by
    rw [fdeg, IsTotallyComplex.finrank E]; omega
  have hn : Fintype.card ι ≤ 2 * fdeg E * r := by
    rw [hfr, heven] at hcard; linarith [Nat.mul_comm r (2 * fdeg E)]
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  let f : (ι → Fin M) → (Fin r → E) := fun c => ((∑ i, ((c i : ℕ) : ℤ) • b i : L) : Fin r → E)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (ι → Fin M)).card :=
          Finset.card_image_le
      _ = M ^ Fintype.card ι := by simp
      _ ≤ M ^ (2 * fdeg E * r) := Nat.pow_le_pow_right hM hn
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ht
    exact (∑ i, ((c i : ℕ) : ℤ) • b i : L).2
  · intro x hx
    let xl : L := ⟨x, hx⟩
    let k := b.repr xl
    let c : ι → Fin M := fun i => ⟨(k i % M).toNat, by
      have := Int.emod_nonneg (k i) hMpos.ne'
      have := Int.emod_lt_of_pos (k i) hMpos
      omega⟩
    refine ⟨f c, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ((∑ i, (k i / M) • b i : L) : Fin r → E), (∑ i, (k i / M) • b i : L).2, ?_⟩
    have hsum : xl = ∑ i, ((c i : ℕ) : ℤ) • b i + (M : ℤ) • ∑ i, (k i / M) • b i := by
      conv_lhs => rw [← b.sum_repr xl]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      show k i = ((k i % M).toNat : ℤ) + M * (k i / M)
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hMpos.ne')]
      linarith [Int.mul_ediv_add_emod (k i) (M : ℤ)]
    have h2 := congrArg Subtype.val hsum
    calc x = (xl : Fin r → E) := rfl
      _ = _ := h2
      _ = f c + M • ((∑ i, (k i / M) • b i : L) : Fin r → E) := by
        rw [Submodule.coe_add, Submodule.coe_smul, natCast_zsmul]

end GlobalTheory
