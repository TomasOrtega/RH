import Mathlib
open NumberField IsDedekindDomain Filter

noncomputable section

namespace GlobalTheory.BCT.SuppFin

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨c, hc⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hc.symm`.

Establish `: {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]`. Rewrite using `[this]`. Conclude with `Valued.isOpen_closedBall _ (by simp [hc0])`.
-/
theorem isOpen_vle (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

/- English proof (translation)
Establish `hcov : K ⊆ ⋃ N : ℤ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp N}`. Introduce `z _`. Rewrite using `[Set.mem_iUnion]`. Distinguish the cases in `hz : Valued.v z = 0`. Conclude with `⟨0, by simp [hz]⟩`.

Conclude with `⟨WithZero.log (Valued.v z), by simp [WithZero.exp_log hz]⟩`. Take `⟨N, hN⟩` from `hK.elim_directed_cover _ (fun N => isOpen_vle w N) hcov (Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 hab))`. Conclude with `⟨N, fun z hz => hN hz⟩`.
-/
theorem exists_bound_of_isCompact (w : HeightOneSpectrum (𝓞 E)) {K : Set (w.adicCompletion E)}
    (hK : IsCompact K) : ∃ N : ℤ, ∀ z ∈ K, Valued.v z ≤ WithZero.exp N := by
  have hcov : K ⊆ ⋃ N : ℤ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp N} := by
    intro z _
    rw [Set.mem_iUnion]
    by_cases hz : Valued.v z = 0
    · exact ⟨0, by simp [hz]⟩
    · exact ⟨WithZero.log (Valued.v z), by simp [WithZero.exp_log hz]⟩
  obtain ⟨N, hN⟩ := hK.elim_directed_cover _ (fun N => isOpen_vle w N) hcov
    (Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 hab))
  exact ⟨N, fun z hz => hN hz⟩

/- English proof (translation)
Introduce `E _ _ w n D hD`. Establish `h1 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v (h.val i j) ≤ WithZero.exp N`. Introduce `i j`. Take `⟨N, hN⟩` from `exists_bound_of_isCompact w (hD.image (Units.continuous_val.matrix_elem i j))`. Conclude with `⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩`.

Establish `h2 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N`. Introduce `i j`. Take `⟨N, hN⟩` from `exists_bound_of_isCompact w (hD.image ((Units.continuous_coe_inv).matrix_elem i j))`. Conclude with `⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩`. Use `choose N1 hN1 using h1`.

Use `choose N2 hN2 using h2`. Use `⟨((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) ⊔ ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ), ?_⟩` and prove the remaining obligations. Introduce `h hh i j`. Establish `a1 : N1 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ)` using `(Int.self_le_toNat _).trans (Int.ofNat_le.2 (Finset.le_sup (f := fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) (Finset.mem_univ (i, j))))`. Establish `a2 : N2 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ)` using `(Int.self_le_toNat _).trans (Int.ofNat_le.2 (Finset.le_sup (f := fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) (Finset.mem_univ (i, j))))`.

Conclude with `⟨(hN1 i j h hh).trans (WithZero.exp_le_exp.2 (a1.trans le_sup_left)), (hN2 i j h hh).trans (WithZero.exp_le_exp.2 (a2.trans le_sup_right))⟩`.
-/
theorem gl_entries_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))),
    IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j,
      Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
  intro E _ _ w n D hD
  have h1 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v (h.val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image (Units.continuous_val.matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  have h2 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image ((Units.continuous_coe_inv).matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  choose N1 hN1 using h1
  choose N2 hN2 using h2
  refine ⟨((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) ⊔
      ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ), ?_⟩
  intro h hh i j
  have a1 : N1 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  have a2 : N2 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  exact ⟨(hN1 i j h hh).trans (WithZero.exp_le_exp.2 (a1.trans le_sup_left)),
    (hN2 i j h hh).trans (WithZero.exp_le_exp.2 (a2.trans le_sup_right))⟩

end GlobalTheory.BCT.SuppFin
