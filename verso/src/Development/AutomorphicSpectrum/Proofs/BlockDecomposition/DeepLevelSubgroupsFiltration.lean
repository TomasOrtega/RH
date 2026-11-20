import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.KmPow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem finite_quotient_unif_pow (m : ℕ) : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) := by
  have hmax : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {Zls.unif k} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 Zls.irreducible_unif
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k}) := by
    rw [← hmax]
    exact (inferInstance : Finite 𝓀[k])
  have := Ideal.finite_quotient_pow (I := Ideal.span {Zls.unif k}) ⟨{Zls.unif k}, by simp⟩ m
  rwa [Ideal.span_singleton_pow] at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem Km_anti (N : ℕ) {m m' : ℕ} (h : m ≤ m') : Zls.Km k N m' ≤ Zls.Km k N m := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have key : Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g =
      Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)
        (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g) := by
    ext i j
    simp
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [key, hg, map_one]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_pow_mem_Km (N m' : ℕ) {m : ℕ} {x : GL (Fin N) k} (hx : x ∈ Zls.Km k N m) :
    ∃ M : ℕ, 0 < M ∧ x ^ M ∈ Zls.Km k N m' := by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  haveI := finite_quotient_unif_pow (k := k) m'
  set f := Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'}))
    with hf
  refine ⟨orderOf (f g), orderOf_pos _, ?_⟩
  rw [← map_pow]
  refine Subgroup.mem_map.2 ⟨g ^ orderOf (f g), ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem KM_antitone_and_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n),
    Antitone (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd) ∧
    ∀ m m', m ≤ m' → ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd,
      ∃ N : ℕ, 0 < N ∧ u ^ N ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m' + 1)) (fun _ : Fin n => 1) hd := by
  intro k _ _ _ _ n hd
  refine ⟨fun m m' h u hu => Km_anti n (Nat.succ_le_succ h) hu, fun m m' _ u hu => ?_⟩
  obtain ⟨M, hM, hp⟩ := exists_pow_mem_Km n (m' + 1) (show _ ∈ Zls.Km k n (m + 1) from hu)
  refine ⟨M, hM, ?_⟩
  show _ ∈ Zls.Km k n (m' + 1)
  rwa [map_pow]

end GlobalTheory.CompanionTheory.KmPow
