import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneOpen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.out.one_lt`. Establish `hl2` using `hl.out.two_le`. Establish `hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1`. Use `push_cast`. Rewrite using `[PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]`.

Conclude with `max_eq_left (inv_le_one_of_one_le₀ hl1.le)`. Rewrite using `[norm_one, PadicInt.norm_p]`. Conclude with `(inv_lt_one_of_one_lt₀ hl1).ne'`. Take `⟨u, hu⟩` from `PadicInt.isUnit_iff.2 hnorm`. Use `⟨u, fun h => ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[← Units.isOfFinOrder_val, hu, isOfFinOrder_iff_pow_eq_one]`. Take `⟨n, hn, h⟩` from `h`. Rewrite `h` using `[← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_unit (l : ℕ) [hl : Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl2 := hl.out.two_le
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left (inv_le_one_of_one_le₀ hl1.le)
    · rw [norm_one, PadicInt.norm_p]
      exact (inv_lt_one_of_one_lt₀ hl1).ne'
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.2 hnorm
  refine ⟨u, fun h => ?_⟩
  rw [← Units.isOfFinOrder_val, hu, isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, hn, h⟩ := h
  rw [← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h
  omega

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ U hU A hlt`. Take `⟨hP1, hP2, hP3, -⟩` from `places k Ω l A`. Establish `hA : A ≠ ⊤` using `fun h => (hP2 h).2 hlt`. Take `⟨v, hv⟩` from `hP1 hA`. Establish `hvl : v ∈ Above k l` using `(hP3 v hv).1 hlt`.

Take `⟨-, hidx, -⟩` from `LDataCardLeFinrank.ineOpen k Ω l v A hvl hv`. Take `⟨u, hu⟩` from `exists_unit l`. Establish `hmem : u ^ (LDataCardLeFinrank.ineImage k l A).index ∈ LDataCardLeFinrank.ineImage k l A` using `Subgroup.pow_index_mem _ u`. Take `⟨g, hg, hgu⟩` from `Subgroup.mem_map.1 hmem`. Use `haveI : Finite (G k Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU`.

Use `haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Use `haveI := Subgroup.finiteIndex_normalCore U`. Use `haveI := Subgroup.normalCore_normal U`. Establish `hN : U.normalCore.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`. Establish `hgU : g ^ U.normalCore.index ∈ U` using `U.normalCore_le (Subgroup.pow_index_mem _ g)`.

Use `⟨g ^ U.normalCore.index, ⟨hgU, Subgroup.pow_mem (Dec (F := k) A) hg.1 _⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hgu, ← pow_mul, isOfFinOrder_pow]`. Introduce and unpack `(h | h)`. Conclude with `hu h`. Conclude with `mul_ne_zero hidx hN h`.
-/
theorem UpperTheory.V.Base.decInf :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsOpen (U : Set (G k Ω)) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ g ∈ U ⊓ Dec (F := k) A, ¬ IsOfFinOrder (cycZ k Ω l g) := by
  intro k Ω _ _ _ _ _ l _ U hU A hlt
  obtain ⟨hP1, hP2, hP3, -⟩ := places k Ω l A
  have hA : A ≠ ⊤ := fun h => (hP2 h).2 hlt
  obtain ⟨v, hv⟩ := hP1 hA
  have hvl : v ∈ Above k l := (hP3 v hv).1 hlt
  obtain ⟨-, hidx, -⟩ := LDataCardLeFinrank.ineOpen k Ω l v A hvl hv
  obtain ⟨u, hu⟩ := exists_unit l
  have hmem : u ^ (LDataCardLeFinrank.ineImage k l A).index ∈ LDataCardLeFinrank.ineImage k l A := Subgroup.pow_index_mem _ u
  obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.1 hmem
  haveI : Finite (G k Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_normalCore U
  haveI := Subgroup.normalCore_normal U
  have hN : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hgU : g ^ U.normalCore.index ∈ U := U.normalCore_le (Subgroup.pow_index_mem _ g)
  refine ⟨g ^ U.normalCore.index, ⟨hgU, Subgroup.pow_mem (Dec (F := k) A) hg.1 _⟩, ?_⟩
  rw [map_pow, hgu, ← pow_mul, isOfFinOrder_pow]
  rintro (h | h)
  · exact hu h
  · exact mul_ne_zero hidx hN h
