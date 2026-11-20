import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Introduce `l _ L _ _ _ J`. Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ L`. Establish `hl : ‖(l : PadicAlgCl l)‖ < 1`. Rewrite using `[← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p l]`. Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Simplify using `only [one_div, NNReal.coe_inv, NNReal.coe_natCast]`. Conclude with `inv_lt_one_of_one_lt₀ h1`. Set `I : Ideal (𝓞 L)` to `{ carrier := {x : 𝓞 L | ‖J (x : L)‖ < 1} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Use `show ‖J ((a : L) + (b : L))‖ < 1`. Rewrite using `[map_add]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`.

Introduce `c x hx`. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Use `show ‖J ((c : L) * (x : L))‖ < 1`. Rewrite using `[map_mul, norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (LocStab.norm_int_le J c)) hx }`.

Establish `hmem : ∀ x : 𝓞 L, x ∈ I ↔ ‖J (x : L)‖ < 1` using `fun x => Iff.rfl`. Establish `hIp : I.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, hmem]`. Simplify using the standard rewrite rules.

Introduce `a b hab`. Rewrite `hab` using `[hmem]`. Rewrite using `[hmem, hmem]`. Establish `hab' : ‖J (a : L)‖ * ‖J (b : L)‖ < 1`. Rewrite using `[← norm_mul, ← map_mul]`.

Conclude with `hab`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use polynomial arithmetic with `[h.1, h.2]`. Establish `hlI : ((l : ℤ) : 𝓞 L) ∈ I`.

Rewrite using `[hmem]`. Simplify using `using hl`. Establish `hIne : I ≠ ⊥`. Introduce `h`. Rewrite `hlI` using `[h, Ideal.mem_bot]`.

Establish `hne : ((l : ℤ) : 𝓞 L) ≠ 0`. Simplify using `[(Fact.out : l.Prime).ne_zero]`. Conclude with `hne hlI`. Set `v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)` to `⟨I, hIp, hIne⟩`. Establish `hlo : I.LiesOver (Ideal.span {(l : ℤ)})`.

Prove the components needed by the constructor for the conclusion. Establish `hmax : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).irreducible`. Use `hmax.eq_of_le (Ideal.comap_ne_top _ hIp.ne_top) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `show algebraMap ℤ (𝓞 L) (l : ℤ) ∈ I`.

Rewrite using `[eq_intCast]`. Conclude with `hlI`. Use `⟨I, hIp, hlo, hmem, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`. Rewrite using `[MulAction.mem_stabilizer_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hτ`. Establish `hr` using `LocStab.root_of_stab J α τ v hmem hτ`. Establish `hint` using `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) (J α)).isIntegral`. Establish `hmin : minpoly ℚ_[l] (J (τ α)) = minpoly ℚ_[l] (J α)` using `(minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr (minpoly.monic hint)).symm`.

Take `⟨σ, hσ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[l]) (E := PadicAlgCl l)).mp hmin`. Use `⟨σ, fun x => ?_⟩` and prove the remaining obligations. Establish `hext` using `LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J) (J.comp (τ : L →+* L)) (by simpa [AlgEquiv.smul_def] using hσ)`. Conclude with `RingHom.congr_fun hext x`. Introduce and unpack `⟨σ, hσ⟩`.

Apply `LocStab.stab_of_root J hα τ v hmem` to reduce the goal to its premises. Rewrite using `[← hσ α]`. Simplify using `[Polynomial.aeval_algEquiv]`. Introduce `σ`. Take `⟨s, hs⟩` from `LocStab.exists_aut_of_root J α (r := σ (J α)) (by simp [Polynomial.aeval_algEquiv])`.

Use `⟨s, fun x => ?_⟩` and prove the remaining obligations. Establish `hext` using `LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J) (J.comp (s : L →+* L)) (by simpa using hs.symm)`. Conclude with `RingHom.congr_fun hext x`. Conclude with `LocStab.finrank_adjoin_range_eq_card_stabilizer l L J v hmem`.
-/
theorem UpperTheory.HF.loc_onto :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (J : L →+* PadicAlgCl l), ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver (span {(l : ℤ)}) ∧ (∀ x : 𝓞 L, x ∈ P ↔ ‖J (x : L)‖ < 1) ∧ (∀ τ : L ≃ₐ[ℚ] L, τ ∈ MulAction.stabilizer _ P ↔ ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : L, σ (J x) = J (τ x)) ∧ (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ τ : L ≃ₐ[ℚ] L, ∀ x : L, σ (J x) = J (τ x)) ∧ Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range J)) = Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L) P) := by
  intro l _ L _ _ _ J
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hl : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p l]
    have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  let I : Ideal (𝓞 L) :=
    { carrier := {x : 𝓞 L | ‖J (x : L)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        show ‖J ((a : L) + (b : L))‖ < 1
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        show ‖J ((c : L) * (x : L))‖ < 1
        rw [map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (LocStab.norm_int_le J c)) hx }
  have hmem : ∀ x : 𝓞 L, x ∈ I ↔ ‖J (x : L)‖ < 1 := fun x => Iff.rfl
  have hIp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem] at hab
      rw [hmem, hmem]
      have hab' : ‖J (a : L)‖ * ‖J (b : L)‖ < 1 := by
        rw [← norm_mul, ← map_mul]
        exact hab
      by_contra h
      push_neg at h
      nlinarith [h.1, h.2]
  have hlI : ((l : ℤ) : 𝓞 L) ∈ I := by
    rw [hmem]
    simpa using hl
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlI
    have hne : ((l : ℤ) : 𝓞 L) ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact hne hlI
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨I, hIp, hIne⟩
  have hlo : I.LiesOver (Ideal.span {(l : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hIp.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 L) (l : ℤ) ∈ I
    rw [eq_intCast]
    exact hlI
  refine ⟨I, hIp, hlo, hmem, ?_, ?_, ?_⟩
  · intro τ
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hτ
      have hr := LocStab.root_of_stab J α τ v hmem hτ
      have hint := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) (J α)).isIntegral
      have hmin : minpoly ℚ_[l] (J (τ α)) = minpoly ℚ_[l] (J α) :=
        (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr (minpoly.monic hint)).symm
      obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[l]) (E := PadicAlgCl l)).mp hmin
      refine ⟨σ, fun x => ?_⟩
      have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
        (J.comp (τ : L →+* L)) (by simpa [AlgEquiv.smul_def] using hσ)
      exact RingHom.congr_fun hext x
    · rintro ⟨σ, hσ⟩
      apply LocStab.stab_of_root J hα τ v hmem
      rw [← hσ α]
      simp [Polynomial.aeval_algEquiv]
  · intro σ
    obtain ⟨s, hs⟩ := LocStab.exists_aut_of_root J α (r := σ (J α)) (by simp [Polynomial.aeval_algEquiv])
    refine ⟨s, fun x => ?_⟩
    have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
      (J.comp (s : L →+* L)) (by simpa using hs.symm)
    exact RingHom.congr_fun hext x
  · exact LocStab.finrank_adjoin_range_eq_card_stabilizer l L J v hmem
