import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Frobenius
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCardStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ a ha r M _ _ _ hne`. Take `⟨e⟩` from `hne`. Use `haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Take `⟨hMfin, -, -⟩` from `UpperTheory.V.X.So.levFacts l O a ha M ⟨e⟩`. Establish `hsm : ∀ x y : O, x • e.symm (Ideal.Quotient.mk (Ideal.span {a}) y) = e.symm (Ideal.Quotient.mk _ (x * y))`.

Introduce `x y`. Rewrite using `[← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]`. Establish `hmk0 : ∀ y : O, e.symm (Ideal.Quotient.mk (Ideal.span {a}) y) = 0 ↔ a ∣ y`. Introduce `y`. Rewrite using `[LinearEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.

Establish `hsurj : ∀ m : M, ∃ y : O, e.symm (Ideal.Quotient.mk (Ideal.span {a}) y) = m`. Introduce `m`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (e m)`. Conclude with `⟨y, by rw [hy, LinearEquiv.symm_apply_apply]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨φ₀, hφ₀⟩ : ∃ φ₀ : M →ₗ[ZMod (l ^ r)] ZMod (l ^ r), ∀ x : O, ¬ a ∣ x → ∃ m : M, φ₀ (x • m) ≠ 0 := by`.

Distinguish the cases in `hu : IsUnit a`. Conclude with `⟨0, fun x hx => absurd hu.dvd hx⟩`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨s, hs⟩` from `IsDiscreteValuationRing.associated_pow_irreducible ha hϖ`. Establish `hs0 : s ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hu (associated_one_iff_isUnit.mp (by simpa using hs))`. Establish `hpd : ∀ t u : ℕ, ϖ ^ t ∣ ϖ ^ u ↔ t ≤ u` using `fun t u => pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit`. Establish `hz : e.symm (Ideal.Quotient.mk (Ideal.span {a}) (ϖ ^ (s - 1))) ≠ 0`. Rewrite using `[Ne, hmk0, hs.dvd_iff_dvd_left, hpd]`.

Use linear arithmetic over natural numbers and integers. Take `⟨f, -, hf⟩` from `KStar.Selmer.exists_form_ne_zero (⊥ : Submodule (ZMod (l ^ r)) M) (z := e.symm (Ideal.Quotient.mk (Ideal.span {a}) (ϖ ^ (s - 1)))) (by rw [Submodule.mem_bot]; exact hz)`. Use `⟨f, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx (dvd_zero a)`. Take `⟨t, ht⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ`. Establish `hts : t < s`. Assume the negation of the conclusion as `h`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[hs.dvd_iff_dvd_left, ht.dvd_iff_dvd_right]`. Conclude with `(hpd s t).mpr (by omega)`. Take `⟨w, hw⟩` from `ht`. Use `⟨e.symm (Ideal.Quotient.mk _ (↑w * ϖ ^ (s - 1 - t))), ?_⟩` and prove the remaining obligations. Rewrite using `[hsm]`.

Establish `hprod : x * (↑w * ϖ ^ (s - 1 - t)) = ϖ ^ (s - 1)`. Rewrite using `[← mul_assoc, hw, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hprod]`.

Conclude with `hf`. Establish `hann : ∀ x : O, a ∣ x → ∀ m : M, x • m = 0`. Introduce `x hx m`. Take `⟨y, rfl⟩` from `hsurj m`. Rewrite using `[hsm, hmk0]`.

Conclude with `hx.mul_right y`. Establish `hcond : ∀ x : O, (∀ m, φ₀ (x • m) = 0) ↔ a ∣ x`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hx`. Take `⟨m, hm⟩` from `hφ₀ x hx`. Conclude with `hm (h m)`. Introduce `hx m`. Rewrite using `[hann x hx m, map_zero]`.

Use `⟨φ₀, hcond, fun φ => ?_⟩` and prove the remaining obligations. Set `sm : O → (M →ₗ[ZMod (l ^ r)] M)` to `fun x => (DistribMulAction.toAddMonoidHom M x).toZModLinearMap (l ^ r)`. Set `Ψ : O →+ Module.Dual (ZMod (l ^ r)) M` to `{ toFun := fun x => φ₀ ∘ₗ sm x map_zero' := by`. Use extensionality with `m`. Simplify using `[sm]`.

Use the proof step `map_add' := by`. Introduce `x y`. Use extensionality with `m`. Simplify using `[sm, add_smul] }`. Establish `hΨ : ∀ x m, Ψ x m = φ₀ (x • m)` using `fun x m => rfl`.

Establish `hker : Ψ.ker = (Ideal.span {a}).toAddSubgroup`. Use extensionality with `x`. Simplify using `only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Rewrite using `[← hcond]`. Prove the components needed by the constructor for the conclusion.

Introduce `h m`. Rewrite using `[← hΨ, h]`. Both sides reduce to the same expression. Introduce `h`. Use extensionality with `m`.

Conclude with `h m`. Establish `hcardR : Nat.card Ψ.range = Nat.card M`. Rewrite using `[← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Ψ).toEquiv, Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hker).toEquiv]`. Conclude with `Nat.card_congr e.symm.toEquiv`. Establish `hcardD` using `GlobalTheory.T.card_dual_zmod_module_eq_card (l ^ r) M`.

Use `haveI : Finite (Module.Dual (ZMod (l ^ r)) M) := Nat.finite_of_card_ne_zero (by rw [hcardD]; exact Nat.card_pos.ne')`. Establish `htop : Ψ.range = ⊤` using `AddSubgroup.eq_top_of_card_eq _ (by rw [hcardR, hcardD])`. Take `⟨x, hx⟩ : φ ∈ Ψ.range` from `htop ▸ AddSubgroup.mem_top φ`. Conclude with `⟨x, fun m => by rw [← hx]; rfl⟩`.
-/
theorem UpperTheory.V.X.So.dualGen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module O M] [Module (ZMod (l ^ r)) M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → ∃ φ₀ : M →ₗ[ZMod (l ^ r)] ZMod (l ^ r), (∀ x : O, (∀ m, φ₀ (x • m) = 0) ↔ a ∣ x) ∧ ∀ φ : M →ₗ[ZMod (l ^ r)] ZMod (l ^ r), ∃ x : O, ∀ m, φ m = φ₀ (x • m) := by
  intro l _ O _ _ _ _ _ a ha r M _ _ _ hne
  obtain ⟨e⟩ := hne
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hMfin, -, -⟩ := UpperTheory.V.X.So.levFacts l O a ha M ⟨e⟩
  have hsm : ∀ x y : O,
      x • e.symm (Ideal.Quotient.mk (Ideal.span {a}) y) = e.symm (Ideal.Quotient.mk _ (x * y)) := by
    intro x y
    rw [← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
  have hmk0 : ∀ y : O, e.symm (Ideal.Quotient.mk (Ideal.span {a}) y) = 0 ↔ a ∣ y := by
    intro y
    rw [LinearEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hsurj : ∀ m : M, ∃ y : O, e.symm (Ideal.Quotient.mk (Ideal.span {a}) y) = m := by
    intro m
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e m)
    exact ⟨y, by rw [hy, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : M →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
      ∀ x : O, ¬ a ∣ x → ∃ m : M, φ₀ (x • m) ≠ 0 := by
    by_cases hu : IsUnit a
    · exact ⟨0, fun x hx => absurd hu.dvd hx⟩
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
      obtain ⟨s, hs⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hu (associated_one_iff_isUnit.mp (by simpa using hs))
      have hpd : ∀ t u : ℕ, ϖ ^ t ∣ ϖ ^ u ↔ t ≤ u :=
        fun t u => pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
      have hz : e.symm (Ideal.Quotient.mk (Ideal.span {a}) (ϖ ^ (s - 1))) ≠ 0 := by
        rw [Ne, hmk0, hs.dvd_iff_dvd_left, hpd]
        omega
      obtain ⟨f, -, hf⟩ := KStar.Selmer.exists_form_ne_zero (⊥ : Submodule (ZMod (l ^ r)) M)
        (z := e.symm (Ideal.Quotient.mk (Ideal.span {a}) (ϖ ^ (s - 1))))
        (by rw [Submodule.mem_bot]; exact hz)
      refine ⟨f, fun x hx => ?_⟩
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx (dvd_zero a)
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
      have hts : t < s := by
        by_contra h
        apply hx
        rw [hs.dvd_iff_dvd_left, ht.dvd_iff_dvd_right]
        exact (hpd s t).mpr (by omega)
      obtain ⟨w, hw⟩ := ht
      refine ⟨e.symm (Ideal.Quotient.mk _ (↑w * ϖ ^ (s - 1 - t))), ?_⟩
      rw [hsm]
      have hprod : x * (↑w * ϖ ^ (s - 1 - t)) = ϖ ^ (s - 1) := by
        rw [← mul_assoc, hw, ← pow_add]
        congr 1
        omega
      rw [hprod]
      exact hf
  have hann : ∀ x : O, a ∣ x → ∀ m : M, x • m = 0 := by
    intro x hx m
    obtain ⟨y, rfl⟩ := hsurj m
    rw [hsm, hmk0]
    exact hx.mul_right y
  have hcond : ∀ x : O, (∀ m, φ₀ (x • m) = 0) ↔ a ∣ x := by
    intro x
    constructor
    · intro h
      by_contra hx
      obtain ⟨m, hm⟩ := hφ₀ x hx
      exact hm (h m)
    · intro hx m
      rw [hann x hx m, map_zero]
  refine ⟨φ₀, hcond, fun φ => ?_⟩
  let sm : O → (M →ₗ[ZMod (l ^ r)] M) :=
    fun x => (DistribMulAction.toAddMonoidHom M x).toZModLinearMap (l ^ r)
  let Ψ : O →+ Module.Dual (ZMod (l ^ r)) M :=
    { toFun := fun x => φ₀ ∘ₗ sm x
      map_zero' := by
        ext m
        simp [sm]
      map_add' := by
        intro x y
        ext m
        simp [sm, add_smul] }
  have hΨ : ∀ x m, Ψ x m = φ₀ (x • m) := fun x m => rfl
  have hker : Ψ.ker = (Ideal.span {a}).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    rw [← hcond]
    constructor
    · intro h m
      rw [← hΨ, h]
      rfl
    · intro h
      ext m
      exact h m
  have hcardR : Nat.card Ψ.range = Nat.card M := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Ψ).toEquiv,
      Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hker).toEquiv]
    exact Nat.card_congr e.symm.toEquiv
  have hcardD := GlobalTheory.T.card_dual_zmod_module_eq_card (l ^ r) M
  haveI : Finite (Module.Dual (ZMod (l ^ r)) M) :=
    Nat.finite_of_card_ne_zero (by rw [hcardD]; exact Nat.card_pos.ne')
  have htop : Ψ.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [hcardR, hcardD])
  obtain ⟨x, hx⟩ : φ ∈ Ψ.range := htop ▸ AddSubgroup.mem_top φ
  exact ⟨x, fun m => by rw [← hx]; rfl⟩
