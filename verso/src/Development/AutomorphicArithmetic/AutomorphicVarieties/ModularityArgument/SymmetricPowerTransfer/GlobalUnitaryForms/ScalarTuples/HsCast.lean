import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Unfold `Loc.hs`. Distinguish the cases in `hx : x ∈ GlobalTheory.HilbertRecip.nrm p d`. Take `⟨a, b, e⟩` from `h.1 hx`. Rewrite using `[if_pos ⟨a, b, e.symm⟩, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hx]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg fun ⟨a, b, e⟩ => hx (h.2 ⟨a, b, e.symm⟩), GlobalTheory.HilbertRecip.hs_eq_neg_one_iff.2 hx]`. Simplify using the standard rewrite rules.
-/
private theorem hs_cast {F A : Type} [Field F] [NumberField F] [Field A] (φ : F →+* A) (p : GlobalTheory.HilbertRecip.Place F) (x d : Fˣ)
    (h : x ∈ GlobalTheory.HilbertRecip.nrm p d ↔ ∃ a b : A, φ x = a ^ 2 - φ d * b ^ 2) :
    Loc.hs (φ d) (φ x) = (((GlobalTheory.HilbertRecip.hs p x d : ℤˣ) : ℤ) : ℂ) := by
  unfold Loc.hs
  by_cases hx : x ∈ GlobalTheory.HilbertRecip.nrm p d
  · obtain ⟨a, b, e⟩ := h.1 hx
    rw [if_pos ⟨a, b, e.symm⟩, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hx]
    simp
  · rw [if_neg fun ⟨a, b, e⟩ => hx (h.2 ⟨a, b, e.symm⟩), GlobalTheory.HilbertRecip.hs_eq_neg_one_iff.2 hx]
    simp

/- English proof (translation)
Introduce `F _ _ d x hd hx`. Use `lift d to Fˣ using hd.isUnit`. Use `lift x to Fˣ using hx.isUnit`. Establish `h1 : ∀ v : Pl F, Loc.hs (cv v d) (cv v x) = (((GlobalTheory.HilbertRecip.hs (.inl v) x d : ℤˣ) : ℤ) : ℂ)` using `fun v => hs_cast (cv v) (.inl v) x d Iff.rfl`. Establish `h2 : ∀ σ : F →+* ℝ, Loc.hs (σ d) (σ x) = (((GlobalTheory.HilbertRecip.hs (.inr σ) x d : ℤˣ) : ℤ) : ℂ)` using `fun σ => hs_cast σ (.inr σ) x d Iff.rfl`.

Establish `hfin : {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d}.Finite` using `(GlobalTheory.HilbertRecip.finite_not_mem_nrm x d).preimage (f := Sum.inl) Sum.inl_injective.injOn`. Establish `hsub : {v : Pl F | Loc.hs (cv v d) (cv v x) ≠ 1} ⊆ {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d}`. Introduce `v hv hm`. Use `hv ?_` and prove the remaining obligations. Rewrite using `[h1, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hm]`.

Simplify using the standard rewrite rules. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.HilbertRecip.prod_hs x d (hfin.toFinset.disjSum Finset.univ) (by`. Introduce and unpack `(v | σ) hv`. Rewrite using `[Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]`.

Conclude with `hv`. Use the proof step `simp)`. Rewrite `h` using `[Finset.prod_disjSum, mul_eq_one_iff_eq_inv, Int.units_inv_eq_self]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset]; exact hsub)]`. Simplify using `only [h1, h2]`.

Establish `h'` using `congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) h`. Simplify `h'` using `only [Units.coe_prod, Int.cast_prod]`.
-/
theorem UpperTheory.V.Z.Sym.Glob.recip :
    UpperTheory.V.Z.Sym.Glob.Recip := by
  intro F _ _ d x hd hx
  classical
  lift d to Fˣ using hd.isUnit
  lift x to Fˣ using hx.isUnit
  have h1 : ∀ v : Pl F, Loc.hs (cv v d) (cv v x) = (((GlobalTheory.HilbertRecip.hs (.inl v) x d : ℤˣ) : ℤ) : ℂ) :=
    fun v => hs_cast (cv v) (.inl v) x d Iff.rfl
  have h2 : ∀ σ : F →+* ℝ, Loc.hs (σ d) (σ x) = (((GlobalTheory.HilbertRecip.hs (.inr σ) x d : ℤˣ) : ℤ) : ℂ) :=
    fun σ => hs_cast σ (.inr σ) x d Iff.rfl
  have hfin : {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d}.Finite :=
    (GlobalTheory.HilbertRecip.finite_not_mem_nrm x d).preimage (f := Sum.inl) Sum.inl_injective.injOn
  have hsub : {v : Pl F | Loc.hs (cv v d) (cv v x) ≠ 1} ⊆ {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d} := by
    intro v hv hm
    refine hv ?_
    rw [h1, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hm]
    simp
  refine ⟨hfin.subset hsub, ?_⟩
  have h := GlobalTheory.HilbertRecip.prod_hs x d (hfin.toFinset.disjSum Finset.univ) (by
    rintro (v | σ) hv
    · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      exact hv
    · simp)
  rw [Finset.prod_disjSum, mul_eq_one_iff_eq_inv, Int.units_inv_eq_self] at h
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset]; exact hsub)]
  simp only [h1, h2]
  have h' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) h
  simpa only [Units.coe_prod, Int.cast_prod] using h'
