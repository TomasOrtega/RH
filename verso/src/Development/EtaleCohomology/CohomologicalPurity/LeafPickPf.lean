import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `v _`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul k m`.

Establish `: k ⊗ₜ[A] m = k • ((1 : K) ⊗ₜ[A] m)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)`. Consider the case `add a c ha hc => exact add_mem (ha trivial) (hc trivial)`.
-/
theorem pick_span_top (A M K : Type) [CommRing A] [AddCommGroup M] [Module A M] [Field K] [Algebra A K] :
    Submodule.span K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[A] m = k • ((1 : K) ⊗ₜ[A] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add a c ha hc => exact add_mem (ha trivial) (hc trivial)

/- English proof (translation)
Introduce `d A M _ _ _ _ p _ hd`. Use `set K := p.ResidueField`. Take `⟨b, hbs, hbspan, hbli⟩` from `exists_linearIndependent K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m)`. Rewrite `hbspan` using `[pick_span_top]`. Set `B : Module.Basis b K (K ⊗[A] M)` to `Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])`.

Set `_ : Fintype b` to `FiniteDimensional.fintypeBasisIndex B`. Establish `hcard : Fintype.card b = d` using `by rw [← hd, Module.finrank_eq_card_basis B]`. Set `B'` to `B.reindex (Fintype.equivFinOfCardEq hcard)`. Establish `hmem : ∀ i, ∃ m : M, (1 : K) ⊗ₜ[A] m = B' i`. Introduce `i`.

Establish `: B' i ∈ b` using `by simp [B', B]`. Take `⟨m, hm⟩` from `hbs this`. Conclude with `⟨m, hm⟩`. Use `choose x hx using hmem`. Use `set N := Submodule.span A (Set.range x)`.

Set `g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N)` to `(N.mkQ).baseChange K`. Establish `hgsurj : Function.Surjective g` using `LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N)`. Establish `hg0 : ∀ v, g v = 0`. Introduce `v`. Establish `hv : v ∈ Submodule.span K (Set.range B')` using `by rw [B'.span_eq]; trivial`.

Use `Submodule.span_induction ?_ ?_ ?_ ?_ hv` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← hx i]`. Simplify using `[g, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩)]`. Simplify using the standard rewrite rules.

Introduce `a c _ _ ha hc`. Simplify using `[ha, hc]`. Introduce `r a _ ha`. Simplify using `[ha]`. Establish `hsub : Subsingleton (K ⊗[A] (M ⧸ N))` using `by constructor; intro u w`.

Take `⟨u', rfl⟩` from `hgsurj u`. Take `⟨w', rfl⟩` from `hgsurj w`. Rewrite using `[hg0, hg0]`. Establish `hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ N)`. Rewrite using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct]`.

Introduce `h`. Conclude with `(not_nontrivial_iff_subsingleton.2 hsub) h`. Rewrite `hnot` using `[Module.mem_support_iff_of_finite]`. Take `⟨f, hf, hfp⟩` from `Set.not_subset.1 hnot`. Use `⟨x, f, hfp, fun m => ?_⟩` and prove the remaining obligations.

Rewrite `hf` using `[SetLike.mem_coe, Module.mem_annihilator]`. Use `hf (Submodule.Quotient.mk m)` as an intermediate fact. Rewrite `this` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis.
-/
theorem LeafPick_of : LeafPick := by
  intro d A M _ _ _ _ p _ hd
  set K := p.ResidueField
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m)
  rw [pick_span_top] at hbspan
  let B : Module.Basis b K (K ⊗[A] M) := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = d := by rw [← hd, Module.finrank_eq_card_basis B]
  let B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  have hmem : ∀ i, ∃ m : M, (1 : K) ⊗ₜ[A] m = B' i := by
    intro i
    have : B' i ∈ b := by simp [B', B]
    obtain ⟨m, hm⟩ := hbs this
    exact ⟨m, hm⟩
  choose x hx using hmem
  set N := Submodule.span A (Set.range x)
  let g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N) := (N.mkQ).baseChange K
  have hgsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N)
  have hg0 : ∀ v, g v = 0 := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range B') := by rw [B'.span_eq]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i, rfl⟩
      rw [← hx i]
      simp [g, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩)]
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro r a _ ha; simp [ha]
  have hsub : Subsingleton (K ⊗[A] (M ⧸ N)) := by
    constructor; intro u w
    obtain ⟨u', rfl⟩ := hgsurj u
    obtain ⟨w', rfl⟩ := hgsurj w
    rw [hg0, hg0]
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro h
    exact (not_nontrivial_iff_subsingleton.2 hsub) h
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.1 hnot
  refine ⟨x, f, hfp, fun m => ?_⟩
  rw [SetLike.mem_coe, Module.mem_annihilator] at hf
  have := hf (Submodule.Quotient.mk m)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end LateralTheory.CohomologicalPurity.ChartCut
