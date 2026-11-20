import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AdmissibleOfPiDecomposition
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhi

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Conclude with `⟨c, fun g => hc (f g)⟩`.
-/
private theorem UpperTheory.Ru.crystallineComparison.isGr_comp {Γ Γ' L : Type} [Group Γ] [Group Γ'] [Field L] {d : ℕ}
    {ρ₀ ρ : Γ →* GL (Fin d) L} (f : Γ' →* Γ) (h : UpperTheory.Gal.Int.Geo.IsGr ρ₀ ρ) :
    UpperTheory.Gal.Int.Geo.IsGr (ρ₀.comp f) (ρ.comp f) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g => hc (f g)⟩

/- English proof (translation)
Introduce `hGeo E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hc hP w hw n ϑ R hcong hR`. Take `⟨ρ₀, hmat, hgr⟩` from `hP`. Take `⟨h0, hroot⟩` from `hR`. Introduce `P AI hT A hA O _ _ _ Bw hj`. Establish `hcr` using `hGeo E Ω l H θ hN dd ρ₀ hmat w hw n ϑ hcong P AI hT A hA O Bw hj`.

Establish `hcont : Continuous (ρ.comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) := hc.comp continuous_subtype_val`. Take `⟨LL, r', ϑ', hmod, hcrE, hag, hnil⟩` from `UpperTheory.Ru.crystallineComparison.joinQ l P AI hT E Ω _ O Bw _ _ n ϑ dd _ _ hcont (UpperTheory.Ru.crystallineComparison.isGr_comp _ hgr) hcr`. Use `UpperTheory.Ru.crystallineComparison.nilToPhi l P AI hT ι E Ω A w hA O Bw hj dd _ LL r' hmod hcrE _ hnil R (ι (ϑ 0)) ((map_ne_zero ι).2 h0) ?_` and prove the remaining obligations. Rewrite using `[← hroot, UpperTheory.Gal.crystallineComparison.heckePol_map, UpperTheory.Gal.crystallineComparison.heckePol_map]`. Unfold `UpperTheory.Gal.crystallineComparison.heckePol`.

Use `Finset.sum_congr rfl fun j hj' => ?_` and prove the remaining obligations. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj')`. Simplify using `only [RingHom.comp_apply]`. Use `hag j hjn` as an intermediate fact. Rewrite using `[show algebraMap ↥LL.1 (Formalism.ConjugateSelfDual.Qbar l) (ϑ' j) = ϑ j from this]`.
-/
theorem UpperTheory.Ru.crystallineComparison.phiStep_of :
    UpperTheory.Ru.crystallineComparison.GeoSide → UpperTheory.Gal.Int.Geo.PhiStep := by
  intro hGeo E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hc hP w hw n ϑ R hcong hR
  obtain ⟨ρ₀, hmat, hgr⟩ := hP
  obtain ⟨h0, hroot⟩ := hR
  intro P AI hT A hA O _ _ _ Bw hj
  have hcr := hGeo E Ω l H θ hN dd ρ₀ hmat w hw n ϑ hcong P AI hT A hA O Bw hj
  have hcont : Continuous (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    hc.comp continuous_subtype_val
  obtain ⟨LL, r', ϑ', hmod, hcrE, hag, hnil⟩ :=
    UpperTheory.Ru.crystallineComparison.joinQ l P AI hT E Ω _ O Bw _ _ n ϑ dd _ _ hcont
      (UpperTheory.Ru.crystallineComparison.isGr_comp _ hgr) hcr
  refine UpperTheory.Ru.crystallineComparison.nilToPhi l P AI hT ι E Ω A w hA O Bw hj dd _ LL r' hmod hcrE _ hnil R (ι (ϑ 0))
    ((map_ne_zero ι).2 h0) ?_
  rw [← hroot, UpperTheory.Gal.crystallineComparison.heckePol_map, UpperTheory.Gal.crystallineComparison.heckePol_map]
  unfold UpperTheory.Gal.crystallineComparison.heckePol
  refine Finset.sum_congr rfl fun j hj' => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj')
  simp only [RingHom.comp_apply]
  have := hag j hjn
  rw [show algebraMap ↥LL.1 (Formalism.ConjugateSelfDual.Qbar l) (ϑ' j) = ϑ j from this]
