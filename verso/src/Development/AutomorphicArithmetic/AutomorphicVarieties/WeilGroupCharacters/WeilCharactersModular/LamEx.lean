import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

/- English proof (translation)
Introduce `h l hl L Ω _ _ _ _ _ _ s V c n r`. Use `haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1`. Use `haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1`. Use `haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv`. Use `haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])`.

Use `haveI : CharP (ResidueField ℤ_[l]) l := charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom) (PadicInt.residueField (p := l)).symm.injective l`. Use `haveI : CharP (ResidueField c.O) l := charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l`. Take `⟨d₀, hd, hA⟩` from `h l L Ω s`. Set `d : V.frame.Vl → ℕ` to `d₀`. Take `⟨⟨Λ⟩, hΛ⟩` from `lam_ex_free l V.frame c.O n r d fun v => (hA v).some`.

Take `⟨e, -⟩` from `hΛ Λ`. Establish `hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L)` using `(finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd`. Establish `hc : Fintype.card (Σ v : V.frame.Vl, Fin n × Fin (d v)) = n * Module.finrank ℚ (Lp L)`. Rewrite using `[Fintype.card_sigma, ← hsum, Finset.mul_sum]`. Simplify using the standard rewrite rules.

Conclude with `⟨Λ, ⟨e.symm.trans (MvPowerSeries.renameEquiv c.O (Fintype.equivFinOfCardEq hc))⟩⟩`.
-/
theorem UpperTheory.V.W.lamEx :
    LocCFTAll → LamEx := by
  intro h l hl L Ω _ _ _ _ _ _ s V c n r
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, hd, hA⟩ := h l L Ω s
  let d : V.frame.Vl → ℕ := d₀
  obtain ⟨⟨Λ⟩, hΛ⟩ := lam_ex_free l V.frame c.O n r d fun v => (hA v).some
  obtain ⟨e, -⟩ := hΛ Λ
  have hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L) :=
    (finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd
  have hc : Fintype.card (Σ v : V.frame.Vl, Fin n × Fin (d v)) = n * Module.finrank ℚ (Lp L) := by
    rw [Fintype.card_sigma, ← hsum, Finset.mul_sum]
    simp
  exact ⟨Λ, ⟨e.symm.trans (MvPowerSeries.renameEquiv c.O (Fintype.equivFinOfCardEq hc))⟩⟩
