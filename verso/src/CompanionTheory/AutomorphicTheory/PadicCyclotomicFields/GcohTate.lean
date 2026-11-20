import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTateB

open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

/- English proof (translation)
Take `⟨A, _, eA, hA⟩` from `hRep G (ZMod n) M rho hrho`. Establish `ht : Function.Bijective H.tTop` using `(H.t ⊤).bijective.comp (bijective_cohomologyRes_top D 2)`. Set `t : cohomology D 2 ≃+ ZMod n` to `AddEquiv.ofBijective H.tTop ht`. Establish `: Finite A` using `Finite.of_equiv _ eA.toEquiv`. Establish `: Finite D` using `Finite.of_equiv _ eD.toEquiv`.

Establish `hAn : ∀ a : A, n • a = 0` using `fun a => by`. Take `⟨m, rfl⟩` from `eA.surjective a`. Rewrite using `[← map_nsmul, nsmul_zmod, map_zero]`. Establish `hDn : ∀ a : D, n • a = 0` using `nsmul_eq_zero_of_nonempty_addEquiv ⟨eD.symm⟩`. Set `ι` to `MonoidHom.id G`.

Establish `hid : Function.Bijective (evalPair (R` using `ZMod n) (M := M)).flip := Function.bijective_id`. Establish `hev : Function.Bijective (evalPair (R` using `ZMod n) (M := M)).flip.flip := bij_flip _ (AddEquiv.refl _) hid`. Take `⟨eB, hB, hAB⟩` from `exists_dualEquiv (rho.comp ι) ((twDual χ rho).comp ι) ((charRep χ).comp ι) evalPair (fun g x y => evalPair_equiv χ rho (ι g) x y) A D eA hA eD hD hid`. Take `⟨eC, hC, hBC⟩` from `exists_dualEquiv ((twDual χ rho).comp ι) (rho.comp ι) ((charRep χ).comp ι) evalPair.flip (fun g y x => evalPair_equiv χ rho (ι g) x y) (dualRep D A) D eB hB eD hD hev`. Establish `: Finite (dualRep D A)` using `finite_dualRep`.

Establish `: IsDiscreteRep (dualRep D (dualRep D A))` using `isDiscreteRep_dualRep D (dualRep D A)`. Establish `h11 : Function.Bijective (cupH1H1TwistedDual χ rho ι (hrho.comp' continuous_id))` using `cup_product_H1_H1_bijective _ _ _ _ _ _ (dualRep D A) D eB hB eD hD eC hC hBC t h1 h2 _ (H.bijective_dualityMap_of_group (dualRep D A) (nsmul_dualRep_eq_zero hDn) _)`. Take `⟨eP, -⟩` from `h2 G (ZMod n) (ZMod n) (charRep χ) D eD hD`. Take `⟨eP', -⟩` from `h2 G (ZMod n) (ZMod n) ((charRep χ).comp ι) D eD hD`. Take `⟨e1, -⟩` from `h1 G (ZMod n) M (rho.comp ι) A eA hA`.

Use `hfin A hAn` as an intermediate fact. Establish `: Finite (H1 (rho.comp ι))` using `Finite.of_equiv _ e1.symm.toEquiv`. Use `⟨⟨LinearEquiv.ofBijective ((eP.trans t).toAddMonoidHom.toZModLinearMap n) (eP.trans t).bijective⟩, ?_, h11, bij_flip _ (eP'.trans t) h11, ?_⟩` and prove the remaining obligations. Conclude with `cup_product_H0_H2_bijective _ _ _ _ _ _ A D eA hA eD hD eB hB hAB t h0 h2 (H.bijective_dualityMap_of_group A hAn _)`. Conclude with `cup_product_H2_H0_bijective _ _ _ _ _ _ A D eA hA eD hD eB hB hAB t h0 h2 (H.bijective_dualityMap_of_group A hAn _)`.
-/
theorem tate_core (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) {n : ℕ} [NeZero n]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D]
    (H : DualityHypotheses n D)
    (hfin : ∀ (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [Finite A], (∀ a : A, n • a = 0) →
      Finite (cohomology A 1))
    (χ : G →* (ZMod n)ˣ) (eD : ZMod n ≃+ D.V)
    (hD : ∀ (g : G) (m : ZMod n), eD ((χ g : ZMod n) * m) = D.ρ g (eD m))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod n) G M) (hrho : ContAction rho) :
    Nonempty (H2 (charRep χ) ≃ₗ[ZMod n] ZMod n) ∧
    Function.Bijective (cupH0H2TwistedDual χ rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 χ rho (MonoidHom.id _)) := by
  obtain ⟨A, _, eA, hA⟩ := hRep G (ZMod n) M rho hrho
  have ht : Function.Bijective H.tTop :=
    (H.t ⊤).bijective.comp (bijective_cohomologyRes_top D 2)
  let t : cohomology D 2 ≃+ ZMod n := AddEquiv.ofBijective H.tTop ht
  have : Finite A := Finite.of_equiv _ eA.toEquiv
  have : Finite D := Finite.of_equiv _ eD.toEquiv
  have hAn : ∀ a : A, n • a = 0 := fun a => by
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, nsmul_zmod, map_zero]
  have hDn : ∀ a : D, n • a = 0 := nsmul_eq_zero_of_nonempty_addEquiv ⟨eD.symm⟩
  let ι := MonoidHom.id G
  have hid : Function.Bijective (evalPair (R := ZMod n) (M := M)).flip :=
    Function.bijective_id
  have hev : Function.Bijective (evalPair (R := ZMod n) (M := M)).flip.flip :=
    bij_flip _ (AddEquiv.refl _) hid
  obtain ⟨eB, hB, hAB⟩ := exists_dualEquiv (rho.comp ι) ((twDual χ rho).comp ι)
    ((charRep χ).comp ι) evalPair (fun g x y => evalPair_equiv χ rho (ι g) x y) A D eA hA eD hD hid
  obtain ⟨eC, hC, hBC⟩ := exists_dualEquiv ((twDual χ rho).comp ι) (rho.comp ι)
    ((charRep χ).comp ι) evalPair.flip (fun g y x => evalPair_equiv χ rho (ι g) x y)
    (dualRep D A) D eB hB eD hD hev
  have : Finite (dualRep D A) := finite_dualRep
  have : IsDiscreteRep (dualRep D (dualRep D A)) := isDiscreteRep_dualRep D (dualRep D A)
  have h11 : Function.Bijective (cupH1H1TwistedDual χ rho ι (hrho.comp' continuous_id)) :=
    cup_product_H1_H1_bijective _ _ _ _ _ _ (dualRep D A) D eB hB eD hD eC hC hBC t h1 h2 _
      (H.bijective_dualityMap_of_group (dualRep D A) (nsmul_dualRep_eq_zero hDn) _)
  obtain ⟨eP, -⟩ := h2 G (ZMod n) (ZMod n) (charRep χ) D eD hD
  obtain ⟨eP', -⟩ := h2 G (ZMod n) (ZMod n) ((charRep χ).comp ι) D eD hD
  obtain ⟨e1, -⟩ := h1 G (ZMod n) M (rho.comp ι) A eA hA
  have := hfin A hAn
  have : Finite (H1 (rho.comp ι)) := Finite.of_equiv _ e1.symm.toEquiv
  refine ⟨⟨LinearEquiv.ofBijective ((eP.trans t).toAddMonoidHom.toZModLinearMap n)
    (eP.trans t).bijective⟩, ?_, h11, bij_flip _ (eP'.trans t) h11, ?_⟩
  · exact cup_product_H0_H2_bijective _ _ _ _ _ _ A D eA hA eD hD eB hB hAB t h0 h2
      (H.bijective_dualityMap_of_group A hAn _)
  · exact cup_product_H2_H0_bijective _ _ _ _ _ _ A D eA hA eD hD eB hB hAB t h0 h2
      (H.bijective_dualityMap_of_group A hAn _)

/- English proof (translation)
Introduce `l _ K hK r M _ _ _ _ _ rho hr hrho`. Take `⟨hsep, _, _, hloc, -⟩` from `hF l K hK`. Establish `hl : (l ^ r : ℕ) ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`. Establish `: NeZero (l ^ r)` using `⟨hl⟩`. Establish `: CharZero K` using `algebraRat.charZero K`.

Establish `hn : ((l ^ r : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 hl`. Take `⟨eD, hD⟩` from `hMu l K r`. Conclude with `tate_core hRep h0 h1 h2 (galRootsOfUnity.{0} K (PadicAlgCl l) (l ^ r)) (localDualityHypotheses hn) (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl l) hn A hA 1) (cycK l K r) eD hD M rho hrho`.
-/
theorem tate_of (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) (hF : SgcField) (hMu : SgcMu) :
    Formalism.GaloisCohomology.LocalTateDualityK := by
  intro l _ K hK r M _ _ _ _ _ rho hr hrho
  obtain ⟨hsep, _, _, hloc, -⟩ := hF l K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨eD, hD⟩ := hMu l K r
  exact tate_core hRep h0 h1 h2 (galRootsOfUnity.{0} K (PadicAlgCl l) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl l) hn A hA 1)
    (cycK l K r) eD hD M rho hrho

end CompanionTheory.LocalTateOrthogonality.Gcoh
