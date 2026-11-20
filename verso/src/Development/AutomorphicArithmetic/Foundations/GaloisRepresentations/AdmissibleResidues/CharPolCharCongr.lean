import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

/- English proof (translation)
Take `⟨c, hc⟩` from `Multiset.card_eq_one.1 ((WD.card_eig z g).trans hz)`. Rewrite using `[WD.charPol_eq_prod, WD.charPol_eq_prod (y.lpChar z), GlobalTheory.RowTie.EigTwist.eig_lpChar x z g hz c hc, GlobalTheory.RowTie.EigTwist.eig_lpChar y z g hz c hc, WD.eig, WD.eig, e]`.
-/
theorem charPol_char_congr {x y z : WD h} (hz : z.lpDim = 1) (g : ↥(Weil h)) (e : x.charPol g = y.charPol g) :
    (x.lpChar z).charPol g = (y.lpChar z).charPol g := by
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((WD.card_eig z g).trans hz)
  rw [WD.charPol_eq_prod, WD.charPol_eq_prod (y.lpChar z), GlobalTheory.RowTie.EigTwist.eig_lpChar x z g hz c hc,
    GlobalTheory.RowTie.EigTwist.eig_lpChar y z g hz c hc, WD.eig, WD.eig, e]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g => charPol_char_congr hz g (k.pol g), fun m => by rw [k.n0 ((WD.monomial_char_iff _ _ hz).1 m)]⟩`.
-/
theorem AwV.char {x y z : WD h} (k : AwV x y) (hz : z.lpDim = 1) : AwV (x.lpChar z) (y.lpChar z) :=
  ⟨fun g => charPol_char_congr hz g (k.pol g), fun m => by rw [k.n0 ((WD.monomial_char_iff _ _ hz).1 m)]⟩

/- English proof (translation)
Take `⟨x, hx, k⟩` from `k`. Establish `e` using `hx.wdOf_eq hl`. Take `⟨t, ht, φ, hφ, N, b, hN, -⟩` from `hx`. Rewrite using `[← hN.charPol_wdOf hl ht ι g, e, k.pol]`.
-/
theorem WDN.charpoly (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (k : WDN ι r y) (g : ↥(Weil h)) :
    (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = y.charPol g := by
  obtain ⟨x, hx, k⟩ := k
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  rw [← hN.charPol_wdOf hl ht ι g, e, k.pol]

/- English proof (translation)
The claim follows from `k`.
-/
theorem wn' (k : WDN ι r y) : WDN ι r y := k
/- English proof (translation)
The claim follows from `.of_isWDOf k`.
-/
theorem woOf' (k : IsWDOf ι r y) : WDN ι r y := .of_isWDOf k
/- English proof (translation)
The claim follows from `k.of_conj hl P hP`.
-/
theorem woConj' (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : WDN ι r' y := k.of_conj hl P hP
/- English proof (translation)
Take `⟨x, hx, k⟩` from `k`. Take `⟨x', hx', k'⟩` from `k'`. Conclude with `⟨_, hA E Ω l ι n m r r' hc hc' w hl A h _ _ hx hx', k.sum k'⟩`.
-/
theorem woSum' (hA : Gu.SumAway) {m : ℕ} {r' : G E Ω →* GL (Fin m) (Qbar l)} (hc : Continuous r) (hc' : Continuous r')
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {y' : WD h} (k : WDN ι r y) (k' : WDN ι r' y') :
    WDN ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (y.lpSum y') := by
  obtain ⟨x, hx, k⟩ := k
  obtain ⟨x', hx', k'⟩ := k'
  exact ⟨_, hA E Ω l ι n m r r' hc hc' w hl A h _ _ hx hx', k.sum k'⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨_, e, (k.awV hl).char hz⟩`.
-/
theorem woChar' (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)} {z : WD h} (hz : z.lpDim = 1)
    (e : IsWDOf ι r' ((wdOf h hl ι r).lpChar z)) (k : WDN ι r y) : WDN ι r' (y.lpChar z) := ⟨_, e, (k.awV hl).char hz⟩
/- English proof (translation)
Take `⟨r, wt, HT, k⟩` from `H E Ω l ι a ha π χ hr hp`. Conclude with `⟨r, wt, HT, k, fun w hl A h rc hrc σ hσ => .of_aw hl k.cont (.of_aw (k.away w hl A h rc hrc σ hσ))⟩`.
-/
theorem galEx' (H : CuspU) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (hr : (CG.mk π).IsRegAlg) (hp : IsPolarized π χ) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalU π χ ι r wt HT ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι r (rc (algNorm σ)) := by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, k, fun w hl A h rc hrc σ hσ => .of_aw hl k.cont (.of_aw (k.away w hl A h rc hrc σ hσ))⟩

end UpperTheory.GalN.V
