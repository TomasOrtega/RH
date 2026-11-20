import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

/- English proof (translation)
Introduce `h` and use `by have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h simp [bdParam, MvPowerSeries.coeff_X] at this`.
-/
theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

/- English proof (translation)
Establish `hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ)` using `(IsFractionRing.injective B (FractionRing B)).comp hψ`. Set `fK : FractionRing A →+* FractionRing B` to `IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg`. Establish `e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ`. Use extensionality with `x`. Rewrite using `[RingHom.comp_apply]`.

Conclude with `IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x`. Use `⟨fK, ?_⟩` and prove the remaining obligations. Establish `e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK = CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B))`. Rewrite using `[← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]`. Establish `e2` using `congrArg Spec.map e1`.

Rewrite `e2` using `[Spec.map_comp, Spec.map_comp]`. Conclude with `e2`.
-/
theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

/- English proof (translation)
Take `⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩` from `hN`. Establish `hE : FinalTheorems.EffCartier (J.comap a)` using `GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ`. Establish `hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a))`. Use `GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf`.

Rewrite using `[show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ, Ideal.map_span, Set.image_singleton]`. Take `⟨b, hb, -⟩` from `hB.2 _ a hE`. Establish `hK : (y ≫ j) ≫ ν = jK R ≫ b`. Use `(hB.2 _ _ hEK).unique ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hνπ, hji, hy]`.

Rewrite using `[Category.assoc, hb]`. Take `⟨c, ⟨hc1, -⟩, -⟩` from `GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK`. Conclude with `⟨c, hc1⟩`.
-/
theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT`. Take `⟨hm, hs, -⟩` from `hT`. Establish `hcF : CharZero (ChartRing k m e)` using `(C.b.charZero_iff C.b.injective).1 inferInstance`. Use `haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero`. Establish `hAdm` using `GlobalTheory.MumfordChart.admissibleBase_chartRing k m e`.

Establish `hBase : GlobalTheory.Mum.Base (ChartRing k m e)` using `⟨hAdm, hcF⟩`. Use `haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1`. Take `⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩` from `hU`. Take `⟨ξZ, hξZ, -⟩` from `hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm`. Use `haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X`.

Establish `hPF` using `hpf C.P.D.toPre.X C.rank`. Establish `hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n` using `fun i => hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by`. Simplify using `using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))`. Use `choose b hb using hnat`. Set `a : Fin m → ℕ` to `fun i => d * b (Fin.cast hm.symm i)`.

Establish `hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i)` using `(Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm`. Establish `hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i}`. Use `GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_` and prove the remaining obligations. Use `haveI := hW.1`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`.

Establish `hne : ∀ i, ψ (C.s i) ≠ 0` using `fun i h0 => by`. Establish `: C.s i = 0` using `hψi (h0.trans (map_zero ψ).symm)`. Rewrite `this` using `[hs i]`. Conclude with `bdParam_ne_zero k m e _ this`. Use `choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ`.

Take `⟨fK, hκ⟩` from `exists_fractionRing_map ψ hψi`. Take `⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩` from `GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ`. Take `⟨n, hn, hIn⟩` from `hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y) (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono`. Rewrite using `[← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]`. Use `Ideal.span_singleton_eq_span_singleton.2 ?_` and prove the remaining obligations.

Establish `hnw : n = ∑ i, w i * (d * b i)`. Establish `: (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i)`. Rewrite using `[hn, hφ, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hb i]; ring`. Conclude with `this` after adjusting the coercions.

Establish `: Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i))` using `Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow`. Rewrite using `[hnw]`. Use `(this.trans ?_).symm` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Simplify using `only [← pow_mul]`.

Conclude with `Associated.refl _`. Establish `hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)`. Take `⟨ξ, hξ⟩` from `exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI`. Conclude with `⟨ξ, hξ.symm⟩`.
-/
theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
