import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhood
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanonBd

/- English proof (translation)
Establish `key : ∀ f : MvPowerSeries σ A, MvPowerSeries.X i ∣ f ↔ (1 : ℕ∞) ≤ f.weightedOrder (Pi.single i 1)` using `fun f => by`. Establish `hw : ∀ d : σ →₀ ℕ, Finsupp.weight (Pi.single i 1 : σ → ℕ) d = d i` using `fun d => by`. Rewrite using `[Finsupp.weight_single_one_apply]`. Rewrite using `[MvPowerSeries.X_dvd_iff]`. Use `⟨fun h => ?_, fun h d hd => ?_⟩` and prove the remaining obligations.

Conclude with `MvPowerSeries.nat_le_weightedOrder _ (n := 1) fun d hd => h d (by rw [hw] at hd; omega)`. Conclude with `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (lt_of_lt_of_le (by rw [hw, hd]; simp) h)`. Use `⟨fun h => ?_, fun h => ?_, fun f g h => ?_⟩` and prove the remaining obligations. Simplify `congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h` using `[MvPowerSeries.coeff_X]`. Simplify using `using h.map MvPowerSeries.constantCoeff`.

Rewrite `h` using `[key, MvPowerSeries.weightedOrder_mul]`. Rewrite using `[key, key]`. Assume the negation of the conclusion as `hn`. Simplify using `only [not_or, not_le, Order.lt_one_iff] at hn`. Simplify using `[hn.1, hn.2] at h`.
-/
theorem prime_X {σ A : Type} [CommRing A] [IsDomain A] (i : σ) : Prime (MvPowerSeries.X i : MvPowerSeries σ A) := by
  classical
  have key : ∀ f : MvPowerSeries σ A, MvPowerSeries.X i ∣ f ↔ (1 : ℕ∞) ≤ f.weightedOrder (Pi.single i 1) := fun f => by
    have hw : ∀ d : σ →₀ ℕ, Finsupp.weight (Pi.single i 1 : σ → ℕ) d = d i := fun d => by
      rw [Finsupp.weight_single_one_apply]
    rw [MvPowerSeries.X_dvd_iff]
    refine ⟨fun h => ?_, fun h d hd => ?_⟩
    · exact MvPowerSeries.nat_le_weightedOrder _ (n := 1) fun d hd => h d (by rw [hw] at hd; omega)
    · exact MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (lt_of_lt_of_le (by rw [hw, hd]; simp) h)
  refine ⟨fun h => ?_, fun h => ?_, fun f g h => ?_⟩
  · simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  · simpa using h.map MvPowerSeries.constantCoeff
  · rw [key, MvPowerSeries.weightedOrder_mul] at h
    rw [key, key]
    by_contra hn
    simp only [not_or, not_le, Order.lt_one_iff] at hn
    simp [hn.1, hn.2] at h

/- English proof (translation)
Introduce `x hx`. Take `⟨n, hn⟩` from `Ideal.mem_radical_iff.1 hx`. Rewrite `hn`, the goal using `[Ideal.mem_span_singleton]`. Use `GlobalTheory.RelParamRad.prod_dvd_of_forall_dvd m _ (fun i => prime_X (v i)) (fun i j hij => ?_) x fun i => (prime_X (v i)).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hn)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Use `MvPowerSeries.X_dvd_iff.1 hij (Finsupp.single (v j) 1) (Finsupp.single_eq_of_ne fun h => hne (hv h))` as an intermediate fact. Simplify using `[MvPowerSeries.coeff_X] at this`.
-/
theorem isRadical_span_prod_X {σ A : Type} [CommRing A] [IsDomain A] {m : ℕ} (v : Fin m → σ) (hv : Function.Injective v) :
    (Ideal.span {∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ A)}).IsRadical := by
  classical
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  refine GlobalTheory.RelParamRad.prod_dvd_of_forall_dvd m _ (fun i => prime_X (v i)) (fun i j hij => ?_) x
    fun i => (prime_X (v i)).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hn)
  by_contra hne
  have := MvPowerSeries.X_dvd_iff.1 hij (Finsupp.single (v j) 1)
    (Finsupp.single_eq_of_ne fun h => hne (hv h))
  simp [MvPowerSeries.coeff_X] at this

/- English proof (translation)
Use `haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p`. Set `lo` to `algebraMap R (Localization.AtPrime p.asIdeal)`. Establish `e : (spMap lo ≫ ξ) (closedPoint (Localization.AtPrime p.asIdeal)) = ξ p`. Express the relevant statement in the definitionally equal form `ξ (spMap lo (closedPoint _)) = ξ p`. Use `congr 1`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `Localization.AtPrime.under_maximalIdeal`. Rewrite using `[← e]`. Use `(mem_support_iff_stalkId I _).2 fun htop => ?_` and prove the remaining obligations. Establish `h₁ : idlAlong I (spMap lo ≫ ξ) = ⊤` using `by rw [idlAlong, htop, Ideal.map_top]`.

Rewrite `h₁` using `[GlobalTheory.TraitOrder.idlAlong_comp]`. Establish `h₂ : (idlAlong I ξ).map lo ≤ maximalIdeal _` using `(Ideal.map_mono h).trans (Localization.AtPrime.map_eq_maximalIdeal).le`. Conclude with `(maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h₁ ▸ h₂))`.
-/
theorem mem_support_of_idlAlong_le {S : Scheme.{0}} (I : S.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (p : Sp R) (h : idlAlong I ξ ≤ p.asIdeal) : ξ p ∈ I.support := by
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let lo := algebraMap R (Localization.AtPrime p.asIdeal)
  have e : (spMap lo ≫ ξ) (closedPoint (Localization.AtPrime p.asIdeal)) = ξ p := by
    change ξ (spMap lo (closedPoint _)) = ξ p
    congr 1
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  rw [← e]
  refine (mem_support_iff_stalkId I _).2 fun htop => ?_
  have h₁ : idlAlong I (spMap lo ≫ ξ) = ⊤ := by rw [idlAlong, htop, Ideal.map_top]
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at h₁
  have h₂ : (idlAlong I ξ).map lo ≤ maximalIdeal _ :=
    (Ideal.map_mono h).trans (Localization.AtPrime.map_eq_maximalIdeal).le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h₁ ▸ h₂))

/- English proof (translation)
Establish `hf : f ≠ 0` using `fun h => hp (h ▸ p.asIdeal.zero_mem)`. Establish `hle : Submonoid.powers f ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hf`. Use `haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle`. Establish `hu : ∀ x : Submonoid.powers f, IsUnit (algebraMap R (FractionRing R) x)` using `fun x => IsLocalization.map_units (FractionRing R) (⟨x.1, hle x.2⟩ : nonZeroDivisors R)`. Set `lf : Localization.Away f →+* FractionRing R` to `IsLocalization.lift hu`.

Set `lo` to `spMap (algebraMap R (Localization.Away f))`. Set `κ : Sp (FractionRing R) ⟶ Sp (Localization.Away f)` to `spMap lf`. Establish `hκ : κ ≫ lo = jK R`. Rewrite using `[← Spec.map_comp]`. Conclude with `congrArg spMap (IsLocalization.lift_comp hu)`.

Establish `hinj : Function.Injective lf`. Use `(IsLocalization.lift_injective_iff hu).2 fun x x' => ?_` and prove the remaining obligations. Rewrite using `[(IsLocalization.injective (Localization.Away f) hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]`. Use `haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot lf).1 hinj]`.

Conclude with `bot_le)⟩`. Establish `hξ : lo ≫ ξ = yo ≫ j`. Use `ext_of_isDominant κ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hκ, ← hy, ← Category.assoc, hyo κ hκ]`. Establish `hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))`.

Rewrite using `[PrimeSpectrum.localization_away_comap_range _ f]`. Conclude with `hp`. Take `⟨q, hq⟩` from `hq`. Use `⟨yo q, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(yo ≫ j) q = ξ p`.

Rewrite using `[← hξ, ← hq]`. Both sides reduce to the same expression.
-/
theorem mem_range_of_away {X S : Scheme.{0}} [S.IsSeparated] (j : X ⟶ S) {R : Type} [CommRing R] [IsDomain R]
    (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ) (f : R) (yo : Sp (Localization.Away f) ⟶ X)
    (hyo : ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away f),
      g ≫ spMap (algebraMap R (Localization.Away f)) = jK R → g ≫ yo = y)
    (p : Sp R) (hp : f ∉ p.asIdeal) : ξ p ∈ Set.range j := by
  have hf : f ≠ 0 := fun h => hp (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hu : ∀ x : Submonoid.powers f, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R) (⟨x.1, hle x.2⟩ : nonZeroDivisors R)
  let lf : Localization.Away f →+* FractionRing R := IsLocalization.lift hu
  let lo := spMap (algebraMap R (Localization.Away f))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.Away f) := spMap lf
  have hκ : κ ≫ lo = jK R := by
    rw [← Spec.map_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.Away f) hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hξ : lo ≫ ξ = yo ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hyo κ hκ]
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ f]
    exact hp
  obtain ⟨q, hq⟩ := hq
  refine ⟨yo q, ?_⟩
  change (yo ≫ j) q = ξ p
  rw [← hξ, ← hq]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ hpq hφ hns Z zs i OZ N d J S π j _ BD hP hS k _ m e C hT ξ hy`. Establish `hEt` using `GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy`. Take `⟨-, -, -, ⟨hd, hJ, -⟩, ⟨-, hproj, -, -, -, hπ, hBD, hval⟩, -⟩` from `hP`. Take `⟨hm, hs, ⟨yo, -, -, -, hyo⟩, -⟩` from `hT.1`. Use `haveI : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance`.

Use `haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))`. Establish `hA` using `GlobalTheory.MumfordChart.admissibleBase_chartRing k m e`. Use `haveI : IsProper (π ≫ zs) := by`. Take `⟨n, lo, hlo, h⟩` from `hproj`. Use `isProper_str c.F n` as an intermediate fact.

Rewrite using `[← h]`. Use `infer_instance`. Use `haveI : S.IsSeparated := by`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← terminal.comp_from (π ≫ zs)]`.

Use `infer_instance`. Use `haveI := GlobalTheory.PointStepCompare.projective_of_free E (X := C.P.D.toPre.X)`. Establish `hF` using `hφ C.P.D.toPre.X C.rank`. Establish `hM : 0 < l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos`. Establish `hex : ∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)` using `fun i => by`.

Take `⟨n, hn⟩` from `hF.exists_nat (C.cone.mem i) (C.cone.nonneg i)`. Establish `h0` using `hF.pos _ (C.cone.mem i) (C.cone.nonneg i) (C.cone.linearIndependent.ne_zero i)`. Rewrite `h0` using `[hn]`. Use `⟨d * (l.M' * n), by have : 0 < n := by exact_mod_cast h0 positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[C.cone.evalZ_smul, hn]`.

Use `push_cast`. Both sides reduce to the same expression. Use `choose a ha0 ha using hex`. Establish `hprod : ∀ b : Fin C.m → ℕ, ∏ i, C.s i ^ b i = ∏ i, bdParam k m e i ^ b (Fin.cast hm.symm i)` using `fun b => Fintype.prod_equiv (finCongr hm) _ _ fun i => by rw [hs]; rfl`. Establish `hs0 : ∀ i, C.s i ≠ 0` using `fun i => by rw [hs]; exact (prime_X _).ne_zero`.

Establish `hdiv : idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i}`. Rewrite using `[hprod]`. Use `GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR k m e _ _ fun W _ _ _ hW ψ hψ hψl => ?_` and prove the remaining obligations. Rewrite using `[← hprod, ← GlobalTheory.TraitOrder.idlAlong_comp]`. Use `haveI : IsDiscreteValuationRing W := hW.1`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Use `choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible ((map_ne_zero_iff ψ hψ).2 (hs0 i)) hϖ`. Establish `hκ : spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ jK _ = jK W ≫ spMap ψ` using `(GlobalTheory.ArcPull.fracMap_sq hψ).symm.trans (Category.id_comp _)`. Take `⟨t, tK, P, h₁, h₂, be, hbe, hmon, hev⟩` from `GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ ⟨hA, inferInstance⟩ C W hW ψ hψ hψl ϖ hϖ w hw _ hκ`. Take `⟨n, hn, hI⟩` from `hval W hW ϖ hϖ (spMap ψ ≫ ξ) _ (by rw [Category.assoc, hy, reassoc_of% hκ]) t tK h₁ h₂ P be hbe hmon`.

Establish `hn' : n = ∑ i, w i * a i`. Apply `Nat.cast_injective (R := ℝ)` to reduce the goal to its premises. Rewrite using `[hn, hev, Finset.mul_sum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [ha]; ring`.

Rewrite using `[hI, hn', Ideal.span_singleton_eq_span_singleton, map_prod, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Associated.prod _ _ _ fun i _ => by rw [map_pow, pow_mul]; exact (hw i).symm.pow_pow`. Establish `hset : ∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal` using `fun p => by`. Use `⟨fun h hp => ?_, mem_range_of_away j ξ C.y hy _ yo hyo p⟩` and prove the remaining obligations. Establish `h₁ : ξ p ∈ BD.idealSheaf.support`.

Use `mem_support_of_idlAlong_le _ ξ p ?_` and prove the remaining obligations. Rewrite using `[hdiv, Ideal.span_singleton_le_iff_mem]`. Conclude with `Ideal.mem_of_dvd _ (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => dvd_pow_self _ (ha0 i).ne') hp`. Rewrite `h₁` using `[hBD, Scheme.IdealSheafData.support_comap]`. Rewrite `h` using `[← hπ]`.

Conclude with `hJ _ h₁ h`. Use `⟨hset, ?_, a, ha, hdiv⟩` and prove the remaining obligations. Use `haveI := GlobalTheory.GenFan.essFiniteType_int_stalk c.F S (π ≫ zs) (ξ (closedPoint _))`. Use `haveI := hA.1`. Use `GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl S j.opensRange _ ξ _ ?_ (fun p => ?_) (GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ _ hA.2.2.2 hEt (GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ hEt))` and prove the remaining obligations.

Simplify using `only [hs]`. Conclude with `isRadical_span_prod_X (fun i => Sum.inl (Fin.cast hm i)) (Sum.inl_injective.comp (Fin.cast_injective hm))`. Rewrite using `[Scheme.Hom.coe_opensRange]`. Conclude with `hset p`.
-/
theorem boundary_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧ ∃ a : Fin C.m → ℕ, (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns Z zs i OZ N d J S π j _ BD hP hS k _ m e C hT ξ hy
  have hEt := GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨-, -, -, ⟨hd, hJ, -⟩, ⟨-, hproj, -, -, -, hπ, hBD, hval⟩, -⟩ := hP
  obtain ⟨hm, hs, ⟨yo, -, -, -, hyo⟩, -⟩ := hT.1
  haveI : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsProper (π ≫ zs) := by
    obtain ⟨n, lo, hlo, h⟩ := hproj
    have := isProper_str c.F n
    rw [← h]
    infer_instance
  haveI : S.IsSeparated := by
    constructor
    rw [← terminal.comp_from (π ≫ zs)]
    infer_instance

  haveI := GlobalTheory.PointStepCompare.projective_of_free E (X := C.P.D.toPre.X)
  have hF := hφ C.P.D.toPre.X C.rank
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hex : ∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i) := fun i => by
    obtain ⟨n, hn⟩ := hF.exists_nat (C.cone.mem i) (C.cone.nonneg i)
    have h0 := hF.pos _ (C.cone.mem i) (C.cone.nonneg i) (C.cone.linearIndependent.ne_zero i)
    rw [hn] at h0
    refine ⟨d * (l.M' * n), by have : 0 < n := by exact_mod_cast h0
                               positivity, ?_⟩
    rw [C.cone.evalZ_smul, hn]
    push_cast
    rfl
  choose a ha0 ha using hex
  have hprod : ∀ b : Fin C.m → ℕ, ∏ i, C.s i ^ b i = ∏ i, bdParam k m e i ^ b (Fin.cast hm.symm i) := fun b =>
    Fintype.prod_equiv (finCongr hm) _ _ fun i => by rw [hs]; rfl
  have hs0 : ∀ i, C.s i ≠ 0 := fun i => by rw [hs]; exact (prime_X _).ne_zero

  have hdiv : idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
    rw [hprod]
    refine GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR k m e _ _ fun W _ _ _ hW ψ hψ hψl => ?_
    rw [← hprod, ← GlobalTheory.TraitOrder.idlAlong_comp]
    haveI : IsDiscreteValuationRing W := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible
      ((map_ne_zero_iff ψ hψ).2 (hs0 i)) hϖ
    have hκ : spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ jK _ = jK W ≫ spMap ψ :=
      (GlobalTheory.ArcPull.fracMap_sq hψ).symm.trans (Category.id_comp _)
    obtain ⟨t, tK, P, h₁, h₂, be, hbe, hmon, hev⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ ⟨hA, inferInstance⟩ C W hW ψ hψ hψl ϖ hϖ w hw _ hκ
    obtain ⟨n, hn, hI⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξ) _ (by rw [Category.assoc, hy, reassoc_of% hκ]) t tK h₁ h₂ P be hbe hmon
    have hn' : n = ∑ i, w i * a i := by
      apply Nat.cast_injective (R := ℝ)
      rw [hn, hev, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; ring
    rw [hI, hn', Ideal.span_singleton_eq_span_singleton, map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => by rw [map_pow, pow_mul]; exact (hw i).symm.pow_pow

  have hset : ∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal := fun p => by
    refine ⟨fun h hp => ?_, mem_range_of_away j ξ C.y hy _ yo hyo p⟩
    have h₁ : ξ p ∈ BD.idealSheaf.support := by
      refine mem_support_of_idlAlong_le _ ξ p ?_
      rw [hdiv, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_of_dvd _ (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => dvd_pow_self _ (ha0 i).ne') hp
    rw [hBD, Scheme.IdealSheafData.support_comap] at h₁
    rw [← hπ] at h
    exact hJ _ h₁ h
  refine ⟨hset, ?_, a, ha, hdiv⟩
  haveI := GlobalTheory.GenFan.essFiniteType_int_stalk c.F S (π ≫ zs) (ξ (closedPoint _))
  haveI := hA.1
  refine GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl S j.opensRange _ ξ _ ?_ (fun p => ?_)
    (GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ _ hA.2.2.2 hEt
      (GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ hEt))
  · simp only [hs]
    exact isRadical_span_prod_X (fun i => Sum.inl (Fin.cast hm i)) (Sum.inl_injective.comp (Fin.cast_injective hm))
  · rw [Scheme.Hom.coe_opensRange]
    exact hset p

end GlobalTheory.UCanonBd
