import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntFormDescentBelow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsRayFieldOfRayIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompatStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
  Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
  GlobalTheory.SeriesTie.UnivRat
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntSteps

variable {D : D7}

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem castDict_smul {V W : HSp D} (e : V = W) (z : ℂ) (ψ : GA D V → ℂ) : castDict e (z • ψ) = z • castDict e ψ := by
  subst e
  rfl

/- English proof (translation)
Establish `h` using `GlobalTheory.Cmp.SeriesRay.sum_mem_intForms C a n S (fun _ : Fin (Fintype.card ι) => 1) (fun _ _ _ => by simp) (fun k => φ ((Fintype.equivFin ι).symm k)) fun k => hφ _`. Simplify using `only [map_one, one_smul] at h`. Rewrite `h` using `[Equiv.sum_comp (Fintype.equivFin ι).symm φ]`. Then use the resulting hypothesis.
-/
theorem sum_mem_intForms' {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {ι : Type} [Fintype ι] (φ : ι → GA D (T.V j σ) → ℂ)
    (hφ : ∀ k, φ k ∈ C.intForms a n S) : (∑ k, φ k) ∈ C.intForms a n S := by
  have h := GlobalTheory.Cmp.SeriesRay.sum_mem_intForms C a n S (fun _ : Fin (Fintype.card ι) => 1) (fun _ _ _ => by simp)
    (fun k => φ ((Fintype.equivFin ι).symm k)) fun k => hφ _
  simp only [map_one, one_smul] at h
  rwa [Equiv.sum_comp (Fintype.equivFin ι).symm φ] at h

/- English proof (translation)
Substitute `hV` using the available equality. Use `⟨_, sum_mem_intForms' C _ _ _ _ fun a' => intForms_fibre hRF hT hU hray hu hQ a' _ _ _ (hφ (a - a')), fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∑ a', _ : GA D _ → ℂ) g = φ _ g`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single (Multiplicative.toAdd (detChar _ (u.delQ Q) g)) (fun a' _ ha' => by rw [if_neg (Ne.symm ha'), zero_mul]) (fun h0 => absurd (Finset.mem_univ _) h0), if_pos rfl, one_mul]`.
-/
theorem exists_sum_fibres {T : CoreJ D} {j : Fin D.R.m} {C : Cover T ((j : ℕ) + 1) T.σ₀} {W : HSp D}
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = W) (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (hU : C.IsUnif)
    (hray : RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange) {A : Type} [AddCommGroup A] [Fintype A] {u : UnivTwist D A}
    {Q : Finset (Pl D.host.E)} (hu : u.Good Q) (hQ : ∀ PP ∈ Q, ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (a : ↥Q → A) (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)))
    (φ : (↥Q → A) → GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ) (hφ : ∀ a', φ a' ∈ C.intForms w n S) :
    ∃ Φ ∈ C.intForms w n S, ∀ g, castDict hV Φ g =
      castDict hV (φ (a - Multiplicative.toAdd (detChar W (u.delQ Q) g))) g := by
  classical
  subst hV
  refine ⟨_, sum_mem_intForms' C _ _ _ _ fun a' => intForms_fibre hRF hT hU hray hu hQ a' _ _ _ (hφ (a - a')), fun g => ?_⟩
  change (∑ a', _ : GA D _ → ℂ) g = φ _ g
  rw [Finset.sum_apply, Finset.sum_eq_single (Multiplicative.toAdd (detChar _ (u.delQ Q) g))
    (fun a' _ ha' => by rw [if_neg (Ne.symm ha'), zero_mul]) (fun h0 => absurd (Finset.mem_univ _) h0), if_pos rfl, one_mul]

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A} (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good)
  (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

include YS hρ in

/- English proof (translation)
Establish `hT` using `hti.laws`. Establish `hB` using `hρ.base i j b`. Establish `hl : (D.ntw.l i).Prime` using `(D.ntw.lPrime i).out`. Take `⟨c₀, hc₀, gramR, c0R, c0L, hft, u, hu, hsc⟩` from `exists_isScale Rl cG v₀ hρ hpin hcore.lev hcore.fam.tie hcore.models.cV hcore.thP hio i j b (hti.hv₀ j _)`. Take `⟨cC, hcC⟩` from `GlobalTheory.ExtCoeff.exists_ext_map D.what₂.embLL (VV D.what₂.LL (lamV D j)) (VV ℂ (lamV D j)) (c0L j)`.

Establish `hCM : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap Rl.toRealDat j cC` using `⟨gramR, c0R, c0L, hft, fun v => ⟨⟨MvPolynomial.map D.what₂.embLL v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ v.2⟩, rfl, hcC v _ rfl⟩⟩`. Take `⟨ph, hph, hS⟩` from `(hSI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hT hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti j hstd hV hfr).1 u hu cC hCM`. Establish `hph0 : ph ≠ 0` using `fun e => by simp [e] at hph`. Set `Λ : Subring ℂ` to `(ρ.eO i b).range`. Set `eΛ : D.ntw.O i ≃+* Λ` to `RingEquiv.ofBijective (ρ.eO i b).rangeRestrict ⟨fun x y e => ρ.eO_injective i b (congrArg Subtype.val e), (ρ.eO i b).rangeRestrict_surjective⟩`.

Use `haveI : IsDiscreteValuationRing Λ := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eΛ`. Establish `hlu : ¬ IsUnit ((D.ntw.l i : ℕ) : Λ)` using `fun e => by`. Use `e.map eΛ.symm` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `D.ntw.O_l i this`.

Establish `hΛ : ∀ z ∈ (ρ.e i b).fieldRange, z ∈ Λ ∨ z⁻¹ ∈ Λ`. Introduce and unpack `_ ⟨y, rfl⟩`. Break down `ValuationRing.isInteger_or_isInteger (D.ntw.O i) y with ⟨o, ho⟩ | ⟨o, ho⟩` into its components or cases. Conclude with `Or.inl ⟨o, congrArg (ρ.e i b) ho⟩`. Conclude with `Or.inr ⟨o, (congrArg (ρ.e i b) ho).trans (map_inv₀ _ _)⟩`.

Take `⟨e, he⟩` from `GlobalTheory.TowerPlace.placeIn_unique Λ _ hl hlu`. Take `⟨c₁, hc₁⟩` from `intForm_descent_below _ e hl`. Use `⟨ph * c₀, mul_ne_zero hph0 hc₀, fun P' hP' F' hF => ?_⟩` and prove the remaining obligations. Establish `hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank` using `fun τ => by`. Establish `h1` using `hB.sig τ`.

Establish `h2` using `Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)`. Rewrite `h2` using `[← h1]`. Conclude with `h2.le`. Establish `hinj` using `GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (ρ.B i j b).F.BS hB.wt hm`. Establish `hlam : (ρ.B i j b).w.lam = lamV D j` using `GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 Rl.toLevCh A3.A.μ0 j _ hcore.lev hB (hpin.mu0 i j b) (hpin.ap i j b) (hpin.am i j b)`.

Take `⟨v, hvc, hv⟩` from `exists_vec_of_small j hlam F'`. Establish `hio' : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j v) = c₀ • P'`. Take `⟨u', w₀, hu', -, hw⟩` from `IsChosenExtremalVector.io _ (hti.hv₀ j _) hio`. Take `rfl : u' = u` from `funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)`. Conclude with `IsScaleAt.ioP_eq (Rl := Rl) (c0 := c0L j) hsc hinj hP' (ioP_mem_harmonic hcore.lev hcore.thP (hcore.models.cV j) hB (hpin.psi i j b) (hpin.inf i j b) (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b) _ w₀ hw _ …`.

Set `v' : VsV D j ℂ` to `⟨MvPolynomial.map D.what₂.embLL v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ v.2⟩`. Establish `hv' : cC v' = c0L j v` using `hcC v _ rfl`. Take `⟨c₂, hc₂⟩` from `hS _ hl h hh (Submodule.span ℤ {v'}) (Submodule.fg_span_singleton _)`. Use `⟨c₁ + c₂, fun Q M hQ a => ?_⟩` and prove the remaining obligations. Establish `hsub : half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) ⊆ Q` using `fun P hP => admissibleConjugatePairPlaces_subset i Q M (mem_half.1 hP).1`.

Establish `hgood` using `GlobalTheory.UnivGood.univOf_good D D.nd D.ntw ρ hρ D.nexp i Q M`. Establish `hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))` using `GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D D.nd D.ntw ρ hρ i j b _ (fun P hP => hQ.1 P (admissibleConjugatePairPlaces_subset i Q M hP)) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))`. Take `⟨C, hG, hcl, hL0, hLe, hpd, hQpd, hchi, hres⟩` from `exists_cover_coprime YS hρ i j b hRF hT hti.alg hgal hval hray hde hU (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (fun P hP => hQ.2.1 P (hsub hP)) (hQ.2.2.mono_left hsub) (κ j).n`. Establish `hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z` using `fun z => congrArg (fun f => f z) hG.1.2.2.1`. Take `⟨la, -, hla, hl1, hl2⟩` from `he _ C.σ₂ fun x => hΛ _ (hLe ⟨x, rfl⟩)`.

Take `⟨p, -, hp, -, -⟩` from `he _ T.σ₀ fun x => hΛ _ (hLe ⟨C.inc x, hσ₂ x⟩)`. Establish `hpla` using `comap_eq_of_le_one_iff C.inc p la fun x => by rw [← hla, ← hp, hσ₂]`. Use `⟨p, fun x => by rw [GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff, ← hp]; rfl, ?_⟩` and prove the remaining obligations. Establish `hM : C.d.l₂.M = T.Q.l.M * C.d.pd` using `hG.1.1.2.1`. Establish `hMg : T.Q.l.M = D.host.g 0 * D.host.g 1` using `hT.toLawsM.pins.2.1.1`.

Establish `hPg : ∀ PP ∈ (ρ.B i j b).G.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `hρ.Pg i j b`. Establish `hN : ∀ PP, PP ∈ (ρ.B i j b).G.Pg ∨ PP ∈ (ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) → ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Introduce and unpack `PP (hP | hP)`. Take `⟨k, hk⟩` from `hPg PP hP`. Use `GlobalTheory.HalfCompare.mem_of_dvd hk (Dvd.dvd.mul_right ?_ _)` and prove the remaining obligations.

Rewrite using `[hMg]`. Use `fin_cases k`. Use `exacts [dvd_mul_right _ _, dvd_mul_left _ _]`. Break down `Finset.mem_union.1 hP with hP | hP` into its components or cases. Rewrite `hP` using `[hρ.delta]`.

Conclude with `GlobalTheory.HalfCompare.mem_of_dvd ((mem_pD_iff i PP).1 (mem_half.1 hP).1) (hpd.mul_left _)`. Conclude with `GlobalTheory.HalfCompare.mem_of_dvd (hQpd PP hP) (dvd_mul_left _ _)`. Establish `hcop : Nat.Coprime (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK) (T.Q.l.M * C.d.pd)`. Use `Nat.Coprime.mul_right ?_ hG.2.2.1.2.2.2.2.symm` and prove the remaining obligations. Rewrite using `[hMg]`.

Conclude with `Nat.Coprime.mul_right (GlobalTheory.CoverHalf.g_coprime D 0).symm (GlobalTheory.CoverHalf.g_coprime D 1).symm`. Establish `hδ` using `isDelta_delAt Rl.C (D.ntw.l i)`. Establish `htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi` using `⟨hpin.delta i j b, hδ.fin, hδ.triv, hδ.tame, fun w hw => hδ.unr w fun h0 => hw (GlobalTheory.HalfCompare.mem_of_dvd h0 hpd), fun w hw => by`. Take `⟨y, hy⟩` from `valuesIn_delAt hval _ w hw`. Take `⟨z, hz⟩` from `hL0 ⟨y, rfl⟩`.

Conclude with `⟨z, hz.trans hy⟩⟩`. Establish `hω` using `hρ.weil_base i j b`. Establish `hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1 (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1)`. Establish `h1` using `hω`. Rewrite `h1` using `[Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta]`.

Conclude with `h1`. Take `⟨_, ⟨z, rfl⟩, ⟨mz, hmz, hz⟩, xi, hxi, hθ⟩` from `theta_twist (R := Rl.toRealDat) hcore.lev hcore.thP j C.σ₂ hG.2.2.1.1 htw hω' h`. Establish `hzi : la.valuation _ z ≤ 1` using `(hla z).1 (mem_of_pow_eq_one hmz hz (hΛ _ (hLe ⟨z, rfl⟩)))`. Establish `hTC : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T j (D.ntw.l i) C` using `⟨hG.1, hG.2.2.1.2.1, hcl, hG.2.2.1.2.2.2.2⟩`. Establish `hFB : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.FieldBig Rl.toRealDat (Submodule.span ℤ {v'}) C`.

Use `⟨GlobalTheory.Member.character_quotient_values_in_embedding_field.small_quot_values D Γ Pl0 T0 A3.A _ Rl.toRealDat j _ C.σ₂ hG.2.2.2.1, fun w hw m => ?_, hM ▸ containsRayField_of_rayIn C.σ₂ hG.2.2.2.2⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Establish `h1 : MvPolynomial.coeff m (v' : Pol ℂ D.what₂.Tau (Vc D j).rank) ∈ C.σ₂.fieldRange`. Express the relevant statement in the definitionally equal form `MvPolynomial.coeff m (MvPolynomial.map D.what₂.embLL v.1) ∈ _`. Rewrite using `[MvPolynomial.coeff_map]`.

Conclude with `hL0 (hvc m)`. Establish `h2` using `zsmul_mem h1 r`. Rewrite `h2` using `[← MvPolynomial.coeff_smul]`. Conclude with `h2`. Set `k : Subring ℂ` to `C.σ₂.range ⊓ Λ`.

Establish `hk : ∀ {H : Type} [Group H] [Finite H] (f : H →* ℂˣ) (x : H), ((f x : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange → ((f x : ℂˣ) : ℂ) ∈ k` using `fun {H} _ _ f x hx => ⟨hx, mem_of_pow_eq_one (m := Nat.card H) Nat.card_pos (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]) (hΛ _ (hLe hx))⟩`. Use `haveI : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot`. Establish `hser : ∀ a', ∃ φ ∈ C.intForms (wtA (κ j)) (κ j).n {la}, castDict hV φ = (((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * c₀)) • series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (Base.univFam (univOf D.nexp i (admissibleConjuga …` using `fun a' => by`. Take `⟨hd1, hd2⟩` from `isLevelFn_datumFn hB hadm (fun PP hP => GlobalTheory.HalfCompare.not_mem_of_coprime PP hcop (hN PP hP)) _ hN k (fun g => hk _ _ (hchi g)) (fun PP hP x => by`. Take `⟨k, hk'⟩` from `hPg PP hP`.

Conclude with `hk _ _ (hL0 (char_mem_of_over hroots hk' _ x))) (fun PP hP x => hk _ _ (hres PP hP x))`. Use the proof step `(fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))`. Use `fun PP y => ⟨SubfieldClass.ratCast_mem C.σ₂.fieldRange _, by`. Establish `h1` using `GlobalTheory.NormUnit.normProd_inv_mem D ρ i b {PP.1} (Finset.disjoint_singleton_left.2 (Finset.disjoint_left.1 hQ.2.2 (hsub PP.2)))`. Rewrite `h1` using `[normProd, Finset.prod_singleton]`.

Rewrite using `[Base.univFam, univCoef_eq]`. Use `push_cast`. Rewrite using `[← inv_pow]`. Conclude with `mul_mem (pow_mem h1 _) (natCast_mem Λ _)⟩`. Establish `hth` using `Base.isThetaAt_vecAt hB hadm (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))`.

Establish `hft` using `Base.isThetaFunO_fock_vecAt hB hadm (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ)) (c₀ • P')`. Establish `hLV : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelVec Rl.toRealDat j C.d.l₂.M ((ρ.B i j b).F.datumFn (ρ.B i j b).G ((ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) ((ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw …`. Use `⟨_, _, GlobalTheory.RefDatumLev.isIdemSum_conjPl (isIdemSum_halfIdem hadm.1), fun PP hPP => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨P1, hP1, rfl⟩` from `Finset.mem_image.1 hPP show Formalism.L2.DIV.starOHom ((C.d.l₂.M : ℕ) : 𝓞 D.host.E) ∈ P1.asIdeal`. Rewrite using `[map_natCast, hM]`.

Break down `Finset.mem_union.1 hP1 with h1 | h1` into its components or cases. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.1 h1 show Formalism.L2.DIV.starOHom ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hN P0 (Or.inl hP0)`. Conclude with `hN P1 (Or.inr h1)`.

Rewrite using `[Formalism.L2.Theta.cA_cA, hM]`. Rewrite `hd1` using `[hpin.latS, hpin.latT]`. Conclude with `hd1`. Rewrite using `[Formalism.L2.Theta.cA_cA]`. Unfold `Frame.lat at hth`.

Rewrite `hth` using `[hpin.psi, hpin.latS, hpin.latT, hpin.vac]`. Conclude with `hth`. Take `⟨φ, hφ, hφg⟩` from `hc₂ C hTC hG.2.1 hFB {la} (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hl1) xi hxi _ _ hLV (fun t => by`. Take `⟨⟨y, hy⟩, h2⟩` from `hd2 t`. Conclude with `⟨y, hy, fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact (hla y).1 (hy ▸ h2)⟩)`.

Use the proof step `v' (Submodule.mem_span_singleton_self _)`. Establish `h3` using `GlobalTheory.Cmp.SeriesRay.sum_mem_intForms C _ _ {la} (fun _ : Fin 1 => z) (fun _ q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hzi) (fun _ => φ) fun _ => hφ`. Rewrite `h3` using `[Fin.sum_univ_one]`. Use `⟨_, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[castDict_smul, mul_smul, ← hpin.phase_mul_thetaKO i b hio']`.

Use function extensionality and compare the values at `g`. Establish `e1 : harmVec Rl.toRealDat j u (c0L j v) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') = (ρ.B i j b).F.fock ((ρ.B i j b).vecFam (half (ρ.ch i) (admissi …`. Rewrite using `[← hio', GlobalTheory.ExportSeries.Frame.fock, hpin.psi, hpin.inf, hpin.cartT, hpin.onbT, funext (hpin.onbS i j b)]`. Both sides reduce to the same expression. Rewrite `hft` using `[hpin.psi]`.

Establish `e2` using `hθ _ (e1.symm ▸ hft : IsThetaFunO _ _ _ (harmVec Rl.toRealDat j u (c0L j v) _)) g`. Establish `e3 : castDict hV φ g = ((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D j) g)) : ℂˣ) : ℂ) * thetaKO (Rl.toRealDat.ωP j A3.A.μ0) h g (harmVec Rl.toRealDat j u (c0L j v) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q …` using `(hφg g).trans (congrArg (fun w => ((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D j) g)) : ℂˣ) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series Rl.toRealDat j u h ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPla …`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, e3, smul_eq_mul, smul_eq_mul]`. Use `beta_reduce`. Rewrite using `[e2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∃ φ ∈ C.intForms (wtA (κ j)) (κ j).n {la}, castDict hV φ = (((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * c₀)) • ρ.xi i j b D.nexp Q M h P' a` using `by choose φ hφ hφe using hser`. Take `⟨Φ, h1, h2⟩` from `exists_sum_fibres hV hRF hT hG.1 hG.2.2.2.2 hgood (fun PP hP => hN PP (Or.inr (Finset.mem_union_right _ hP))) a _ _ _ φ hφ`. Use `⟨Φ, h1, funext fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[h2, hφe, Pi.smul_apply, Pi.smul_apply]`.

Conclude with `congrArg _ (Base.xiCoef_apply _ _ _ _ _ _ _ _ _).symm`. Take `⟨φ, hφ, hφe⟩` from `hsum`. Establish `hlast : (κ j).LastPos` using `fun τ k hk => by`. Rewrite using `[(hti.kap j τ).1 k]`. Conclude with `GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk`.

Establish `hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n`. Rewrite using `[(hti.kap j (D.eTau.symm 1)).2.2]`. Conclude with `hnV`. Establish `hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n) ≤ Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧ rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSu …`. Use `(GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ (inR j) (κ j) hlast hn T.σ₀ T.toCore.good_σ₀).trans (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))` and prove the remaining obligations.

Conclude with `((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀`. Conclude with `Formalism.L2.Pj.rdU_mem_offZero _ _`. Establish `hinv : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g` using `fun k hk g => by`. Rewrite using `[LevelInv.apply_eq_castDict hV φ (g * k), LevelInv.apply_eq_castDict hV φ g, LevelInv.cast_mul hV g k, hφe]`. Establish `hlift` using `(GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV (cast (congrArg (GA D) hV) k)).2 (by rw [cast_cast, cast_eq]; exact hk)`.

Rewrite using `[Pi.smul_apply, Pi.smul_apply]`. Use `congrArg _ (DualType.xiCoef_mul_right_of_red hB (D.sp.V_sig _) hgood hadm (Base.isAdmFam_univFam _ _ _) hω hlift.1 ?_ (fun PP hPP => ?_) h P' a _)` and prove the remaining obligations. Rewrite using `[hpin.frT]`. Conclude with `parLev_St hlift.2.1`. Rewrite using `[hpin.frT]`.

Conclude with `(GlobalTheory.PrincipalLevel.upperLeftBlock_eq_one_iff_of_mem_blockTri _ (rank_Wc j).symm _).1 (congrFun hlift.2.2 ⟨PP, (hpin.Pg i j b ▸ hPP : PP ∈ Rl.Pg)⟩)`. Take `⟨m, x, ψ, hx, hψ, hsum⟩` from `hc₁ D T hT _ (inR j) (κ j) hlast (dom_wtA _) hspan (mu_mul_level hcore.lev hti j) C hG.1 (hG.2.1 _ (dom_wtA _)) la p hpla hl1 hl2 φ hφ hinv`. Use `choose o ho using fun k => (hla (x k)).2 (hx k)`. Use `⟨m, o, ψ, hψ, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_assoc, mul_smul, ← hφe, ← castDict_smul, hsum]`.

Conclude with `congrArg _ (Finset.sum_congr rfl fun k _ => by rw [ho k])`.
-/
theorem xi_int_of_ties (hRF : GlobalTheory.NT.RayField) (hSI : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j)
    (hpin : RealPin Rl cG ρ) (hU : ρ.LevelOf D.nexp) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hstd : VStd D j) (hfr : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV)
    (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam,
      harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
        coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) →
      ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → ∀ a, ∃ la : HeightOneSpectrum (𝓞 T.Q.c.F),
        (∀ x : T.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, ρ.eO i b o = T.σ₀ x) ∧
        ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ k, ψ k ∈ baseInt T ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) (κ j).n {la}) ∧
          (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • ρ.xi i j b D.nexp Q M h P a = castDict hV (∑ k, ρ.eO i b (o k) • ψ k) := by
  classical
  have hT := hti.laws
  have hB := hρ.base i j b
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  obtain ⟨c₀, hc₀, gramR, c0R, c0L, hft, u, hu, hsc⟩ := exists_isScale Rl cG v₀ hρ hpin hcore.lev hcore.fam.tie
    hcore.models.cV hcore.thP hio i j b (hti.hv₀ j _)
  obtain ⟨cC, hcC⟩ := GlobalTheory.ExtCoeff.exists_ext_map D.what₂.embLL (VV D.what₂.LL (lamV D j)) (VV ℂ (lamV D j)) (c0L j)
  have hCM : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap Rl.toRealDat j cC := ⟨gramR, c0R, c0L, hft, fun v =>
    ⟨⟨MvPolynomial.map D.what₂.embLL v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ v.2⟩, rfl, hcC v _ rfl⟩⟩
  obtain ⟨ph, hph, hS⟩ := (hSI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hT hcore.lev hcore.grp hcore.fam hcore.models hcore.thP
    hti j hstd hV hfr).1 u hu cC hCM
  have hph0 : ph ≠ 0 := fun e => by simp [e] at hph

  let Λ : Subring ℂ := (ρ.eO i b).range
  let eΛ : D.ntw.O i ≃+* Λ := RingEquiv.ofBijective (ρ.eO i b).rangeRestrict
    ⟨fun x y e => ρ.eO_injective i b (congrArg Subtype.val e), (ρ.eO i b).rangeRestrict_surjective⟩
  haveI : IsDiscreteValuationRing Λ := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eΛ
  have hlu : ¬ IsUnit ((D.ntw.l i : ℕ) : Λ) := fun e => by
    have := e.map eΛ.symm
    rw [map_natCast] at this
    exact D.ntw.O_l i this
  have hΛ : ∀ z ∈ (ρ.e i b).fieldRange, z ∈ Λ ∨ z⁻¹ ∈ Λ := by
    rintro _ ⟨y, rfl⟩
    rcases ValuationRing.isInteger_or_isInteger (D.ntw.O i) y with ⟨o, ho⟩ | ⟨o, ho⟩
    · exact Or.inl ⟨o, congrArg (ρ.e i b) ho⟩
    · exact Or.inr ⟨o, (congrArg (ρ.e i b) ho).trans (map_inv₀ _ _)⟩
  obtain ⟨e, he⟩ := GlobalTheory.TowerPlace.placeIn_unique Λ _ hl hlu
  obtain ⟨c₁, hc₁⟩ := intForm_descent_below _ e hl
  refine ⟨ph * c₀, mul_ne_zero hph0 hc₀, fun P' hP' F' hF => ?_⟩
  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (ρ.B i j b).F.BS hB.wt hm
  have hlam : (ρ.B i j b).w.lam = lamV D j :=
    GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 Rl.toLevCh A3.A.μ0 j _ hcore.lev hB (hpin.mu0 i j b) (hpin.ap i j b) (hpin.am i j b)
  obtain ⟨v, hvc, hv⟩ := exists_vec_of_small j hlam F'
  have hio' : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j v) = c₀ • P' := by
    obtain ⟨u', w₀, hu', -, hw⟩ := IsChosenExtremalVector.io _ (hti.hv₀ j _) hio
    obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
    exact IsScaleAt.ioP_eq (Rl := Rl) (c0 := c0L j) hsc hinj hP' (ioP_mem_harmonic hcore.lev hcore.thP (hcore.models.cV j) hB
      (hpin.psi i j b) (hpin.inf i j b)
      (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
      _ w₀ hw _) (hF.trans hv)
  let v' : VsV D j ℂ := ⟨MvPolynomial.map D.what₂.embLL v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ v.2⟩
  have hv' : cC v' = c0L j v := hcC v _ rfl
  obtain ⟨c₂, hc₂⟩ := hS _ hl h hh (Submodule.span ℤ {v'}) (Submodule.fg_span_singleton _)
  refine ⟨c₁ + c₂, fun Q M hQ a => ?_⟩
  have hsub : half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) ⊆ Q := fun P hP => admissibleConjugatePairPlaces_subset i Q M (mem_half.1 hP).1
  have hgood := GlobalTheory.UnivGood.univOf_good D D.nd D.ntw ρ hρ D.nexp i Q M
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) := GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D D.nd D.ntw ρ hρ i j b _
    (fun P hP => hQ.1 P (admissibleConjugatePairPlaces_subset i Q M hP)) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))

  obtain ⟨C, hG, hcl, hL0, hLe, hpd, hQpd, hchi, hres⟩ := exists_cover_coprime YS hρ i j b hRF hT hti.alg hgal hval hray hde hU
    (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (fun P hP => hQ.2.1 P (hsub hP)) (hQ.2.2.mono_left hsub) (κ j).n
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hG.1.2.2.1
  obtain ⟨la, -, hla, hl1, hl2⟩ := he _ C.σ₂ fun x => hΛ _ (hLe ⟨x, rfl⟩)
  obtain ⟨p, -, hp, -, -⟩ := he _ T.σ₀ fun x => hΛ _ (hLe ⟨C.inc x, hσ₂ x⟩)
  have hpla := comap_eq_of_le_one_iff C.inc p la fun x => by rw [← hla, ← hp, hσ₂]
  refine ⟨p, fun x => by rw [GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff, ← hp]; rfl, ?_⟩
  have hM : C.d.l₂.M = T.Q.l.M * C.d.pd := hG.1.1.2.1
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have hPg : ∀ PP ∈ (ρ.B i j b).G.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hρ.Pg i j b
  have hN : ∀ PP, PP ∈ (ρ.B i j b).G.Pg ∨ PP ∈ (ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) →
      ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rintro PP (hP | hP)
    · obtain ⟨k, hk⟩ := hPg PP hP
      refine GlobalTheory.HalfCompare.mem_of_dvd hk (Dvd.dvd.mul_right ?_ _)
      rw [hMg]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    · rcases Finset.mem_union.1 hP with hP | hP
      · rw [hρ.delta] at hP
        exact GlobalTheory.HalfCompare.mem_of_dvd ((mem_pD_iff i PP).1 (mem_half.1 hP).1) (hpd.mul_left _)
      · exact GlobalTheory.HalfCompare.mem_of_dvd (hQpd PP hP) (dvd_mul_left _ _)
  have hcop : Nat.Coprime (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK) (T.Q.l.M * C.d.pd) := by
    refine Nat.Coprime.mul_right ?_ hG.2.2.1.2.2.2.2.symm
    rw [hMg]
    exact Nat.Coprime.mul_right (GlobalTheory.CoverHalf.g_coprime D 0).symm (GlobalTheory.CoverHalf.g_coprime D 1).symm
  have hδ := isDelta_delAt Rl.C (D.ntw.l i)
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi :=
    ⟨hpin.delta i j b, hδ.fin, hδ.triv, hδ.tame, fun w hw => hδ.unr w fun h0 => hw (GlobalTheory.HalfCompare.mem_of_dvd h0 hpd),
      fun w hw => by
        obtain ⟨y, hy⟩ := valuesIn_delAt hval _ w hw
        obtain ⟨z, hz⟩ := hL0 ⟨y, rfl⟩
        exact ⟨z, hz.trans hy⟩⟩
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at h1
    exact h1
  obtain ⟨_, ⟨z, rfl⟩, ⟨mz, hmz, hz⟩, xi, hxi, hθ⟩ := theta_twist (R := Rl.toRealDat) hcore.lev hcore.thP j C.σ₂ hG.2.2.1.1 htw hω' h
  have hzi : la.valuation _ z ≤ 1 := (hla z).1 (mem_of_pow_eq_one hmz hz (hΛ _ (hLe ⟨z, rfl⟩)))
  have hTC : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T j (D.ntw.l i) C := ⟨hG.1, hG.2.2.1.2.1, hcl, hG.2.2.1.2.2.2.2⟩
  have hFB : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.FieldBig Rl.toRealDat (Submodule.span ℤ {v'}) C := by
    refine ⟨GlobalTheory.Member.character_quotient_values_in_embedding_field.small_quot_values D Γ Pl0 T0 A3.A _ Rl.toRealDat j _ C.σ₂ hG.2.2.2.1, fun w hw m => ?_,
      hM ▸ containsRayField_of_rayIn C.σ₂ hG.2.2.2.2⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 : MvPolynomial.coeff m (v' : Pol ℂ D.what₂.Tau (Vc D j).rank) ∈ C.σ₂.fieldRange := by
      change MvPolynomial.coeff m (MvPolynomial.map D.what₂.embLL v.1) ∈ _
      rw [MvPolynomial.coeff_map]
      exact hL0 (hvc m)
    have h2 := zsmul_mem h1 r
    rw [← MvPolynomial.coeff_smul] at h2
    exact h2

  let k : Subring ℂ := C.σ₂.range ⊓ Λ
  have hk : ∀ {H : Type} [Group H] [Finite H] (f : H →* ℂˣ) (x : H), ((f x : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange →
      ((f x : ℂˣ) : ℂ) ∈ k := fun {H} _ _ f x hx => ⟨hx, mem_of_pow_eq_one (m := Nat.card H) Nat.card_pos
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]) (hΛ _ (hLe hx))⟩
  haveI : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

  have hser : ∀ a', ∃ φ ∈ C.intForms (wtA (κ j)) (κ j).n {la}, castDict hV φ =
      (((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * c₀)) • series (ρ.B i j b).F (ρ.om i j b 1)
      ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') h P' := fun a' => by
    obtain ⟨hd1, hd2⟩ := isLevelFn_datumFn hB hadm (fun PP hP => GlobalTheory.HalfCompare.not_mem_of_coprime PP hcop (hN PP hP)) _ hN
      k (fun g => hk _ _ (hchi g)) (fun PP hP x => by
        obtain ⟨k, hk'⟩ := hPg PP hP
        exact hk _ _ (hL0 (char_mem_of_over hroots hk' _ x))) (fun PP hP x => hk _ _ (hres PP hP x))
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))
      fun PP y => ⟨SubfieldClass.ratCast_mem C.σ₂.fieldRange _, by
        have h1 := GlobalTheory.NormUnit.normProd_inv_mem D ρ i b {PP.1} (Finset.disjoint_singleton_left.2
          (Finset.disjoint_left.1 hQ.2.2 (hsub PP.2)))
        rw [normProd, Finset.prod_singleton] at h1
        rw [Base.univFam, univCoef_eq]
        push_cast
        rw [← inv_pow]
        exact mul_mem (pow_mem h1 _) (natCast_mem Λ _)⟩
    have hth := Base.isThetaAt_vecAt hB hadm
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))
    have hft := Base.isThetaFunO_fock_vecAt hB hadm
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ)) (c₀ • P')
    have hLV : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelVec Rl.toRealDat j C.d.l₂.M
        ((ρ.B i j b).F.datumFn (ρ.B i j b).G ((ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          ((ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
            fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ)))
        ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') := by
      refine ⟨_, _, GlobalTheory.RefDatumLev.isIdemSum_conjPl (isIdemSum_halfIdem hadm.1), fun PP hPP => ?_, ?_, ?_⟩
      · obtain ⟨P1, hP1, rfl⟩ := Finset.mem_image.1 hPP
        show Formalism.L2.DIV.starOHom ((C.d.l₂.M : ℕ) : 𝓞 D.host.E) ∈ P1.asIdeal
        rw [map_natCast, hM]
        rcases Finset.mem_union.1 hP1 with h1 | h1
        · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 h1
          show Formalism.L2.DIV.starOHom ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
          rw [map_natCast]
          exact hN P0 (Or.inl hP0)
        · exact hN P1 (Or.inr h1)
      · rw [Formalism.L2.Theta.cA_cA, hM]
        rw [hpin.latS, hpin.latT] at hd1
        exact hd1
      · rw [Formalism.L2.Theta.cA_cA]
        unfold Frame.lat at hth
        rw [hpin.psi, hpin.latS, hpin.latT, hpin.vac] at hth
        exact hth
    obtain ⟨φ, hφ, hφg⟩ := hc₂ C hTC hG.2.1 hFB {la} (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hl1) xi hxi _ _ hLV
      (fun t => by
        obtain ⟨⟨y, hy⟩, h2⟩ := hd2 t
        exact ⟨y, hy, fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact (hla y).1 (hy ▸ h2)⟩)
      v' (Submodule.mem_span_singleton_self _)
    have h3 := GlobalTheory.Cmp.SeriesRay.sum_mem_intForms C _ _ {la} (fun _ : Fin 1 => z)
      (fun _ q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hzi) (fun _ => φ) fun _ => hφ
    rw [Fin.sum_univ_one] at h3
    refine ⟨_, h3, ?_⟩
    rw [castDict_smul, mul_smul, ← hpin.phase_mul_thetaKO i b hio']
    funext g
    have e1 : harmVec Rl.toRealDat j u (c0L j v) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') = (ρ.B i j b).F.fock
        ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') (c₀ • P') := by
      rw [← hio', GlobalTheory.ExportSeries.Frame.fock, hpin.psi, hpin.inf, hpin.cartT, hpin.onbT, funext (hpin.onbS i j b)]
      rfl
    rw [hpin.psi] at hft
    have e2 := hθ _ (e1.symm ▸ hft : IsThetaFunO _ _ _ (harmVec Rl.toRealDat j u (c0L j v) _)) g
    have e3 : castDict hV φ g = ((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D j) g)) : ℂˣ) : ℂ) *
        thetaKO (Rl.toRealDat.ωP j A3.A.μ0) h g (harmVec Rl.toRealDat j u (c0L j v)
          ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a')))) :=
      (hφg g).trans (congrArg (fun w => ((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph *
        (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D j) g)) : ℂˣ) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series Rl.toRealDat j u h
          ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') w g))) hv')
    rw [Pi.smul_apply, Pi.smul_apply, e3, smul_eq_mul, smul_eq_mul]
    beta_reduce
    rw [e2]
    ring

  have hsum : ∃ φ ∈ C.intForms (wtA (κ j)) (κ j).n {la}, castDict hV φ =
      (((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * c₀)) • ρ.xi i j b D.nexp Q M h P' a := by
    choose φ hφ hφe using hser
    obtain ⟨Φ, h1, h2⟩ := exists_sum_fibres hV hRF hT hG.1 hG.2.2.2.2 hgood
      (fun PP hP => hN PP (Or.inr (Finset.mem_union_right _ hP))) a _ _ _ φ hφ
    refine ⟨Φ, h1, funext fun g => ?_⟩
    rw [h2, hφe, Pi.smul_apply, Pi.smul_apply]
    exact congrArg _ (Base.xiCoef_apply _ _ _ _ _ _ _ _ _).symm
  obtain ⟨φ, hφ, hφe⟩ := hsum

  have hlast : (κ j).LastPos := fun τ k hk => by
    rw [(hti.kap j τ).1 k]
    exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n := by
    rw [(hti.kap j (D.eTau.symm 1)).2.2]
    exact hnV
  have hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n) ≤
      Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
        rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
          (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)}) := by
    refine (GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ (inR j) (κ j) hlast hn T.σ₀ T.toCore.good_σ₀).trans
      (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))
    · exact ((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀
    · exact Formalism.L2.Pj.rdU_mem_offZero _ _
  have hinv : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := fun k hk g => by
    rw [LevelInv.apply_eq_castDict hV φ (g * k), LevelInv.apply_eq_castDict hV φ g, LevelInv.cast_mul hV g k, hφe]
    have hlift := (GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV
      (cast (congrArg (GA D) hV) k)).2 (by rw [cast_cast, cast_eq]; exact hk)
    rw [Pi.smul_apply, Pi.smul_apply]
    refine congrArg _ (DualType.xiCoef_mul_right_of_red hB (D.sp.V_sig _) hgood hadm (Base.isAdmFam_univFam _ _ _) hω
      hlift.1 ?_ (fun PP hPP => ?_) h P' a _)
    · rw [hpin.frT]
      exact parLev_St hlift.2.1
    · rw [hpin.frT]
      exact (GlobalTheory.PrincipalLevel.upperLeftBlock_eq_one_iff_of_mem_blockTri _ (rank_Wc j).symm _).1 (congrFun hlift.2.2 ⟨PP, (hpin.Pg i j b ▸ hPP : PP ∈ Rl.Pg)⟩)
  obtain ⟨m, x, ψ, hx, hψ, hsum⟩ := hc₁ D T hT _ (inR j) (κ j) hlast (dom_wtA _) hspan (mu_mul_level hcore.lev hti j) C hG.1
    (hG.2.1 _ (dom_wtA _)) la p hpla hl1 hl2 φ hφ hinv
  choose o ho using fun k => (hla (x k)).2 (hx k)
  refine ⟨m, o, ψ, hψ, ?_⟩
  rw [pow_add, mul_assoc, mul_smul, ← hφe, ← castDict_smul, hsum]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [ho k])

end Main

end GlobalTheory.XiIntSteps

section Bundles
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)

/- English proof (translation)
Introduce `hA _ hSI D X E Y hF hP hde i _ j b s h hd`. Establish `hC` using `X.char`. Establish `ht : Formalism.IndefR.FWT.TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀` using `⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩`. Establish `hio` using `GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP`. Establish `hpb : X.core.pb = X.R.C.P.pb` using `GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev ((X.geo.pins j).2.tuple ()).half`.

Establish `hV₀ : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j` using `X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀`. Take `⟨u, hu, H⟩` from `GlobalTheory.XiIntSteps.xi_int_of_ties (F := X.F.lv2) Y.YS X.geo.κ X.geo.v₀ Y.Z.good i j b (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hA) hSI hV₀ Y.Z.pin ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩ X.size ⟨hC.lev, hC.grp, hC.fam, …`. Use `⟨u, hu, fun P hP F hPF => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `H P hP F hPF`. Conclude with `⟨c, fun Q M hQ _ a _ => hc Q M hQ a⟩`.
-/
theorem GlobalTheory.XiIntSteps.xi_int_core_forms : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∀ hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j, ∃ la : HeightOneSpectrum (𝓞 X.core.Q.c.F), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) ∧ ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) := by
  intro hA _ hSI D X E Y hF hP hde i _ j b s h hd
  have hC := X.char
  have ht : Formalism.IndefR.FWT.TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev ((X.geo.pins j).2.tuple ()).half
  have hV₀ : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
    X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀
  obtain ⟨u, hu, H⟩ := GlobalTheory.XiIntSteps.xi_int_of_ties (F := X.F.lv2) Y.YS X.geo.κ X.geo.v₀ Y.Z.good i j b
    (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hA) hSI hV₀ Y.Z.pin
    ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩ X.size
    ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ ht hio hpb (X.std j) (hP j hV₀) hF.galois hF.vals hF.ray hF.roots hde hd.fin
  refine ⟨u, hu, fun P hP F hPF => ?_⟩
  obtain ⟨c, hc⟩ := H P hP F hPF
  exact ⟨c, fun Q M hQ _ a _ => hc Q M hQ a⟩

end Bundles
