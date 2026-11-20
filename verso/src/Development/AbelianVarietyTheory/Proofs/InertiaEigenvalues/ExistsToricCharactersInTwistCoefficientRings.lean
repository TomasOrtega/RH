import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFullTeich
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBKeep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterIsLadicOfFiniteOrderHeckeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHeckeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.LamTie GlobalTheory.LamTie.TrueList

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

/- English proof (translation)
Use `haveI : CharZero (FractionRing (T.O0 i)) := (T.emb0 i).charZero_iff (T.emb0 i).injective |>.1 inferInstance`. Set `f : ℤ_[T.l i] →+* FractionRing (T.O0 i)` to `(algebraMap (T.O0 i) (FractionRing (T.O0 i))).comp (algebraMap ℤ_[T.l i] (T.O0 i))`. Establish `hf : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Assume the negation of the conclusion as `h0`. Rewrite `hz` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`. Break down `mul_eq_zero.1 hz with h | h` into its components or cases. Conclude with `((PadicInt.unitCoeff h0).isUnit.map f).ne_zero h`. Conclude with `(pow_ne_zero _ (Nat.cast_ne_zero.2 (T.lPrime i).out.ne_zero)) h`.

Establish `hf0 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i))` using `Function.Injective.of_comp (f := algebraMap (T.O0 i) (FractionRing (T.O0 i))) hf`. Use `haveI : Module.IsTorsionFree ℤ_[T.l i] (T.O0 i) := Module.isTorsionFree_iff_algebraMap_injective.2 hf0`. Use `haveI : Module.IsTorsionFree ℤ_[T.l i] (Qbar (T.l i)) := Module.isTorsionFree_iff_algebraMap_injective.2 (by rw [IsScalarTower.algebraMap_eq ℤ_[T.l i] ℚ_[T.l i] (Qbar (T.l i))]`. Conclude with `(algebraMap ℚ_[T.l i] (Qbar (T.l i))).injective.comp Subtype.val_injective)`. Set `g : T.O0 i →ₐ[ℤ_[T.l i]] Qbar (T.l i)` to `IsAlgClosed.lift`.

Establish `hg : Function.Injective g`. Use `(RingHom.injective_iff_ker_eq_bot g.toRingHom).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[T.l i]) ?_)` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Establish `h1 : algebraMap ℤ_[T.l i] (Qbar (T.l i)) z = 0` using `(g.commutes z).symm.trans hz`.

Conclude with `(map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h1`. Use `haveI : Countable ↥D.LL0 := (Module.finBasis ℚ ↥D.LL0).equivFun.injective.countable`. Set `κ : FractionRing (T.O0 i) →+* Qbar (T.l i)` to `IsFractionRing.lift (g := g.toRingHom) hg`. Take `⟨ι, hι⟩` from `GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (T.l i) ↥D.LL0 (κ.comp (T.emb0 i)) (embLL0 D)`. Conclude with `⟨κ, ι, fun z => (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z), hι⟩`.
-/
theorem exists_reading {D : D7} {N : NData D.R D.host D.what₂} (T : TwR D.LL0 N) (i : T.Tw) :
    ∃ (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
      (∀ z : ℤ_[T.l i], κ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
        algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) ∧
      ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL) := by
  haveI : CharZero (FractionRing (T.O0 i)) := (T.emb0 i).charZero_iff (T.emb0 i).injective |>.1 inferInstance
  let f : ℤ_[T.l i] →+* FractionRing (T.O0 i) :=
    (algebraMap (T.O0 i) (FractionRing (T.O0 i))).comp (algebraMap ℤ_[T.l i] (T.O0 i))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map f).ne_zero h
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (T.lPrime i).out.ne_zero)) h
  have hf0 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    Function.Injective.of_comp (f := algebraMap (T.O0 i) (FractionRing (T.O0 i))) hf
  haveI : Module.IsTorsionFree ℤ_[T.l i] (T.O0 i) := Module.isTorsionFree_iff_algebraMap_injective.2 hf0
  haveI : Module.IsTorsionFree ℤ_[T.l i] (Qbar (T.l i)) := Module.isTorsionFree_iff_algebraMap_injective.2
    (by rw [IsScalarTower.algebraMap_eq ℤ_[T.l i] ℚ_[T.l i] (Qbar (T.l i))]
        exact (algebraMap ℚ_[T.l i] (Qbar (T.l i))).injective.comp Subtype.val_injective)
  let g : T.O0 i →ₐ[ℤ_[T.l i]] Qbar (T.l i) := IsAlgClosed.lift
  have hg : Function.Injective g := by
    refine (RingHom.injective_iff_ker_eq_bot g.toRingHom).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[T.l i]) ?_)
    rw [eq_bot_iff]
    intro z hz
    have h1 : algebraMap ℤ_[T.l i] (Qbar (T.l i)) z = 0 := (g.commutes z).symm.trans hz
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h1
  haveI : Countable ↥D.LL0 := (Module.finBasis ℚ ↥D.LL0).equivFun.injective.countable
  let κ : FractionRing (T.O0 i) →+* Qbar (T.l i) := IsFractionRing.lift (g := g.toRingHom) hg
  obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (T.l i) ↥D.LL0
    (κ.comp (T.emb0 i)) (embLL0 D)
  exact ⟨κ, ι, fun z => (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z), hι⟩

/- English proof (translation)
The claim follows from `GlobalTheory.T.twist_character_is_ladic_of_finite_order_hecke hC Sp ha i κ ι hι`.
-/
theorem delta_isGal (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
    {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) :
    IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := GlobalTheory.T.twist_character_is_ladic_of_finite_order_hecke hC Sp ha i κ ι hι

/- English proof (translation)
The claim follows from `GlobalTheory.T.twistCharacter_eq_galois_of_ladic_unitaryHecke ha κ ι hι b embO hO χ hu S hv H hH hr`.
-/
theorem read_of_isGal {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}
    (ha : IsGlobalArtin art) {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i))
    (hO : ∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x →
      embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y))
    (χ : HChar D.host.E) (hu : χ.IsUnitary) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hv : ∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ))
    (H : NC.HC D.host.E) (hH : ∀ x, H.χ x = χ.1 x) {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}
    (hr : IsGal art κ (sideIso ι b) χ n r) :
    NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i)))
      embO (NC.complexEmbeddingRestrictedToSubfield D) H 0 := GlobalTheory.T.twistCharacter_eq_galois_of_ladic_unitaryHecke ha κ ι hι b embO hO χ hu S hv H hH hr

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `hC hA hR D hE cf Rw low Pq S hL eig θ b0 b1 Sx T Sp Z hZC hZ hT hV hχv hS`. Substitute `hZC` using the available equality. Take `⟨art, ha⟩` from `hA D.host.E D.nd.Om`. Use `choose κ ι hκ hι using fun i => exists_reading T i`. Establish `hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i))` using `fun i j v hv' => by`.

Take `⟨y, hy⟩` from `hV.mu0 j v hv'`. Conclude with `⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩`. Establish `hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i))` using `fun i a v hv' => by`. Take `⟨y, hy⟩` from `hχv a v hv'`. Conclude with `⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩`.

Establish `hδ` using `fun i => delta_isGal hC Sp ha i (κ i) (ι i) (hι i)`. Take `⟨L, e, hcl, hfull⟩` from `exists_twL_full_teich hA hR D D.nd hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS hT`. Use `⟨L, fun F => ⟨hfull F, fun ex h0 th hB th' => ?_⟩⟩` and prove the remaining obligations. Take `⟨B⟩` from `hB`. Use `sideB_keep B (fun s lam => FitTw.toHC (Z.chi (e s lam).2.1)) ?_ ?_` and prove the remaining obligations.

Introduce `i lam P _`. Take `⟨-, -, h2, -, h4⟩` from `hcl i lam`. Rewrite using `[h4 P, h2]`. Set `f : FractionRing (T.O i) →+* ℂ` to `B.twF.iCq i`. Use `show f (((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) = _`.

Rewrite using `[map_zpow₀, map_natCast]`. Establish `e2 : (-(((2 * ((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ)) / 2) = ((-((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ)` using `by push_cast; ring`. Rewrite using `[e2, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]`. Introduce `s lam`. Take `⟨h1, h2, -, ⟨n, r, hr, hG⟩, -⟩` from `hcl s lam`.

Set `C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j)` to `⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩`. Establish `hpD : ∀ v, v ∈ T.pD s ↔ OverP D.host (if T.l s = D.host.pde then D.host.pde' else D.host.pde) v` using `fun v => by`. Rewrite using `[← Finset.mem_coe, T.pD_eq]`. Both sides reduce to the same expression. Establish `hmu : ∀ P, P ∉ T.S0 s → (Z.C.mu0 (e s lam).1).UnrAt P` using `fun P hP => (Z.C.isMu0 _).unr P fun k hk => hP (T.placesOver_subset_exceptional s k hk)`.

Establish `hde : ∀ P, P ∉ T.S0 s → (Z.C.delAt (T.l s)).UnrAt P` using `fun P hP => (inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l s)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional s ((hpD P).2 hk))`. Establish `hcu : ∀ P, P ∉ T.S0 s → (Z.chi (e s lam).2.1).UnrAt P` using `fun P hP => chi_unr hZ _ fun h => hP (hS s P h)`. Establish `hdel : (Z.C.delAt (T.l s)).ValuesIn 0 (embLL0 D)`. Unfold `CharFrame.delAt`. Use `split_ifs`.

Use `exacts [hV.del', hV.del]`. Rewrite using `[hG, h2]`. Use `read_of_isGal ha (κ s) (ι s) (hι s) _ _ (fun x y h => B.chi.ringSpec_sidedEmbedding_fixedField s _ x y h) (Z.lam0 (T.l s) (e s lam).1 (e s lam).2.1) ?_ (T.S0 s) ?_ _ ?_ hr` and prove the remaining obligations. Introduce `x`. Establish `e1` using `(Z.C.isMu0 (e s lam).1).unitary x`.

Establish `e2` using `Z.C.delAt_unitary (T.l s) x`. Establish `e3` using `(hZ.aux (e s lam).2.1).unitary x`. Use `show ‖(((Z.C.mu0 (e s lam).1).1 x * (Z.C.delAt (T.l s)).1 x * ((Z.chi (e s lam).2.1).1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_mul, norm_inv, e1, e2, e3]`. Evaluate the numerical expressions.

Introduce `P hP`. Use `⟨((hmu P hP).mul (hde P hP)).mul (hcu P hP).inv, ?_⟩` and prove the remaining obligations. Take `⟨y1, hy1⟩` from `hV.mu0 (e s lam).1 P (hmu P hP)`. Take `⟨y2, hy2⟩` from `hdel P (hde P hP)`. Take `⟨y3, hy3⟩` from `hχv (e s lam).2.1 P (hcu P hP)`.

Simplify using `only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at hy1 hy2 hy3`. Use `⟨y1 * y2 * y3⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv₀, hy1, hy2, hy3, LamDat.lam0, HChar.val_mul, HChar.val_mul, HChar.val_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]`. Introduce `x`. Rewrite using `[h1]`.

Establish `e1 : (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x = (Z.C.mu0 (e s lam).1).1 x` using `B.ringSpec_normalisedCharacter_eq _ x`. Establish `e2 : (B.chiD.del s).χ x = (Z.C.delAt (T.l s)).1 x` using `B.del_eq s x`. Use `show (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x * (B.chiD.del s).χ x * ((Z.chi (e s lam).2.1).1 x)⁻¹ = _`. Rewrite using `[e1, e2]`. Both sides reduce to the same expression.
-/
theorem exists_twL_installed : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  intro hC hA hR D hE cf Rw low Pq S hL eig θ b0 b1 Sx T Sp Z hZC hZ hT hV hχv hS
  subst hZC
  obtain ⟨art, ha⟩ := hA D.host.E D.nd.Om
  choose κ ι hκ hι using fun i => exists_reading T i
  have hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i j v hv' => by
    obtain ⟨y, hy⟩ := hV.mu0 j v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i a v hv' => by
    obtain ⟨y, hy⟩ := hχv a v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hδ := fun i => delta_isGal hC Sp ha i (κ i) (ι i) (hι i)
  obtain ⟨L, e, hcl, hfull⟩ := exists_twL_full_teich hA hR D D.nd hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS hT
  refine ⟨L, fun F => ⟨hfull F, fun ex h0 th hB th' => ?_⟩⟩
  obtain ⟨B⟩ := hB
  refine sideB_keep B (fun s lam => FitTw.toHC (Z.chi (e s lam).2.1)) ?_ ?_
  · intro i lam P _
    obtain ⟨-, -, h2, -, h4⟩ := hcl i lam
    rw [h4 P, h2]
    let f : FractionRing (T.O i) →+* ℂ := B.twF.iCq i
    show f (((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) = _
    rw [map_zpow₀, map_natCast]
    have e2 : (-(((2 * ((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ)) / 2) = ((-((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [e2, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]
  · intro s lam
    obtain ⟨h1, h2, -, ⟨n, r, hr, hG⟩, -⟩ := hcl s lam
    let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
      ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
    have hpD : ∀ v, v ∈ T.pD s ↔ OverP D.host (if T.l s = D.host.pde then D.host.pde' else D.host.pde) v := fun v => by
      rw [← Finset.mem_coe, T.pD_eq]; rfl
    have hmu : ∀ P, P ∉ T.S0 s → (Z.C.mu0 (e s lam).1).UnrAt P := fun P hP =>
      (Z.C.isMu0 _).unr P fun k hk => hP (T.placesOver_subset_exceptional s k hk)
    have hde : ∀ P, P ∉ T.S0 s → (Z.C.delAt (T.l s)).UnrAt P := fun P hP =>
      (inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l s)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional s ((hpD P).2 hk))
    have hcu : ∀ P, P ∉ T.S0 s → (Z.chi (e s lam).2.1).UnrAt P := fun P hP =>
      chi_unr hZ _ fun h => hP (hS s P h)
    have hdel : (Z.C.delAt (T.l s)).ValuesIn 0 (embLL0 D) := by
      unfold CharFrame.delAt
      split_ifs
      exacts [hV.del', hV.del]
    rw [hG, h2]
    refine read_of_isGal ha (κ s) (ι s) (hι s) _ _ (fun x y h => B.chi.ringSpec_sidedEmbedding_fixedField s _ x y h)
      (Z.lam0 (T.l s) (e s lam).1 (e s lam).2.1) ?_ (T.S0 s) ?_ _ ?_ hr
    · intro x
      have e1 := (Z.C.isMu0 (e s lam).1).unitary x
      have e2 := Z.C.delAt_unitary (T.l s) x
      have e3 := (hZ.aux (e s lam).2.1).unitary x
      show ‖(((Z.C.mu0 (e s lam).1).1 x * (Z.C.delAt (T.l s)).1 x * ((Z.chi (e s lam).2.1).1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_mul, norm_inv, e1, e2, e3]
      norm_num
    · intro P hP
      refine ⟨((hmu P hP).mul (hde P hP)).mul (hcu P hP).inv, ?_⟩
      obtain ⟨y1, hy1⟩ := hV.mu0 (e s lam).1 P (hmu P hP)
      obtain ⟨y2, hy2⟩ := hdel P (hde P hP)
      obtain ⟨y3, hy3⟩ := hχv (e s lam).2.1 P (hcu P hP)
      simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at hy1 hy2 hy3
      refine ⟨y1 * y2 * y3⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv₀, hy1, hy2, hy3, LamDat.lam0, HChar.val_mul, HChar.val_mul, HChar.val_inv,
        Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    · intro x
      rw [h1]
      have e1 : (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x = (Z.C.mu0 (e s lam).1).1 x := B.ringSpec_normalisedCharacter_eq _ x
      have e2 : (B.chiD.del s).χ x = (Z.C.delAt (T.l s)).1 x := B.del_eq s x
      show (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x * (B.chiD.del s).χ x * ((Z.chi (e s lam).2.1).1 x)⁻¹ = _
      rw [e1, e2]
      rfl

end GlobalTheory.LamInstall
