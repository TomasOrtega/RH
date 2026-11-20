import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative

noncomputable section

namespace GlobalTheory.HeightCounting.Blocks

open NumberField IsDedekindDomain Polynomial Filter

section Satake

open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

/- English proof (translation)
Establish `hc` using `Final.GLintComm E w n`. Set `τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) (I →₀ V)` to `{ toFun := fun g => Finsupp.mapRange.linearMap (σ g) map_one' := by ext; simp map_mul' := fun g g' => by ext; simp }`. Establish `hτ : ∀ g i v, τ g (Finsupp.single i v) = Finsupp.single i (σ g v)` using `fun g i v => Finsupp.mapRange_single (hf := map_zero _)`. Set `p : (I →₀ V) →ₗ[ℂ] W` to `Finsupp.lsum ℂ f`. Establish `hp : ∀ i v, p (Finsupp.single i v) = f i v` using `fun i v => Finsupp.lsum_single ℂ f i v`.

Establish `hpe : ∀ g m, p (τ g m) = ρ g (p m)` using `fun g m => by`. Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single i v => rw [hτ, hp, hp, hf]`.

Take `⟨x₀, hx₀⟩` from `h.exists_vec`. Establish `hfin : ∀ m, m ∈ HeckeScalar.finOrbit τ (KGL w n)` using `fun m => by`. Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b ha hb => exact add_mem ha hb`.

Consider the case `single i v`. Take `⟨φ, rfl⟩` from `HeckeScalar.orbitMap_surjective hσ hx₀.2.1 hx₀.1 v`. Use `(Set.Finite.image (fun ψ => Finsupp.single i (HeckeScalar.orbitMap σ (KGL w n) x₀ ψ)) (HeckeScalar.mem_finOrbit hc φ)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, ⟨k, rfl⟩, by simp only [hτ, HeckeScalar.orbitMap_permRep hx₀.2.1]⟩`.

Take `⟨m, rfl⟩ : x ∈ LinearMap.range p` from `(iSup_le fun i => by rintro _ ⟨v, rfl⟩; exact ⟨_, hp i v⟩ : (⨆ i, LinearMap.range (f i)) ≤ LinearMap.range p) hx`. Take `⟨m', hm', e⟩` from `HeckeScalar.exists_fixed_preimage p hpe (hfin m) hK`. Use `⟨h0, hK, h.card, fun ϖ hϖ j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← map_heckeVec hc (Tj_mem_hecke hϖ j) p hpe, ← map_smul]`. Use `congr 1`.

Use extensionality with `i`. Establish `h1 : m' i ∈ fixed σ (KGL w n)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => DFunLike.congr_fun (GlobalTheory.LGrp.mem_fixed.1 hm' k hk) i`. Use `(map_heckeVec hc (Tj_mem_hecke hϖ j) (ρ := τ) (ρ' := σ) (Finsupp.lapply i) (fun _ _ => rfl) m').trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `heckeVec σ _ _ (m' i) = satEig (qV E w) n B j • m' i`. Distinguish the cases in `h2 : m' i = 0`.

Rewrite using `[h2, smul_zero]`. Conclude with `(SatCompare.heckeLin hc (Tj_mem_hecke hϖ j) σ).map_zero`. Conclude with `(h.2 _ h1 h2).2.2.2 ϖ hϖ j hj`.
-/
theorem isSatVecGL_of_mem_iSup {V W I : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hσ : σ.IsIrreducible) {B : Multiset ℂˣ} (h : HasSatGL w σ B) (f : I → V →ₗ[ℂ] W)
    (hf : ∀ i g v, f i (σ g v) = ρ g (f i v)) {x : W} (hx : x ∈ ⨆ i, LinearMap.range (f i))
    (hK : x ∈ fixed ρ (KGL w n)) (h0 : x ≠ 0) : IsSatVecGL w ρ x B := by
  classical
  have hc := Final.GLintComm E w n
  let τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) (I →₀ V) :=
    { toFun := fun g => Finsupp.mapRange.linearMap (σ g)
      map_one' := by ext; simp
      map_mul' := fun g g' => by ext; simp }
  have hτ : ∀ g i v, τ g (Finsupp.single i v) = Finsupp.single i (σ g v) := fun g i v =>
    Finsupp.mapRange_single (hf := map_zero _)
  let p : (I →₀ V) →ₗ[ℂ] W := Finsupp.lsum ℂ f
  have hp : ∀ i v, p (Finsupp.single i v) = f i v := fun i v => Finsupp.lsum_single ℂ f i v
  have hpe : ∀ g m, p (τ g m) = ρ g (p m) := fun g m => by
    induction m using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single i v => rw [hτ, hp, hp, hf]
  obtain ⟨x₀, hx₀⟩ := h.exists_vec
  have hfin : ∀ m, m ∈ HeckeScalar.finOrbit τ (KGL w n) := fun m => by
    induction m using Finsupp.induction_linear with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | single i v =>
      obtain ⟨φ, rfl⟩ := HeckeScalar.orbitMap_surjective hσ hx₀.2.1 hx₀.1 v
      refine (Set.Finite.image (fun ψ => Finsupp.single i (HeckeScalar.orbitMap σ (KGL w n) x₀ ψ))
        (HeckeScalar.mem_finOrbit hc φ)).subset ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, by simp only [hτ, HeckeScalar.orbitMap_permRep hx₀.2.1]⟩
  obtain ⟨m, rfl⟩ : x ∈ LinearMap.range p :=
    (iSup_le fun i => by rintro _ ⟨v, rfl⟩; exact ⟨_, hp i v⟩ : (⨆ i, LinearMap.range (f i)) ≤ LinearMap.range p) hx
  obtain ⟨m', hm', e⟩ := HeckeScalar.exists_fixed_preimage p hpe (hfin m) hK
  refine ⟨h0, hK, h.card, fun ϖ hϖ j hj => ?_⟩
  rw [← e, ← map_heckeVec hc (Tj_mem_hecke hϖ j) p hpe, ← map_smul]
  congr 1
  ext i
  have h1 : m' i ∈ fixed σ (KGL w n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk =>
    DFunLike.congr_fun (GlobalTheory.LGrp.mem_fixed.1 hm' k hk) i
  refine (map_heckeVec hc (Tj_mem_hecke hϖ j) (ρ := τ) (ρ' := σ) (Finsupp.lapply i) (fun _ _ => rfl) m').trans ?_
  change heckeVec σ _ _ (m' i) = satEig (qV E w) n B j • m' i
  by_cases h2 : m' i = 0
  · rw [h2, smul_zero]
    exact (SatCompare.heckeLin hc (Tj_mem_hecke hϖ j) σ).map_zero
  · exact (h.2 _ h1 h2).2.2.2 ϖ hϖ j hj

variable [IsTotallyComplex E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨f, h0, hf⟩` from `hσ`. Take `⟨x, hx⟩` from `h.exists_vec`. Establish `hi : LinearMap.ker f = ⊥` using `((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)`. Establish `h1` using `hx.map f hf ((map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hi)).2 hx.1)`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩`. Introduce `x hx h0`. Use `IsSatVecGL.of_map (ρ' := (finRep E n).comp (locGL E n w)) π.V.subtype (fun _ _ => rfl) Subtype.val_injective ?_` and prove the remaining obligations.

Conclude with `isSatVecGL_of_mem_iSup σ.irred h (fun f : LocSph.Maps π w σ => f.1) (fun f => f.2.2) ((LocSph.iSup_range_eq π w σ hσ).symm ▸ x.2) (GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk)) fun e => h0 (Subtype.ext e)`.
-/
theorem hasSatGL_locRep {π : CuspSub E n} {σ : SmIrr (GL (Fin n) (w.adicCompletion E))} (hσ : π.IsLocComp w σ)
    {B : Multiset ℂˣ} (h : HasSatGL w σ.ρ B) : HasSatGL w (π.locRep w) B := by
  constructor
  · obtain ⟨f, h0, hf⟩ := hσ
    obtain ⟨x, hx⟩ := h.exists_vec
    have hi : LinearMap.ker f = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
    have h1 := hx.map f hf ((map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro x hx h0
    refine IsSatVecGL.of_map (ρ' := (finRep E n).comp (locGL E n w)) π.V.subtype (fun _ _ => rfl) Subtype.val_injective ?_
    exact isSatVecGL_of_mem_iSup σ.irred h (fun f : LocSph.Maps π w σ => f.1) (fun f => f.2.2)
      ((LocSph.iSup_range_eq π w σ hσ).symm ▸ x.2)
      (GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
      fun e => h0 (Subtype.ext e)

end Satake

section Local

open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[CG.loc_eq_zpow (hν.1 w), Units.val_zpow_eq_zpow_val, hν.2.1 w, GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, resCard_eq_normV, GlobalTheory.SmGL.SphCompletion.ord_completion]`. Establish `h0 : Valued.v (x : w.adicCompletion E) ≠ 0` using `by simp`. Establish `e : Formalism.UG.ordV E w x = -WithZero.log (Valued.v (x : w.adicCompletion E))`. Rewrite using `[Formalism.UG.ordV, dif_neg h0]`.

Use `conv_rhs => rw [← WithZero.coe_unzero h0]`. Both sides reduce to the same expression. Rewrite using `[e, ← Complex.ofReal_cpow (by positivity), ← Real.rpow_intCast, ← Real.rpow_mul (by positivity), ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem loc_of_isAbsPow {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (w : HeightOneSpectrum (𝓞 E)) :
    ν.loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) s := by
  ext x
  rw [CG.loc_eq_zpow (hν.1 w), Units.val_zpow_eq_zpow_val, hν.2.1 w, GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow,
    resCard_eq_normV, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have e : Formalism.UG.ordV E w x = -WithZero.log (Valued.v (x : w.adicCompletion E)) := by
    rw [Formalism.UG.ordV, dif_neg h0]
    conv_rhs => rw [← WithZero.coe_unzero h0]
    rfl
  rw [e, ← Complex.ofReal_cpow (by positivity), ← Real.rpow_intCast, ← Real.rpow_mul (by positivity),
    ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_zpow,
    ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

variable [IsTotallyComplex E] (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)

include hF in

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with | _ π =>`. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a π w`. Take `⟨_, _, _, -, H⟩` from `isRec_locRec hL h`. Use `(locPar_mk hL (hσ.twist ν) h).trans ?_` and prove the remaining obligations. Rewrite using `[show locPar hL (Quotient.mk _ π) h = _ from locPar_mk hL hσ h, ← H.nu_eq]`.

Use `congrArg _ ((GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _ (isSmoothChar_loc ν w)).symm.trans ?_)` and prove the remaining obligations. Unfold `GlobalTheory.LocGL.IrrGL.nu`. Use `congr 1`. Conclude with `loc_of_isAbsPow hν w`.
-/
theorem locPar_twist_absPow (π : CG E a) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (h : IsPlaceOver A w) :
    locPar hL (π.twist ν) h = (locPar hL π h).lpTw s := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨_, _, _, -, H⟩ := isRec_locRec hL h
  refine (locPar_mk hL (hσ.twist ν) h).trans ?_
  rw [show locPar hL (Quotient.mk _ π) h = _ from locPar_mk hL hσ h, ← H.nu_eq]
  refine congrArg _ ((GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _ (isSmoothChar_loc ν w)).symm.trans ?_)
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact loc_of_isAbsPow hν w

include hF in

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with | _ π =>`. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a π w`. Establish `e : locPar hL (Quotient.mk _ π) h = _` using `locPar_mk hL hσ h`. Rewrite `hu` using `[e]`. Take `⟨α, hα⟩` from `exists_hasSatake_of_unr (isRec_locRec hL h) hu`.

Use `⟨Finset.univ.val.map α, hasSatGL_locRep hσ (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ _ _).2 ⟨α, rfl, hα⟩)), ?_⟩` and prove the remaining obligations. Rewrite using `[e, rec_eq_diag (isRec_locRec hL h) hα, WD.frobEig_diag, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem exists_hasSat (π : CG E a) (h : IsPlaceOver A w) (hu : (locPar hL π h).unr) :
    ∃ B : Multiset ℂˣ, π.HasSat w B ∧ (locPar hL π h).frobEig = B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  have e : locPar hL (Quotient.mk _ π) h = _ := locPar_mk hL hσ h
  rw [e] at hu
  obtain ⟨α, hα⟩ := exists_hasSatake_of_unr (isRec_locRec hL h) hu
  refine ⟨Finset.univ.val.map α, hasSatGL_locRep hσ (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ _ _).2 ⟨α, rfl, hα⟩)), ?_⟩
  rw [e, rec_eq_diag (isRec_locRec hL h) hα, WD.frobEig_diag, Multiset.map_map]
  rfl

end Local

section Polar

open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E`. Establish `key : ∀ k : E, conjAd E (algebraMap E _ k) = GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (algebraMap E _ k)` using `fun k => by`. Rewrite using `[conjAd_algebraMap, GlobalTheory.UnitaryHeckeBaseChange.adeleConj_algebraMap]`. Both sides reduce to the same expression.

Establish `c1` using `continuous_conjAd (E := E)`. Establish `c2 : Continuous (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E)` using `@continuous_adeleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra`. Establish `i1 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E), (conjAd E (y, z)).1 = (conjAd E (y, 0)).1` using `fun _ _ => rfl`. Establish `i2 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E), (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (y, z)).1 = (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (y, 0)).1` using `fun _ _ => rfl`. Establish `f1 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E), (conjAd E (y, z)).2 = (conjAd E (0, z)).2` using `fun _ _ => rfl`.

Establish `f2 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E), (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (y, z)).2 = (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (0, z)).2` using `fun _ _ => rfl`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `(i1 x.1 x.2).trans ((congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_fst.comp (c1.comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 E) E)))) (continuous_fst.comp (c2.comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 E) E)))) (funext fun k => ?_)) …` and prove the remaining obligations. Use `congrArg Prod.fst (key k)` as an intermediate fact. Conclude with `(i1 _ _).symm.trans (this.trans (i2 _ _))`.

Use `(f1 x.1 x.2).trans ((congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer (continuous_snd.comp (c1.comp (Continuous.prodMk_right (0 : InfiniteAdeleRing E)))) (continuous_snd.comp (c2.comp (Continuous.prodMk_right (0 : InfiniteAdeleRing E)))) (funext fun k => …` and prove the remaining obligations. Use `congrArg Prod.snd (key k)` as an intermediate fact. Conclude with `(f1 _ _).symm.trans (this.trans (f2 _ _))`.
-/
theorem conjAd_eq (x : Ad E) :
    conjAd E x = GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E x := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : E, conjAd E (algebraMap E _ k) =
      GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (algebraMap E _ k) := fun k => by
    rw [conjAd_algebraMap, GlobalTheory.UnitaryHeckeBaseChange.adeleConj_algebraMap]
    rfl
  have c1 := continuous_conjAd (E := E)
  have c2 : Continuous (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E) :=
    @continuous_adeleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have i1 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E), (conjAd E (y, z)).1 = (conjAd E (y, 0)).1 :=
    fun _ _ => rfl
  have i2 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E),
      (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (y, z)).1 =
        (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (y, 0)).1 := fun _ _ => rfl
  have f1 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E), (conjAd E (y, z)).2 = (conjAd E (0, z)).2 :=
    fun _ _ => rfl
  have f2 : ∀ (y : InfiniteAdeleRing E) (z : FiniteAdeleRing (𝓞 E) E),
      (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (y, z)).2 =
        (GlobalTheory.UnitaryHeckeBaseChange.adeleConj (maximalRealSubfield E) E (0, z)).2 := fun _ _ => rfl
  refine Prod.ext ?_ ?_
  · refine (i1 x.1 x.2).trans ((congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer
      (continuous_fst.comp (c1.comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 E) E))))
      (continuous_fst.comp (c2.comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 E) E))))
      (funext fun k => ?_)) x.1).trans (i2 x.1 x.2).symm)
    have := congrArg Prod.fst (key k)
    exact (i1 _ _).symm.trans (this.trans (i2 _ _))
  · refine (f1 x.1 x.2).trans ((congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer
      (continuous_snd.comp (c1.comp (Continuous.prodMk_right (0 : InfiniteAdeleRing E))))
      (continuous_snd.comp (c2.comp (Continuous.prodMk_right (0 : InfiniteAdeleRing E))))
      (funext fun k => ?_)) x.2).trans (f2 x.1 x.2).symm)
    have := congrArg Prod.snd (key k)
    exact (f1 _ _).symm.trans (this.trans (f2 _ _))

def resReal (ξ : HChar E) : HChar (maximalRealSubfield E) :=
  ⟨ξ.1.comp (ideleMap (maximalRealSubfield E) E), ξ.2.1.comp (continuous_ideleMap _ E),
    fun k => (congrArg ξ.1 (ideleMap_principalIdele _ E k)).trans (ξ.2.2 _)⟩

/- English proof (translation)
Use `Subtype.ext (MonoidHom.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ξ.1 x * (ξ.1 (ideleMap _ E (ideleNorm E x)))⁻¹ = _`. Rewrite using `[ideleMap_ideleNorm, map_mul, mul_inv, mul_inv_cancel_left, thetaChar_apply]`. Conclude with `congrArg (fun y => (ξ.1 y)⁻¹) (Units.ext (conjAd_eq _).symm)`.
-/
theorem mul_inv_compNorm (ξ : HChar E) : ξ * (compNorm E (resReal ξ))⁻¹ = thetaChar ξ := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change ξ.1 x * (ξ.1 (ideleMap _ E (ideleNorm E x)))⁻¹ = _
  rw [ideleMap_ideleNorm, map_mul, mul_inv, mul_inv_cancel_left, thetaChar_apply]
  exact congrArg (fun y => (ξ.1 y)⁻¹) (Units.ext (conjAd_eq _).symm)

/- English proof (translation)
Rewrite using `[IsConjDualBy, ← CuspSub.twist_mul, mul_inv_compNorm]`. Establish `h1 : (thetaSub π).Iso π`. Take `⟨T, hT⟩` from `h`. Use `⟨((pull E a).submoduleMap π.V).symm.trans T, fun o φ => ?_⟩` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `((pull E a).submoduleMap π.V).surjective φ`.

Establish `e : (thetaSub π).op o ((pull E a).submoduleMap π.V φ) = (pull E a).submoduleMap π.V (π.op (thetaOp o) φ)` using `Subtype.ext (act_pull o φ.1)`. Rewrite using `[e]`. Conclude with `(congrArg T (((pull E a).submoduleMap π.V).symm_apply_apply _)).trans ((hT o φ).trans (congrArg (π.op o) (congrArg T (((pull E a).submoduleMap π.V).symm_apply_apply φ)).symm))`. Establish `h2` using `h1.twist (thetaChar ξ)`. Rewrite `h2` using `[← thetaSub_twist]`.

Take `⟨T, hT⟩` from `h2`. Use `⟨((pull E a).submoduleMap (π.twist ξ).V).trans T, fun o φ => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg T (Subtype.ext (act_pull o φ.1).symm)).trans (hT o ((pull E a).submoduleMap (π.twist ξ).V φ))`.
-/
theorem isConjDualBy_resReal {π : CuspSub E a} (h : π.IsCsd) (ξ : HChar E) :
    IsConjDualBy (π.twist ξ) (compNorm E (resReal ξ)) := by
  rw [IsConjDualBy, ← CuspSub.twist_mul, mul_inv_compNorm]
  have h1 : (thetaSub π).Iso π := by
    obtain ⟨T, hT⟩ := h
    refine ⟨((pull E a).submoduleMap π.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨φ, rfl⟩ := ((pull E a).submoduleMap π.V).surjective φ
    have e : (thetaSub π).op o ((pull E a).submoduleMap π.V φ) = (pull E a).submoduleMap π.V (π.op (thetaOp o) φ) :=
      Subtype.ext (act_pull o φ.1)
    rw [e]
    exact (congrArg T (((pull E a).submoduleMap π.V).symm_apply_apply _)).trans
      ((hT o φ).trans (congrArg (π.op o) (congrArg T (((pull E a).submoduleMap π.V).symm_apply_apply φ)).symm))
  have h2 := h1.twist (thetaChar ξ)
  rw [← thetaSub_twist] at h2
  obtain ⟨T, hT⟩ := h2
  refine ⟨((pull E a).submoduleMap (π.twist ξ).V).trans T, fun o φ => ?_⟩
  exact (congrArg T (Subtype.ext (act_pull o φ.1).symm)).trans (hT o ((pull E a).submoduleMap (π.twist ξ).V φ))

/- English proof (translation)
Use `(isConjDualBy_resReal h _).isPolarized fun v => ?_` and prove the remaining obligations. Establish `h1 : (resReal (GlobalTheory.HeckeGal.Model.absPow E s)).locInf v (-1) * (resReal (GlobalTheory.HeckeGal.Model.absPow E s)).locInf v (-1) = 1`. Rewrite using `[← map_mul, neg_mul_neg, one_mul, map_one]`. Take `⟨t, ht⟩ : ∃ t : ℝ, (((resReal (GlobalTheory.HeckeGal.Model.absPow E s)).locInf v (-1) : ℂˣ) : ℂ) = Complex.exp (s * t)` from `⟨_, rfl⟩`. Establish `h2` using `congrArg Units.val h1`.

Rewrite `h2` using `[Units.val_mul, Units.val_one, mul_self_eq_one_iff]`. Use `Units.ext (h2.resolve_right fun e => ?_)` and prove the remaining obligations. Rewrite `e` using `[ht, ← Complex.ofReal_mul, ← Complex.ofReal_exp]`. Establish `h3 : Real.exp (s * t) = -1` using `by exact_mod_cast e`. Combine the linear relations using `[Real.exp_pos (s * t)]`.
-/
theorem isPolarized_twist_absPow {π : CuspSub E a} (h : π.IsCsd) (s : ℝ) :
    IsPolarized (π.twist (GlobalTheory.HeckeGal.Model.absPow E s))
      (resReal (GlobalTheory.HeckeGal.Model.absPow E s) * quadChar E ^ (0 + a)) := by
  refine (isConjDualBy_resReal h _).isPolarized fun v => ?_
  have h1 : (resReal (GlobalTheory.HeckeGal.Model.absPow E s)).locInf v (-1) *
      (resReal (GlobalTheory.HeckeGal.Model.absPow E s)).locInf v (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (((resReal (GlobalTheory.HeckeGal.Model.absPow E s)).locInf v (-1) : ℂˣ) : ℂ) =
    Complex.exp (s * t) := ⟨_, rfl⟩
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_one, mul_self_eq_one_iff] at h2
  refine Units.ext (h2.resolve_right fun e => ?_)
  rw [ht, ← Complex.ofReal_mul, ← Complex.ofReal_exp] at e
  have h3 : Real.exp (s * t) = -1 := by exact_mod_cast e
  linarith [Real.exp_pos (s * t)]

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne in

/- English proof (translation)
Establish `hν` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s`. Establish `hr' : (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Rewrite using `[((ParLaws.hasInfChar_infChar π τ).twist _).infChar_eq, (InfType.expo_of_infType E _).2.1 s hν τ]`. Use `⟨(hr τ).1.map (add_left_injective _), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hz`.

Conclude with `(hr τ).2 y hy`. Proceed by induction on `π using Quotient.inductionOn with | _ π =>`. Take `⟨r, wt, HT, H⟩` from `hG E Ω l ι a ha _ _ hr' (isPolarized_twist_absPow hc s)`. Use `⟨r, Units.continuous_val.comp H.cont, fun w hl A h => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)) w`.

Rewrite using `[H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]`. Conclude with `congrArg (fun x : WD h => x.lpTw _) ((ParLaws.locPar_mk hL hσ h).symm.trans (locPar_twist_absPow hL hF (CG.mk π) hν h))`.
-/
theorem exists_rep (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) (π : CG E a) (hc : π.IsCsd) (s : ℝ)
    (hr : ∀ τ, (π.infChar τ).Nodup ∧ ∀ z ∈ π.infChar τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        wdOf h hl ι r = ((ParLaws.locPar hL π h).lpTw s).lpTw ((1 - (a : ℝ)) / 2) := by
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hr' : (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [((ParLaws.hasInfChar_infChar π τ).twist _).infChar_eq, (InfType.expo_of_infType E _).2.1 s hν τ]
    refine ⟨(hr τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact (hr τ).2 y hy
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr' (isPolarized_twist_absPow hc s)
  refine ⟨r, Units.continuous_val.comp H.cont, fun w hl A h => ?_⟩
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)) w
  rw [H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]
  exact congrArg (fun x : WD h => x.lpTw _)
    ((ParLaws.locPar_mk hL hσ h).symm.trans (locPar_twist_absPow hL hF (CG.mk π) hν h))

end Polar

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {l : ℕ} [Fact l.Prime]

variable (N) in

def FrobFam (ι : Qbar l ≃+* ℂ) (f : PlE H → ℂ[X]) : Prop :=
  ∃ F : Qbar l → G H.E N.Om → Qbar l, (∀ z, Continuous (F z)) ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ → ∀ z, ι (F z σ) = (f w).eval (ι z)

variable {ι : Qbar l ≃+* ℂ}

/- English proof (translation)
Take `⟨F, h1, h2⟩` from `h`. Conclude with `⟨F, h1, (h2.and e).mono fun w hw => hw.2 ▸ hw.1⟩`.
-/
theorem FrobFam.congr {f f' : PlE H → ℂ[X]} (h : FrobFam N ι f) (e : ∀ᶠ w in cofinite, f w = f' w) :
    FrobFam N ι f' := by
  obtain ⟨F, h1, h2⟩ := h
  exact ⟨F, h1, (h2.and e).mono fun w hw => hw.2 ▸ hw.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => 1, fun _ => continuous_const, Eventually.of_forall fun _ _ _ _ _ _ => by simp⟩`.
-/
theorem FrobFam.one : FrobFam N ι fun _ => 1 :=
  ⟨fun _ _ => 1, fun _ => continuous_const, Eventually.of_forall fun _ _ _ _ _ _ => by simp⟩

/- English proof (translation)
Take `⟨F, h1, h2⟩` from `h`. Take `⟨F', h1', h2'⟩` from `h'`. Use `⟨fun z σ => F z σ * F' z σ, fun z => (h1 z).mul (h1' z), (h2.and h2').mono fun w hw B σ hB hσ z => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hw.1 B σ hB hσ, hw.2 B σ hB hσ, eval_mul]`.
-/
theorem FrobFam.mul {f f' : PlE H → ℂ[X]} (h : FrobFam N ι f) (h' : FrobFam N ι f') :
    FrobFam N ι fun w => f w * f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  refine ⟨fun z σ => F z σ * F' z σ, fun z => (h1 z).mul (h1' z), (h2.and h2').mono fun w hw B σ hB hσ z => ?_⟩
  rw [map_mul, hw.1 B σ hB hσ, hw.2 B σ hB hσ, eval_mul]

/- English proof (translation)
Take `⟨F, h1, h2⟩` from `h`. Take `⟨F', h1', h2'⟩` from `h'`. Establish `hF : ∀ z, F z = F' z` using `fun z => GlobalTheory.RowPar.eq_of_split hC (h1 z) (h1' z) <| by filter_upwards [h2, h2', e] with w a a' b hw B σ hB hσ`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[a B σ hB hσ, a' B σ hB hσ, b hw]`.

Use `filter_upwards [h2, h2'] with w a a'`. Take `⟨σ, hσ⟩` from `exists_isFrob (N.plOm.2 w)`. Use `Polynomial.funext fun z => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `ι.surjective z`. Rewrite using `[← a _ σ (N.plOm.2 w) hσ, ← a' _ σ (N.plOm.2 w) hσ, hF]`.
-/
theorem FrobFam.eq_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) {f f' : PlE H → ℂ[X]}
    (h : FrobFam N ι f) (h' : FrobFam N ι f') (e : ∀ᶠ w in cofinite, IsSplitPl H w → f w = f' w) :
    ∀ᶠ w in cofinite, f w = f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  have hF : ∀ z, F z = F' z := fun z => GlobalTheory.RowPar.eq_of_split hC (h1 z) (h1' z) <| by
    filter_upwards [h2, h2', e] with w a a' b hw B σ hB hσ
    apply ι.injective
    rw [a B σ hB hσ, a' B σ hB hσ, b hw]
  filter_upwards [h2, h2'] with w a a'
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 w)
  refine Polynomial.funext fun z => ?_
  obtain ⟨z, rfl⟩ := ι.surjective z
  rw [← a _ σ (N.plOm.2 w) hσ, ← a' _ σ (N.plOm.2 w) hσ, hF]

variable (A ι) in

def CuspFam : Prop := ∀ (a : ℕ), 1 ≤ a → ∀ π : A.CG a, A.csd π → ∀ s : ℝ, GlobalTheory.GalOfCusp.RegAlgShift A π s →
  FrobFam N ι fun w => galPol A (A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2))

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Use `FrobFam.one.congr (Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `[galPol, twSum, A.frobEig_tw _ u (A.lpZero_unr w), A.frobEig_zero]`. Consider the case `cons p L ih`.

Take `⟨h1, h2, h3⟩` from `hL p List.mem_cons_self`. Use `((hG _ h1 _ h2 _ h3).mul (ih fun q hq => hL q (List.mem_cons_of_mem _ hq))).congr ?_` and prove the remaining obligations. Use `filter_upwards [A.locG_unr_ae p.1.2, twSum_unr A L] with w a b`. Express the relevant statement in the definitionally equal form `_ = galPol A (A.lpTw (A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) (twSum N A L w)) u)`. Rewrite using `[A.lpTw_sum, A.lpTw_add, sub_add_cancel, galPol, galPol, galPol, A.frobEig_sum _ _ ((A.unr_tw _ _).2 a) ((A.unr_tw _ _).2 (frobEig_twSum b).1), Multiset.map_add, Multiset.prod_add]`.
-/
theorem frobFam_twSum (hG : CuspFam A ι) (u : ℝ) (L : List ((Σ a : ℕ, A.CG a) × ℝ))
    (hL : ∀ p ∈ L, 1 ≤ p.1.1 ∧ A.csd p.1.2 ∧ GlobalTheory.GalOfCusp.RegAlgShift A p.1.2 (p.2 + u - (1 - (p.1.1 : ℝ)) / 2)) :
    FrobFam N ι fun w => galPol A (A.lpTw (twSum N A L w) u) := by
  induction L with
  | nil =>
    refine FrobFam.one.congr (Eventually.of_forall fun w => ?_)
    simp [galPol, twSum, A.frobEig_tw _ u (A.lpZero_unr w), A.frobEig_zero]
  | cons p L ih =>
    obtain ⟨h1, h2, h3⟩ := hL p List.mem_cons_self
    refine ((hG _ h1 _ h2 _ h3).mul (ih fun q hq => hL q (List.mem_cons_of_mem _ hq))).congr ?_
    filter_upwards [A.locG_unr_ae p.1.2, twSum_unr A L] with w a b
    change _ = galPol A (A.lpTw (A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) (twSum N A L w)) u)
    rw [A.lpTw_sum, A.lpTw_add, sub_add_cancel, galPol, galPol, galPol,
      A.frobEig_sum _ _ ((A.unr_tw _ _).2 a) ((A.unr_tw _ _).2 (frobEig_twSum b).1), Multiset.map_add,
      Multiset.prod_add]

open GlobalTheory.SpehRigid in
/- English proof (translation)
Simplify using `only [isoLoc_eq]`. Use `frobFam_twSum hG _ _ fun q hq => ?_` and prove the remaining obligations. Take `⟨p, hp, hq⟩` from `List.mem_flatMap.1 hq`. Take `⟨k, -, rfl⟩` from `List.mem_map.1 hq`. Use `⟨(h0 p hp).1, h.1 p hp, fun τ => ⟨(h.2 p hp τ).1, fun z hz => ?_⟩⟩` and prove the remaining obligations.

Take `⟨m, rfl⟩` from `(h.2 p hp τ).2 z hz`. Conclude with `⟨m - k, by push_cast; ring⟩`.
-/
theorem frobFam_isoLoc (hG : CuspFam A ι) {n : ℕ} {Sig : List (Formalism.BasicNotions.Part A.CG)}
    (h0 : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) (h : IsCohSum A n Sig) :
    FrobFam N ι fun w => galPol A (A.lpTw (isoLoc N A Sig w) ((1 - (n : ℝ)) / 2)) := by
  simp only [isoLoc_eq]
  refine frobFam_twSum hG _ _ fun q hq => ?_
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
  refine ⟨(h0 p hp).1, h.1 p hp, fun τ => ⟨(h.2 p hp τ).1, fun z hz => ?_⟩⟩
  obtain ⟨m, rfl⟩ := (h.2 p hp τ).2 z hz
  exact ⟨m - k, by push_cast; ring⟩

/- English proof (translation)
Use `GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne R H what₂ N A hJ _ _ (fun p hp => ⟨(h0 p hp).1, (h0 p hp).2, h.1 p hp⟩) (fun p hp => ⟨(h0' p hp).1, (h0' p hp).2, h'.1 p hp⟩) ?_` and prove the remaining obligations. Use `filter_upwards [(frobFam_isoLoc hG h0 h).eq_of_split hC (frobFam_isoLoc hG h0' h') (e.mono fun w hw hs => by rw [hw hs]), twSum_unr A (Sig.flatMap (GlobalTheory.SpehRigid.flat N A)), twSum_unr A (Sig'.flatMap (GlobalTheory.SpehRigid.flat N A))] with w a b b'`. Use `eq_of_galPol ?_ ?_ a` and prove the remaining obligations. Rewrite using `[GlobalTheory.SpehRigid.isoLoc_eq]`. Conclude with `(frobEig_twSum b).1`.

Rewrite using `[GlobalTheory.SpehRigid.isoLoc_eq]`. Conclude with `(frobEig_twSum b').1`.
-/
theorem perm_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : IsobaricRigid N A) (hG : CuspFam A ι)
    {n : ℕ} {Sig Sig' : List (Formalism.BasicNotions.Part A.CG)} (h0 : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d)
    (h0' : ∀ p ∈ Sig', 1 ≤ p.a ∧ 1 ≤ p.d) (h : IsCohSum A n Sig) (h' : IsCohSum A n Sig')
    (e : ∀ᶠ w in cofinite, IsSplitPl H w → isoLoc N A Sig w = isoLoc N A Sig' w) : Sig.Perm Sig' := by
  refine GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne R H what₂ N A hJ _ _
    (fun p hp => ⟨(h0 p hp).1, (h0 p hp).2, h.1 p hp⟩) (fun p hp => ⟨(h0' p hp).1, (h0' p hp).2, h'.1 p hp⟩) ?_
  filter_upwards [(frobFam_isoLoc hG h0 h).eq_of_split hC (frobFam_isoLoc hG h0' h')
    (e.mono fun w hw hs => by rw [hw hs]), twSum_unr A (Sig.flatMap (GlobalTheory.SpehRigid.flat N A)),
    twSum_unr A (Sig'.flatMap (GlobalTheory.SpehRigid.flat N A))] with w a b b'
  refine eq_of_galPol ?_ ?_ a
  · rw [GlobalTheory.SpehRigid.isoLoc_eq]; exact (frobEig_twSum b).1
  · rw [GlobalTheory.SpehRigid.isoLoc_eq]; exact (frobEig_twSum b').1

end Record

section True

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne

variable {hL : GlobalTheory.Published.LocalLanglandsGL} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : CGTrue hL D T)

include hF in

/- English proof (translation)
The claim follows from `host_isCMField D.host; ReadsCusp D.naut fun a π => (C.e a π).1 := by have := host_isCMField D.host refine ⟨fun a _ => Subtype.val_injective.comp (C.e a).injective, fun a π _ => (C.e a π).2, fun a π w _ hu => ?_⟩ rw [T.frobEig w _ hu, C.loc] exact exists_hasSat hL hF _ _ (by have …`.
-/
theorem readsCusp : haveI := host_isCMField D.host; ReadsCusp D.naut fun a π => (C.e a π).1 := by
  have := host_isCMField D.host
  refine ⟨fun a _ => Subtype.val_injective.comp (C.e a).injective, fun a π _ => (C.e a π).2, fun a π w _ hu => ?_⟩
  rw [T.frobEig w _ hu, C.loc]
  exact exists_hasSat hL hF _ _ (by have e := (T.unr w _).1 hu; rwa [C.loc] at e)

include hF C in

/- English proof (translation)
Introduce `a ha π hc s hs`. Use `host_isCMField D.host` as an intermediate fact. Take `⟨r, h1, h3⟩` from `exists_rep hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) s fun τ => by`. Use `hs τ` as an intermediate fact. Rewrite `this` using `[C.inf]`. Then use the resulting hypothesis.

Establish `hfin : ∀ᶠ w : PlE D.host in cofinite, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal`. Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0` using `by simpa using hp.out.ne_zero`. Conclude with `((Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv).eventually_cofinite_notMem`. Use `⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.eval z, fun z => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.eval_charpoly]`.

Conclude with `(continuous_const.sub h1).matrix_det`. Use `filter_upwards [hfin, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ z`. Establish `hu'` using `(D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu`. Establish `e : T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r`. Rewrite using `[← D.naut.lpTw_add, T.tw, T.tw, C.loc, h3]`.

Both sides reduce to the same expression. Rewrite using `[galPol, T.frobEig w _ hu', e, ← frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ]`. Conclude with `(eval_map_apply ι.toRingHom _).symm`.
-/
theorem cuspFam (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {l : ℕ} [hp : Fact l.Prime] (ι : Qbar l ≃+* ℂ) :
    CuspFam D.naut ι := by
  intro a ha π hc s hs
  have := host_isCMField D.host
  obtain ⟨r, h1, h3⟩ := exists_rep hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) s fun τ => by
    have := hs τ
    rwa [C.inf] at this
  have hfin : ∀ᶠ w : PlE D.host in cofinite, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by simpa using hp.out.ne_zero
    exact ((Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv).eventually_cofinite_notMem
  refine ⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.eval z, fun z => ?_, ?_⟩
  · simp only [Matrix.eval_charpoly]
    exact (continuous_const.sub h1).matrix_det
  · filter_upwards [hfin, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ z
    have hu' := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
    have e : T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
      rw [← D.naut.lpTw_add, T.tw, T.tw, C.loc, h3]
      rfl
    rw [galPol, T.frobEig w _ hu', e, ← frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ]
    exact (eval_map_apply ι.toRingHom _).symm

end True

end GlobalTheory.HeightCounting.Blocks

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions GlobalTheory.CuspRep Blocks

/- English proof (translation)
Introduce `Sig Sig' h _ _ e`. Use `host_isCMField D.host` as an intermediate fact. Use `haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two`. Take `⟨ι⟩` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2`. Establish `h1` using `fun p hp => h p (List.mem_append_left Sig' hp)`.

Establish `h2` using `fun p hp => h p (List.mem_append_right Sig hp)`. Conclude with `Multiset.coe_eq_coe.2 ((perm_of_split hC (GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hJ (readsCusp hF C)) (cuspFam hF C hG (l := 2) ι) (fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1⟩) (fun p hp => ⟨(h2 p hp).1, (h2 p hp).2.1⟩) ⟨fun p hp => (h1 p hp).2.2.1, fun p hp => (h1 p hp …`.
-/
theorem CGTrue.blocksUnique (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hJ : GlobalTheory.Published.JacquetShalikaRigidity)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : CGTrue hL D T) :
    BlocksUnique D := by
  intro Sig Sig' h _ _ e
  have := host_isCMField D.host
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  have h1 := fun p hp => h p (List.mem_append_left Sig' hp)
  have h2 := fun p hp => h p (List.mem_append_right Sig hp)
  exact Multiset.coe_eq_coe.2 ((perm_of_split hC (GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hJ (readsCusp hF C))
    (cuspFam hF C hG (l := 2) ι) (fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1⟩) (fun p hp => ⟨(h2 p hp).1, (h2 p hp).2.1⟩)
    ⟨fun p hp => (h1 p hp).2.2.1, fun p hp => (h1 p hp).2.2.2⟩ ⟨fun p hp => (h2 p hp).2.2.1, fun p hp => (h2 p hp).2.2.2⟩
    (Filter.Eventually.of_forall e)).map _)

/- English proof (translation)
Introduce `hL hF hG _ hJ hC _ _ C` and use `C.blocksUnique hL hF hG hJ.1 hC`.
-/
theorem blocksUnique_of_cgTrue : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.JacquetShalika →
    GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → BlocksUnique D :=
  fun hL hF hG _ hJ hC _ _ C => C.blocksUnique hL hF hG hJ.1 hC

end GlobalTheory.HeightCounting

end
