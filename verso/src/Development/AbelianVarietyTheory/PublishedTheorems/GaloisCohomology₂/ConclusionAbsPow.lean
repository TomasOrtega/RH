import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCharacterRatio
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMemJumpTypeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.CharAboveModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce `k hk`. Rewrite using `[(absPow_isAbsPow E m).2.2 k]`. Establish `h1 : ∏ φ : E →+* ℂ, ((‖φ (k : E)‖ : ℝ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E)`. Rewrite using `[← Finset.prod_fiberwise (s := Finset.univ) (g := InfinitePlace.mk), ← Finset.prod_fiberwise (s := Finset.univ) (g := InfinitePlace.mk) (f := fun φ : E →+* ℂ => φ (k : E))]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Establish `e : (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) = {w.embedding, ComplexEmbedding.conjugate w.embedding}`. Use extensionality with `φ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Use `conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(h | h)`. Conclude with `Or.inl h`. Conclude with `Or.inr (by rw [← h]; exact (star_star φ).symm)`. Introduce and unpack `(h | h)`. Conclude with `Or.inl h`.

Conclude with `Or.inr (by rw [h]; exact star_star _)`. Rewrite using `[e]`. Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Establish `hr` using `InfinitePlace.isReal_iff.mp hw`. Rewrite using `[ComplexEmbedding.isReal_iff.mp hr]`.

Simplify using `only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.prod_singleton]`. Use `hk hr.embedding` as an intermediate fact. Rewrite using `[← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]`. Establish `hn : w.embedding ≠ ComplexEmbedding.conjugate w.embedding` using `fun h => (InfinitePlace.isComplex_iff.mp hw) (ComplexEmbedding.isReal_iff.mpr h.symm)`. Rewrite using `[Finset.prod_pair hn, Finset.prod_pair hn, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Complex.ofReal_natCast, Complex.cpow_natCast, zpow_natCast]`. Rewrite using `[Finset.prod_pow, Finset.prod_pow, h1]`.
-/
theorem absPow_isAlgPos (E : Type) [Field E] [NumberField E] (m : ℕ) :
    IsAlgPos (absPow E m) (fun _ => (m : ℤ)) := by
  classical
  intro k hk
  rw [(absPow_isAbsPow E m).2.2 k]
  have h1 : ∏ φ : E →+* ℂ, ((‖φ (k : E)‖ : ℝ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) := by
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := InfinitePlace.mk),
      ← Finset.prod_fiberwise (s := Finset.univ) (g := InfinitePlace.mk) (f := fun φ : E →+* ℂ => φ (k : E))]
    refine Finset.prod_congr rfl fun w _ => ?_
    have e : (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by rw [← h]; exact (star_star φ).symm)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact star_star _)
    rw [e]
    rcases w.isReal_or_isComplex with hw | hw
    · have hr := InfinitePlace.isReal_iff.mp hw
      rw [ComplexEmbedding.isReal_iff.mp hr]
      simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.prod_singleton]
      have := hk hr.embedding
      rw [← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]
    · have hn : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
        (InfinitePlace.isComplex_iff.mp hw) (ComplexEmbedding.isReal_iff.mpr h.symm)
      rw [Finset.prod_pair hn, Finset.prod_pair hn, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
  simp only [Complex.ofReal_natCast, Complex.cpow_natCast, zpow_natCast]
  rw [Finset.prod_pow, Finset.prod_pow, h1]

/- English proof (translation)
Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : l.Prime).ne_zero` after adjusting the coercions. Establish `hc : Continuous (cyc E Ω l)` using `(Continuous.units_map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])))).comp (continuous_cycZ E Ω l)`. Use `mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob E Ω art ha _ (μ * (cyc E Ω l ^ m)⁻¹) (hμ.mul (hc.pow m).inv) (Ideal.finite_factors h0).toFinset fun v hv A hA σ hσ => ?_)` and prove the remaining obligations.

Establish `hv' : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal` using `fun hm => hv (by`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_span_singleton.mpr hm)`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[frob_abs E ha h hv' hA hσ, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, cyc_eq_map_cycZ, Units.coe_map, cycZ_of_isFrob hv' hA hσ]`. Simplify using the standard rewrite rules.
-/
theorem eq_cyc_pow [IsAlgClosure E Ω] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ}
    {m : ℕ} {n : (E →+* ℂ) → ℤ} {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ)
    (h : IsLAdicOf art ι (absPow E m) n μ) : μ = cyc E Ω l ^ m := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hc : Continuous (cyc E Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
        (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])))).comp (continuous_cycZ E Ω l)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob E Ω art ha _ (μ * (cyc E Ω l ^ m)⁻¹)
    (hμ.mul (hc.pow m).inv) (Ideal.finite_factors h0).toFinset fun v hv A hA σ hσ => ?_)
  have hv' : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hm => hv (by
    rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hm)
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  refine Units.ext ?_
  rw [frob_abs E ha h hv' hA hσ, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, cyc_eq_map_cycZ, Units.coe_map,
    cycZ_of_isFrob hv' hA hσ]
  simp

section Loc

variable (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

def powModel (a : ℤ) : ↥Gw →* GL (Fin 1) ↥Bw.LL.1 :=
  (rk1 (cycLL (P.PD Bw.Kw) ↥Bw.LL.1 ^ a)).comp Bw.e.toMonoidHom

omit [NumberField E] in
/- English proof (translation)
Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Establish `e : ((powModel P Bw a (Bw.e.symm g) : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) = GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -a) g`. Use extensionality with `b c`. Use `fin_cases b`. Use `fin_cases c`.

Simplify using `only [powModel, rk1, MonoidHom.comp_apply, Units.coe_map]`. Simplify using `[GlobalTheory.HTW.Rec.Model.cycPowSum]`. Use `show Matrix.toLinAlgEquiv' _ = Matrix.toLinAlgEquiv' _`. Conclude with `congrArg _ e`.
-/
theorem repE_powModel (a : ℤ) : Bw.repE Bw.LL (powModel P Bw a) =
    matRep (GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -a)) := by
  refine MonoidHom.ext fun g => ?_
  have e : ((powModel P Bw a (Bw.e.symm g) : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) =
      GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -a) g := by
    ext b c
    fin_cases b
    fin_cases c
    simp only [powModel, rk1, MonoidHom.comp_apply, Units.coe_map]
    simp [GlobalTheory.HTW.Rec.Model.cycPowSum]
  show Matrix.toLinAlgEquiv' _ = Matrix.toLinAlgEquiv' _
  exact congrArg _ e

end Loc

/- English proof (translation)
Take `⟨T⟩` from `hT`. Take `rfl` from `eq_cyc_pow ha hμ h`. Take `⟨hc, hm⟩` from `GlobalTheory.HTW.Rec.Model.cycPowSum_crys_mult T Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))`. Establish `hd` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw Bw.LL _ _ hc).1`. Establish `hM : IsModel Bw ((rk1 (cyc E Ω l ^ m)).comp (Dec (F` using `E) A).subtype) Bw.LL (powModel P Bw m) := by`.

Use `⟨le_rfl, MonoidHom.ext fun g => ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g)`. Use extensionality with `a c`. Use `fin_cases a`. Use `fin_cases c`.

Simplify using `[powModel, rk1, mapRep, cycLL, P.PD_χ, e, cyc_eq_map_cycZ, Matrix.diagonal_pow]`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply]`. Both sides reduce to the same expression. Establish `hC : Bw.IsCrysE P Bw.LL (powModel P Bw m)`. Rewrite using `[LocBridge.IsCrysE, repE_powModel]`.

Conclude with `hc`. Establish `hD : Bw.IsdRE P Bw.LL (powModel P Bw m)`. Rewrite using `[LocBridge.IsdRE, repE_powModel]`. Establish `h2 : Module.finrank ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (matRep (GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))))) = Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin 1 → ↥Bw.LL.1)` using `hd`. Simplify using `using h2`.

Use `⟨⟨_, _, hM, hD⟩, IsCrysAt.isPotCrysAt P Bw _ ⟨_, _, hM, hC⟩, ⟨_, _, hM, hC⟩, fun τ LL' τ' hτ => ?_⟩` and prove the remaining obligations. Set `τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1` to `(LL'.1.val.comp τ').codRestrict Bw.LL.1.toSubalgebra fun x => Bw.LL_split _ x`. Use `⟨Bw.LL, _, hM, hD, τ₂, fun x => hτ x, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[LocBridge.multE, repE_powModel, hm τ₂ n]`. Simplify using `only [List.ofFn_succ, List.ofFn_zero, Multiset.count_singleton, List.count_cons, List.count_nil]`.

Distinguish the cases in `h : n = -(m : ℤ)`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem conclusion_absPow [IsAlgClosure E Ω] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (ha : IsGlobalArtin art) (m : ℕ) (μ : G E Ω →* (Qbar l)ˣ)
    (hμ : Continuous μ) (h : IsLAdicOf art ι (absPow E m) (fun _ => (m : ℤ)) μ) (A : ValuationSubring Ω)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) :
    IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-(m : ℤ)} := by
  obtain ⟨T⟩ := hT
  obtain rfl := eq_cyc_pow ha hμ h
  obtain ⟨hc, hm⟩ := GlobalTheory.HTW.Rec.Model.cycPowSum_crys_mult T Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw Bw.LL _ _ hc).1
  have hM : IsModel Bw ((rk1 (cyc E Ω l ^ m)).comp (Dec (F := E) A).subtype) Bw.LL (powModel P Bw m) := by
    refine ⟨le_rfl, MonoidHom.ext fun g => ?_⟩
    have e := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g)
    ext a c
    fin_cases a
    fin_cases c
    simp [powModel, rk1, mapRep, cycLL, P.PD_χ, e, cyc_eq_map_cycZ, Matrix.diagonal_pow]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply]
    rfl
  have hC : Bw.IsCrysE P Bw.LL (powModel P Bw m) := by
    rw [LocBridge.IsCrysE, repE_powModel]; exact hc
  have hD : Bw.IsdRE P Bw.LL (powModel P Bw m) := by
    rw [LocBridge.IsdRE, repE_powModel]
    have h2 : Module.finrank ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw)
        (matRep (GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))))) =
        Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin 1 → ↥Bw.LL.1) := hd
    simpa using h2
  refine ⟨⟨_, _, hM, hD⟩, IsCrysAt.isPotCrysAt P Bw _ ⟨_, _, hM, hC⟩, ⟨_, _, hM, hC⟩, fun τ LL' τ' hτ => ?_⟩
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1 :=
    (LL'.1.val.comp τ').codRestrict Bw.LL.1.toSubalgebra fun x => Bw.LL_split _ x
  refine ⟨Bw.LL, _, hM, hD, τ₂, fun x => hτ x, fun n => ?_⟩
  rw [LocBridge.multE, repE_powModel, hm τ₂ n]
  simp only [List.ofFn_succ, List.ofFn_zero, Multiset.count_singleton, List.count_cons, List.count_nil]
  by_cases h : n = -(m : ℤ)
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Take `⟨L, r', hM, -, τ', hτ, hc⟩` from `hJ`. Establish `h1` using `(conclusion_absPow P AI hT ι art ha m μ hμ h A O Bw).2.2.2 τ L τ' hτ`. Use extensionality with `a`. Conclude with `(hc a).trans (IsJumpsAt.count_eq P hM hτ h1 a).symm` after adjusting the coercions.
-/
theorem jumps_absPow_eq [IsAlgClosure E Ω] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (ha : IsGlobalArtin art) (m : ℕ) (μ : G E Ω →* (Qbar l)ˣ)
    (hμ : Continuous μ) (h : IsLAdicOf art ι (absPow E m) (fun _ => (m : ℤ)) μ) (A : ValuationSubring Ω)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (τ : E →+* Qbar l) (J : Multiset ℤ) (hJ : IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ J) :
    J = {-(m : ℤ)} := by
  obtain ⟨L, r', hM, -, τ', hτ, hc⟩ := hJ
  have h1 := (conclusion_absPow P AI hT ι art ha m μ hμ h A O Bw).2.2.2 τ L τ' hτ
  ext a
  exact_mod_cast (hc a).trans (IsJumpsAt.count_eq P hM hτ h1 a).symm

/- English proof (translation)
Take `⟨μ, h1, h2⟩` from `ha.exists_isLAdicOf ι (absPow_isAlgPos E m)`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨j, L0, hj, H⟩` from `GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw hA`. Take `⟨Bw, e, -⟩` from `H L0 le_rfl`. Conclude with `⟨μ, absPow_isAlgPos E m, h1, h2, A, hA, L0, Bw, fun x => by rw [e]; exact hj x, Bw.j.comp (algebraMap E Ω), AlgHom.id _ _, fun _ => rfl⟩`.
-/
theorem hypotheses_met [IsAlgClosure E Ω] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (ha : IsGlobalArtin art)
    (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l) :
    ∃ μ : G E Ω →* (Qbar l)ˣ, IsAlgPos (absPow E m) (fun _ => (m : ℤ)) ∧ Continuous μ ∧
      IsLAdicOf art ι (absPow E m) (fun _ => (m : ℤ)) μ ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
      ∃ (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
        ∃ (τ : E →+* Qbar l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.Kw.1), IsInduced Bw τ τ' := by
  obtain ⟨μ, h1, h2⟩ := ha.exists_isLAdicOf ι (absPow_isAlgPos E m)
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨j, L0, hj, H⟩ := GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw hA
  obtain ⟨Bw, e, -⟩ := H L0 le_rfl
  exact ⟨μ, absPow_isAlgPos E m, h1, h2, A, hA, L0, Bw, fun x => by rw [e]; exact hj x,
    Bw.j.comp (algebraMap E Ω), AlgHom.id _ _, fun _ => rfl⟩

end GlobalTheory.Published.CharAboveModel

end
