import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralPointOfTorusPointValuationZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SeriesProportionalAddIotaIffStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparatesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPointStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesAtPoint

section Pull
variable {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

/- English proof (translation)
Introduce `j₁ j₂ hc`. Establish `e : scal π (1 : R) = 1` using `by simp [scal]`. Use `H j₁ j₂ hc` as an intermediate fact. Rewrite using `[Fin.sum_univ_one, e, this]`. Simplify using `only [map_one, _root_.one_mul]`.
-/
theorem secLin_of_secScal {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

/- English proof (translation)
Substitute `e` using the available equality. Use `⟨DVR.pullSec L φ ε s h, DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ (𝟙 _) y hJ).symm, fun R _ x j hj => ?_⟩` and prove the remaining obligations. Establish `hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j` using `fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k`. Use `(CrdCalc.valR_res x _ hj' _).trans ?_` and prove the remaining obligations. Conclude with `(CrdCalc.valR_eq x (h ⁻¹ᵁ LB.wchart L φ j) hj _).trans (CrdCalc.valR_eq (x ≫ h) _ hj (s.f j)).symm`.
-/
theorem exists_pull (hL : L.IsLB) {φ : K₁ → (Y ⟶ X)} {ε : K₁ → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ' : K₁ → (Y' ⟶ X)} (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε s' φ ε s h 1 ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y') (j : K₁ → L.ι), ⊤ ≤ (x ≫ h) ⁻¹ᵁ LB.wchart L φ j →
        valR x (LB.wchart L φ' j) (s'.f j) = valR (x ≫ h) (LB.wchart L φ j) (s.f j) := by
  subst e
  refine ⟨DVR.pullSec L φ ε s h, DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ (𝟙 _) y hJ).symm, fun R _ x j hj => ?_⟩
  have hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  refine (CrdCalc.valR_res x _ hj' _).trans ?_
  exact (CrdCalc.valR_eq x (h ⁻¹ᵁ LB.wchart L φ j) hj _).trans (CrdCalc.valR_eq (x ≫ h) _ hj (s.f j)).symm

/- English proof (translation)
Establish `: (𝟙 (Sp R) : Sp R ⟶ Sp R) (IsLocalRing.closedPoint R) ∈ ⨆ i, M.U i` using `by rw [hM.cover]; trivial`. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Establish `hl' : ⊤ ≤ M.U l` using `(CrdCalc.top_le_iff (𝟙 (Sp R)) _).2 hl`. Establish `le : ∀ V : (Sp R).Opens, V ≤ V ⊓ M.U l` using `fun V => le_inf le_rfl (le_top.trans hl')`. Use `⟨⟨fun j => res (le _) (M.g j l)⟩, fun i j => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (res (le (M.U i ⊓ M.U j))) (hM.cocycle i j l)`. Rewrite `e` using `[map_mul, DVR.res_res', DVR.res_res', DVR.res_res', DVR.res_refl']`. Simplify using `only [DVR.res_res']`. Conclude with `e.symm`.
-/
theorem exists_isGen {R : Type} [CommRing R] [IsLocalRing R] {M : LB (Sp R)} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  have : (𝟙 (Sp R) : Sp R ⟶ Sp R) (IsLocalRing.closedPoint R) ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  have hl' : ⊤ ≤ M.U l := (CrdCalc.top_le_iff (𝟙 (Sp R)) _).2 hl
  have le : ∀ V : (Sp R).Opens, V ≤ V ⊓ M.U l := fun V => le_inf le_rfl (le_top.trans hl')
  refine ⟨⟨fun j => res (le _) (M.g j l)⟩, fun i j => ?_⟩
  have e := congrArg (res (le (M.U i ⊓ M.U j))) (hM.cocycle i j l)
  rw [map_mul, DVR.res_res', DVR.res_res', DVR.res_res', DVR.res_refl'] at e
  simp only [DVR.res_res']
  exact e.symm

end Pull

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

/- English proof (translation)
The claim follows from `exists_isGen (R := PadicAlgCl p) (DVR.linComb_isLB _ u.D.toPre.P.isLB _ _)`.
-/
theorem exists_frm (k : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) :
    ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b, w.IsGen :=
  exists_isGen (R := PadicAlgCl p) (DVR.linComb_isLB _ u.D.toPre.P.isLB _ _)

/- English proof (translation)
Take `⟨l, c, hl, hv⟩` from `hv`. Take `⟨l, rfl⟩ : ∃ l₀, l = fun _ : Fin 1 => l₀` from `⟨l 0, funext fun i => congrArg l (Subsingleton.elim _ _)⟩`. Take `⟨κ, hκ, H⟩` from `hg w hw l (hl.trans ((u.toG a).preimage_mono (LB.wchart_le u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l) 0)))`. Use `⟨κ * (c⁻¹).val, mul_ne_zero hκ (Units.ne_zero _), fun i => ?_⟩` and prove the remaining obligations. Take `⟨σ', h₁, h₂⟩` from `exists_pull u.U.LG.isLB (σ i) (UnifPre.gFK (G := u.G) (PadicAlgCl p)) (φ' := fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (funext fun _ => (Category.comp_id _).symm)`.

Establish `e : (lift (𝟙 (TFK (R` using `u.V) (PadicAlgCl p))) a).left ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by`. Rewrite using `[← Category.assoc, ← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `hsum` using `H σ' (s i) ⟨1, fun _ => 1, fun _ => σ i, fun _ => f i, fun _ => hf i, secLin_of_secScal _ h₁, fun α => secLin_of_secScal _ (hs i α)⟩`. Establish `h₃` using `h₂ (PadicAlgCl p) (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left (fun _ => l) (e.symm ▸ hl)`.

Establish `h₄` using `h₃.trans (congrArg (fun x => valR x (LB.wchart u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l)) ((σ i).f fun _ => l)) e)`. Rewrite using `[hv, _root_.mul_assoc, Units.inv_mul_cancel_left]`. Conclude with `(congrArg (fun x => HasSum _ (κ * x)) h₄).mp hsum`.
-/
theorem hasSum_crd {k : ℕ} {J : Type} {σ : J → (u.H k).Sec} {f : J → ∀ α, u.D.toPre.SecB k α}
    (hf : ∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) {s : J → Fam u.D.toPre (PadicAlgCl p) k}
    (hs : ∀ i, FamOf u.D.toPre _ (f i) (s i)) {a : u.PtC} {g : GtPtF u.D.toPre (PadicAlgCl p)} (hg : u.ParAt k a g)
    {w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b} (hw : w.IsGen) {v : J → PadicAlgCl p}
    (hv : Crd (u.H k) σ (u.toG a) v) :
    ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ i, HasSum (fun χ => GlobalTheory.UT.coef (s i) g w χ) (κ * v i) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  obtain ⟨l, rfl⟩ : ∃ l₀, l = fun _ : Fin 1 => l₀ := ⟨l 0, funext fun i => congrArg l (Subsingleton.elim _ _)⟩
  obtain ⟨κ, hκ, H⟩ := hg w hw l (hl.trans ((u.toG a).preimage_mono
    (LB.wchart_le u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l) 0)))
  refine ⟨κ * (c⁻¹).val, mul_ne_zero hκ (Units.ne_zero _), fun i => ?_⟩
  obtain ⟨σ', h₁, h₂⟩ := exists_pull u.U.LG.isLB (σ i) (UnifPre.gFK (G := u.G) (PadicAlgCl p))
    (φ' := fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (funext fun _ => (Category.comp_id _).symm)
  have e : (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd]
    rfl
  have hsum := H σ' (s i) ⟨1, fun _ => 1, fun _ => σ i, fun _ => f i, fun _ => hf i, secLin_of_secScal _ h₁,
    fun α => secLin_of_secScal _ (hs i α)⟩
  have h₃ := h₂ (PadicAlgCl p) (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left (fun _ => l) (e.symm ▸ hl)
  have h₄ := h₃.trans (congrArg (fun x => valR x (LB.wchart u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l))
    ((σ i).f fun _ => l)) e)
  rw [hv, _root_.mul_assoc, Units.inv_mul_cancel_left]
  exact (congrArg (fun x => HasSum _ (κ * x)) h₄).mp hsum

/- English proof (translation)
Introduce `hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB a ha w hw`. Establish `hN : 4 ≤ S.N` using `(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ u).2.2.2.1`. Establish `hN1 : 1 ≤ S.N` using `le_trans (by norm_num) hN`. Take `⟨-, hsep, hon⟩` from `GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB`. Take `⟨a, rfl⟩` from `hon a ha`.

Take `⟨g, hg⟩` from `GlobalTheory.T.exists_torusExtension_parameter_genericFibrePoint hL hT o Ω S ρ p y₀ u l a`. Take `⟨-, hex, huq, hadd, hι⟩` from `GlobalTheory.T.valuations_torusExtension_points hL o Ω S ρ p y₀ u l`. Take `⟨ν, hν⟩` from `hex g`. Establish `hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) S.N, FamOf u.D.toPre _ (f i) s` using `fun i => by`. Take `⟨s, hs⟩` from `hB.2.2.2.2.1 i`.

Conclude with `GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D S.N s (f i) hs (PadicAlgCl p)`. Use `choose s hs using hs`. Take `⟨fr, hfr⟩` from `exists_frm u S.N g`. Take `⟨κ, hκ, hsum⟩` from `hasSum_crd u hB.2.2.2.1 hs hg hfr hw`. Use `⟨ν, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨r, hr, H⟩` from `GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB s hs g ν fr hν hfr`. Use `⟨fun α i => κ⁻¹ * GlobalTheory.UT.coef (s i) g fr α, ‖κ⁻¹‖ * r, mul_pos (norm_pos_iff.2 (inv_ne_zero hκ)) hr, fun i => ?_, fun α i h => ?_, fun α => ⟨fun i => ?_, ?_⟩⟩` and prove the remaining obligations. Use `(hsum i).mul_left κ⁻¹` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left₀ hκ]`. Then use the resulting hypothesis. Conclude with `(H α).1 i (right_ne_zero_of_mul h)`.

Rewrite using `[norm_mul, _root_.mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left ((H α).2.1 i) (norm_nonneg _)`. Take `⟨i, hi⟩` from `(H α).2.2`. Conclude with `⟨i, by rw [norm_mul, _root_.mul_assoc, hi]⟩`. Introduce and unpack `⟨m, hm⟩`.

Take `⟨-, hio, hsub⟩` from `GlobalTheory.ZH.gt_add_iota_sub_exist hL o Ω S ρ p y₀ u`. Take `⟨h, hh⟩` from `hio m`. Take `⟨g', hg'⟩` from `hsub g h`. Take `⟨ν', hν'⟩` from `hex g'`. Establish `e` using `huq g _ _ hν (hadd g' h g _ _ hg' hν' (hι m h hh))`.

Establish `e0 : (ν' : u.D.toPre.X → ℝ) = 0` using `funext fun α => by`. Use `congrFun e α` as an intermediate fact. Rewrite `this` using `[Pi.add_apply, hm α]`. Conclude with `right_eq_add.1 this`. Take `⟨c, hc, hlev⟩` from `GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero hL o Ω S ρ p y₀ u g' (e0 ▸ hν')`.

Take `⟨a', ha'⟩` from `hon (gPt p ≫ c) (by rw [Category.assoc, hc])`. Establish `hp' : u.ParAt S.N a' g` using `(GlobalTheory.T.seriesProportional_add_iota_iff hL o Ω S ρ p y₀ u S.N a' g' h g m hN1 hh hg').1 ((GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g' a' hc ha'.symm hlev).2 S.N hN1)`. Take `⟨w', hw'⟩` from `CrdCalc.crd_exists (DVR.linComb_isLB _ u.U.LG.isLB _ _) σ (u.toG a')`. Take `⟨κ', hκ', hsum'⟩` from `hasSum_crd u hB.2.2.2.1 hs hp' hfr hw'`. Establish `h₁` using `CrdCalc.crd_smul (Units.mk0 κ hκ) hw`.

Establish `h₂` using `CrdCalc.crd_smul (Units.mk0 κ' hκ') hw'`. Establish `e₃ : (fun j => ((Units.mk0 κ' hκ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w' j) = fun j => ((Units.mk0 κ hκ : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w j`. Use function extensionality and compare the values at `fun j => (hsum' j).unique (hsum j)`. Rewrite `h₂` using `[e₃]`. Conclude with `⟨c, hc, ha'.symm.trans (congrArg u.toG (hsep a' a _ h₂ h₁))⟩`.
-/
theorem main : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∀ w, Crd (u.H S.N) σ a w → ∃ ν : u.D.toPre.X →+ ℝ, Ser l.q S.N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar l.q m α) → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = a) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB a ha w hw
  have hN : 4 ≤ S.N := (GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ u).2.2.2.1
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) hN
  obtain ⟨-, hsep, hon⟩ := GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB
  obtain ⟨a, rfl⟩ := hon a ha
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_torusExtension_parameter_genericFibrePoint hL hT o Ω S ρ p y₀ u l a
  obtain ⟨-, hex, huq, hadd, hι⟩ := GlobalTheory.T.valuations_torusExtension_points hL o Ω S ρ p y₀ u l
  obtain ⟨ν, hν⟩ := hex g
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) S.N, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hB.2.2.2.2.1 i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D S.N s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  obtain ⟨fr, hfr⟩ := exists_frm u S.N g
  obtain ⟨κ, hκ, hsum⟩ := hasSum_crd u hB.2.2.2.1 hs hg hfr hw
  refine ⟨ν, ?_, ?_⟩
  · obtain ⟨r, hr, H⟩ := GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB s hs g ν fr hν hfr
    refine ⟨fun α i => κ⁻¹ * GlobalTheory.UT.coef (s i) g fr α, ‖κ⁻¹‖ * r,
      mul_pos (norm_pos_iff.2 (inv_ne_zero hκ)) hr, fun i => ?_, fun α i h => ?_, fun α => ⟨fun i => ?_, ?_⟩⟩
    · have := (hsum i).mul_left κ⁻¹
      rwa [inv_mul_cancel_left₀ hκ] at this
    · exact (H α).1 i (right_ne_zero_of_mul h)
    · rw [norm_mul, _root_.mul_assoc]
      exact mul_le_mul_of_nonneg_left ((H α).2.1 i) (norm_nonneg _)
    · obtain ⟨i, hi⟩ := (H α).2.2
      exact ⟨i, by rw [norm_mul, _root_.mul_assoc, hi]⟩
  · rintro ⟨m, hm⟩
    obtain ⟨-, hio, hsub⟩ := GlobalTheory.ZH.gt_add_iota_sub_exist hL o Ω S ρ p y₀ u
    obtain ⟨h, hh⟩ := hio m
    obtain ⟨g', hg'⟩ := hsub g h
    obtain ⟨ν', hν'⟩ := hex g'
    have e := huq g _ _ hν (hadd g' h g _ _ hg' hν' (hι m h hh))
    have e0 : (ν' : u.D.toPre.X → ℝ) = 0 := funext fun α => by
      have := congrFun e α
      rw [Pi.add_apply, hm α] at this
      exact right_eq_add.1 this
    obtain ⟨c, hc, hlev⟩ := GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero hL o Ω S ρ p y₀ u g' (e0 ▸ hν')
    obtain ⟨a', ha'⟩ := hon (gPt p ≫ c) (by rw [Category.assoc, hc])
    have hp' : u.ParAt S.N a' g :=
      (GlobalTheory.T.seriesProportional_add_iota_iff hL o Ω S ρ p y₀ u S.N a' g' h g m hN1 hh hg').1
        ((GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g' a' hc ha'.symm hlev).2 S.N hN1)
    obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (DVR.linComb_isLB _ u.U.LG.isLB _ _) σ (u.toG a')
    obtain ⟨κ', hκ', hsum'⟩ := hasSum_crd u hB.2.2.2.1 hs hp' hfr hw'
    have h₁ := CrdCalc.crd_smul (Units.mk0 κ hκ) hw
    have h₂ := CrdCalc.crd_smul (Units.mk0 κ' hκ') hw'
    have e₃ : (fun j => ((Units.mk0 κ' hκ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w' j) =
        fun j => ((Units.mk0 κ hκ : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w j :=
      funext fun j => (hsum' j).unique (hsum j)
    rw [e₃] at h₂
    exact ⟨c, hc, ha'.symm.trans (congrArg u.toG (hsep a' a _ h₂ h₁))⟩

end GlobalTheory.ZH.SeriesAtPoint
