import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [chart, mul_assoc]`.
-/
theorem D_chart_left (F : GA E N → ℂ) (h g : GA E N) : chart (fun x => F (h * x)) g = chart F (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def ltS (h : GA E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun F := ⟨fun g => F.1 (h * g), fun g => by rw [D_chart_left]; exact F.2 (h * g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem ltS_apply (h : GA E N) (F : Sm E N) (g : GA E N) : (ltS h F).1 g = F.1 (h * g) := rfl

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.1 (h * g * finGL E N k) = F.1 (h * (g * finGL E N k))`. Rewrite using `[mul_assoc]`.

Consider the case `cpt k`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.1 (h * g * _) = F.1 (h * (g * _))`. Rewrite using `[mul_assoc]`. Consider the case `lie X`.

Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `lieD X F.1 (h * g) = lieD X (fun x => F.1 (h * x)) g`. Simplify using `only [lieD, D_chart_left]`.
-/
theorem ltS_act (h : GA E N) (o : Op E N) (F : Sm E N) : ltS h (act o F) = act o (ltS h F) := by
  cases o with
  | fin k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * finGL E N k) = F.1 (h * (g * finGL E N k))
    rw [mul_assoc]
  | cpt k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * _) = F.1 (h * (g * _))
    rw [mul_assoc]
  | lie X =>
    refine Subtype.ext (funext fun g => ?_)
    change lieD X F.1 (h * g) = lieD X (fun x => F.1 (h * x)) g
    simp only [lieD, D_chart_left]

/- English proof (translation)
Use `letI : MeasurableSpace (BlockIx N r → Ad E) := borel _`. Establish `: BorelSpace (BlockIx N r → Ad E)` using `⟨rfl⟩`. Take `⟨μ, hμ, hD, hint⟩` from `JDict.exists_normed E N r`. Take `⟨F, h1, h2⟩` from `GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hl hlev μ _ hμ hD`. Establish `key : ∀ (f : GA E N → ℂ) g, ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g`.

Introduce `f g`. Rewrite using `[hint]`. Simplify using `only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]`. Conclude with `⟨F, funext fun g => (h1 g).trans (key _ g), fun X => funext fun g => (h2 X g).trans (key _ g)⟩`.
-/
theorem D_ct_smooth (r : ℕ) (φ : Sm E N) (hl : ∀ γ g, φ.1 (ratGL E N γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E N k φ = φ}) :
    ∃ F : Sm E N, F.1 = An.ctn r φ.1 ∧ ∀ X, (lie E N X F).1 = An.ctn r (lie E N X φ).1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  obtain ⟨F, h1, h2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hl hlev μ _ hμ hD
  have key : ∀ (f : GA E N → ℂ) g, ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  exact ⟨F, funext fun g => (h1 g).trans (key _ g), fun X => funext fun g => (h2 X g).trans (key _ g)⟩

open Classical in

def ctSm (r : ℕ) (φ : Sm E N) : Sm E N := if h : An.ctn r φ.1 ∈ Sm E N then ⟨_, h⟩ else 0

/- English proof (translation)
Take `⟨F, hF, -⟩` from `D_ct_smooth r φ hφ.left hφ.level`. Establish `h : An.ctn r φ.1 ∈ Sm E N` using `hF ▸ F.2`. Simplify using `only [ctSm, dif_pos h]`.
-/
theorem ctSm_val (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) : (ctSm r φ).1 = An.ctn r φ.1 := by
  obtain ⟨F, hF, -⟩ := D_ct_smooth r φ hφ.left hφ.level
  have h : An.ctn r φ.1 ∈ Sm E N := hF ▸ F.2
  simp only [ctSm, dif_pos h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [An.ctn, Pi.add_apply, constantTerm_add hf hg, mul_add]`.
-/
theorem ctn_add (r : ℕ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    An.ctn r (f + g) = An.ctn r f + An.ctn r g := by
  funext x
  simp only [An.ctn, Pi.add_apply, constantTerm_add hf hg, mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [An.ctn, Pi.smul_apply, constantTerm_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ctn_smul (r : ℕ) (c : ℂ) (f : GA E N → ℂ) : An.ctn r (c • f) = c • An.ctn r f := by
  funext x
  simp only [An.ctn, Pi.smul_apply, constantTerm_smul, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨F, hF, hX⟩` from `D_ct_smooth r φ hφ.left hφ.level`. Establish `e : ctSm r φ = F` using `Subtype.ext ((ctSm_val r hφ).trans hF.symm)`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[ctSm_val r hφ', e]`. Consider the cases of `o with`.

Consider the case `fin k`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `An.ctn r (fun x => φ.1 (x * finGL E N k)) g = F.1 (g * finGL E N k)`. Rewrite using `[hF]`. Simplify using `only [An.ctn, constantTerm, mul_assoc]`.

Consider the case `cpt k`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `An.ctn r (fun x => φ.1 (x * _)) g = F.1 (g * _)`. Rewrite using `[hF]`. Simplify using `only [An.ctn, constantTerm, mul_assoc]`.

Consider the case `lie X => exact (hX X).symm`.
-/
theorem ctSm_act (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) (o : Op E N) (hφ' : IsAutForm (act o φ)) :
    ctSm r (act o φ) = act o (ctSm r φ) := by
  obtain ⟨F, hF, hX⟩ := D_ct_smooth r φ hφ.left hφ.level
  have e : ctSm r φ = F := Subtype.ext ((ctSm_val r hφ).trans hF.symm)
  refine Subtype.ext ?_
  rw [ctSm_val r hφ', e]
  cases o with
  | fin k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * finGL E N k)) g = F.1 (g * finGL E N k)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | cpt k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * _)) g = F.1 (g * _)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | lie X => exact (hX X).symm

def Aop (N r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) : Module.End ℂ (Sm E N) := ∑ t ∈ τs, a t • ltS (aT E N r t)

/- English proof (translation)
Simplify using `only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, ltS_apply, smul_eq_mul]`.
-/
theorem Aop_apply (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (F : Sm E N) (g : GA E N) :
    (Aop N r τs a F).1 g = ∑ t ∈ τs, a t * F.1 (aT E N r t * g) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, ltS_apply, smul_eq_mul]

/- English proof (translation)
Simplify using `only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ltS_act]`.
-/
theorem Aop_act (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (o : Op E N) (F : Sm E N) :
    Aop N r τs a (act o F) = act o (Aop N r τs a F) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ltS_act]

/- English proof (translation)
Set `T₁ : V →ₗ[ℂ] Sm E N` to `{ toFun := fun φ => Aop N r τs a (ctSm r φ.1) map_add' := fun φ ψ => by`. Establish `e : ctSm r (φ.1 + ψ.1) = ctSm r φ.1 + ctSm r ψ.1`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_add, ctSm_val r (hV _ (V.add_mem φ.2 ψ.2)), ctSm_val r (hV _ φ.2), ctSm_val r (hV _ ψ.2)]`. Conclude with `ctn_add r (ContAut.continuous_of_isOpen_stab E N _ (hV _ φ.2).level) (ContAut.continuous_of_isOpen_stab E N _ (hV _ ψ.2).level)`.

Simplify using `only [Submodule.coe_add, e, map_add]`. Use the proof step `map_smul' := fun c φ => by`. Establish `e : ctSm r (c • φ.1) = c • ctSm r φ.1`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ctSm_val r (hV _ (V.smul_mem c φ.2)), ctSm_val r (hV _ φ.2)]`.

Conclude with `ctn_smul r c _`. Simplify using `only [Submodule.coe_smul, e, map_smul, RingHom.id_apply] }`. Take `⟨T, hT⟩` from `LinearMap.exists_extend T₁`. Conclude with `⟨T, fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩⟩`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (V : Submodule ℂ (Sm E N)) (hV : ∀ φ ∈ V, IsAutForm φ) (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) :
    ∃ T : Sm E N →ₗ[ℂ] Sm E N, ∀ φ ∈ V, T φ = Aop N r τs a (ctSm r φ) := by
  let T₁ : V →ₗ[ℂ] Sm E N :=
    { toFun := fun φ => Aop N r τs a (ctSm r φ.1)
      map_add' := fun φ ψ => by
        have e : ctSm r (φ.1 + ψ.1) = ctSm r φ.1 + ctSm r ψ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_add, ctSm_val r (hV _ (V.add_mem φ.2 ψ.2)), ctSm_val r (hV _ φ.2),
            ctSm_val r (hV _ ψ.2)]
          exact ctn_add r (ContAut.continuous_of_isOpen_stab E N _ (hV _ φ.2).level)
            (ContAut.continuous_of_isOpen_stab E N _ (hV _ ψ.2).level)
        simp only [Submodule.coe_add, e, map_add]
      map_smul' := fun c φ => by
        have e : ctSm r (c • φ.1) = c • ctSm r φ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_smul, ctSm_val r (hV _ (V.smul_mem c φ.2)), ctSm_val r (hV _ φ.2)]
          exact ctn_smul r c _
        simp only [Submodule.coe_smul, e, map_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₁
  exact ⟨T, fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
