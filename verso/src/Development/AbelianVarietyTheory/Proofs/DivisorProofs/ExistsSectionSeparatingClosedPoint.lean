import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
open GlobalTheory.Twist GlobalTheory.SerreCriterion

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IsolatedSecZero
variable {X : Scheme.{0}}

/- English proof (translation)
Take `⟨V, hyV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Set `W : X.Opens` to `⟨{y}ᶜ, hy.isOpen_compl⟩`. Set `C : Bool → X.Opens` to `fun b => if b then V ⊓ U else W`. Establish `hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0` using `fun O hO r => by`. Use `TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_` and prove the remaining obligations.

Establish `hz'` using `hO hz`. Establish `hns : z ∉ support F` using `fun h => hz'.2 (hF z hz'.1.2 h)`. Conclude with `(notMem_support_iff.1 hns).elim _ _`. Take `⟨g, hg⟩` from `exists_sec_of_cover (F := F) C (fun _ => le_top) (fun z _ => by`. Distinguish the cases in `h : z = y`.

Substitute `h` using the available equality. Conclude with `Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩`. Conclude with `Opens.mem_iSup.2 ⟨false, h⟩)`. Use the proof step `(fun b => match b with`. Consider the case `true => resM F (inf_le_left : V ⊓ U ≤ V) s`.

Consider the case `false => 0)`. Use the proof step `(fun k l => by`. Apply the tactic sequence `cases k <;> cases l`. Both sides reduce to the same expression. Conclude with `(hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm`.

Conclude with `(hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm`. Use the proof step `rfl)`. Use `⟨g, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hyVU : y ∈ V ⊓ U` using `⟨hyV, hyU⟩`. Use `congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)` as an intermediate fact.

Simplify using `only at this`. Rewrite `this` using `[germ_resM, germ_resM]`. Conclude with `this`. Establish `hzW : z ∈ W` using `hz`. Use `congrArg (F.presheaf.germ W z hzW) (hg false)` as an intermediate fact.

Simplify using `only at this`. Rewrite `this` using `[germ_resM, map_zero]`. Conclude with `this`.
-/
theorem exists_germ_eq_zero_of_isolated {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    {U : X.Opens} (hyU : y ∈ U) (hF : ∀ z ∈ U, z ∈ support F → z = y)
    (t : (F.presheaf.stalk y :)) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t ∧
      ∀ z, z ≠ y → F.presheaf.germ ⊤ z trivial s = 0 := by
  obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  let W : X.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  let C : Bool → X.Opens := fun b => if b then V ⊓ U else W
  have hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0 := fun O hO r => by
    refine TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_
    have hz' := hO hz
    have hns : z ∉ support F := fun h => hz'.2 (hF z hz'.1.2 h)
    exact (notMem_support_iff.1 hns).elim _ _
  obtain ⟨g, hg⟩ := exists_sec_of_cover (F := F) C (fun _ => le_top)
    (fun z _ => by
      by_cases h : z = y
      · subst h; exact Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b => match b with
      | true => resM F (inf_le_left : V ⊓ U ≤ V) s
      | false => 0)
    (fun k l => by
      cases k <;> cases l
      · rfl
      · exact (hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm
      · exact (hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm
      · rfl)
  refine ⟨g, ?_, fun z hz => ?_⟩
  · have hyVU : y ∈ V ⊓ U := ⟨hyV, hyU⟩
    have := congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)
    dsimp only at this
    rw [germ_resM, germ_resM] at this
    exact this
  · have hzW : z ∈ W := hz
    have := congrArg (F.presheaf.germ W z hzW) (hg false)
    dsimp only at this
    rw [germ_resM, map_zero] at this
    exact this
end IsolatedSecZero

/- English proof (translation)
Introduce `k _ X _ q _ N hN J x U hxc hxU hJ h`. Use `set φ := toSubscheme J with hφ`. Set `S : ShortComplex X.Modules` to `ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)`. Establish `hS : S.ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Establish `hS' : (S.map (twistFunctor N)).ShortExact` using `Twist.shortExact_map hN hS`.

Establish `hsurj` using `cohOn.app_surjective hS' ⊤ h`. Establish `hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ N) → z = x`. Introduce `z hzU hz`. Rewrite `hz` using `[support_twist hN]`. Use `mem_support_iff.1 hz` as an intermediate fact.

Use `(hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)` and prove the remaining obligations. Conclude with `mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial`. Establish `hx : x ∈ J.support` using `(hJ x hxU).2 rfl`. Take `⟨c, hc⟩` from `exists_chart hN x`. Set `one : Γ(QCoh.structureModule X, ⊤)` to `(structureModuleSectionsEquiv ⊤).symm 1`.

Take `⟨b, hb, hb0⟩` from `IsolatedSecZero.exists_germ_eq_zero_of_isolated hxc hxU hQ ((stalkEquiv S.X₃ hN c hc).symm (stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one)))`. Take `⟨a, rfl⟩` from `hsurj b`. Use `⟨secOfTwist (𝟙 _) a, ?_, ?_⟩` and prove the remaining obligations. Establish `hm : x ∈ ⊤ ⊓ N.U c` using `⟨trivial, hc⟩ replace hb := (stalkEquiv_germ hN c hc (V := ⊤) trivial _).symm.trans ((LinearEquiv.eq_symm_apply _).1 hb)`. Establish `h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm (coord (F` using `QCoh.structureModule X) a c)) = stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one) := (stalkLinear_germ S.g x hm _).trans hb`.

Establish `h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one - (QCoh.structureModule X).presheaf.germ _ x hm (coord (F` using `QCoh.structureModule X) a c)) = 0 := by`. Rewrite using `[← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]`. Conclude with `(congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)`. Establish `h₃` using `not_isUnit_of_toSubscheme_eq_zero J hx _ h₂`. Rewrite `h₃` using `[map_sub]`.

Use `erw [structureModuleStalkEquiv_germ, structureModuleStalkEquiv_germ] at h₃`. Establish `h1 : structureModuleSectionsEquiv ⊤ one = 1` using `by simp [one]`. Rewrite `h₃` using `[h1, map_one]`. Establish `hu` using `(IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃`. Use `basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)` and prove the remaining obligations.

Use `erw [secOfTwist_f]`. Conclude with `(congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu`. Introduce `y hy hyx hmem`. Take `⟨d, hd⟩` from `Opens.mem_iSup.1 hmem`. Establish `hyd : y ∈ N.U d` using `X.basicOpen_le _ hd`.

Establish `hm : y ∈ ⊤ ⊓ N.U d` using `⟨trivial, hyd⟩`. Establish `e0` using `hb0 y hyx`. Establish `h₁ : stalkLinear S.g y ((QCoh.structureModule X).presheaf.germ _ y hm (coord (F` using `QCoh.structureModule X) a d)) = 0 := by`. Use `(stalkEquiv_germ hN d hyd (V := ⊤) trivial _).symm.trans (congrArg (stalkEquiv S.X₃ hN d hyd) e0)` as an intermediate fact. Rewrite `this` using `[map_zero]`.

Conclude with `(stalkLinear_germ S.g y hm _).trans this`. Establish `h₂ : stalkLinear φ y ((QCoh.structureModule X).presheaf.germ _ y hm (coord (F` using `QCoh.structureModule X) a d)) = 0 := by`. Rewrite using `[← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply]`. Conclude with `(congrArg _ h₁).trans (map_zero _)`. Establish `h₃` using `not_isUnit_of_toSubscheme_eq_zero J hy _ h₂`.

Rewrite `h₃` using `[structureModuleStalkEquiv_germ]`. Apply `h₃` to reduce the goal to its premises. Use `erw [secOfTwist_f] at hd`. Conclude with `(congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hyd _)).mp ((X.mem_basicOpen _ y hyd).1 hd)`.
-/
theorem exists_sec_mem_nonzeroLocus_of_isolated_zero_else : ∀ (k : Type) [Field k] (X : Scheme.{0})
    [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB →
    ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U →
    (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) →
    ∃ s : L.Sec, x ∈ nonzeroLocus s ∧ ∀ y ∈ J.support, y ≠ x → y ∉ nonzeroLocus s := by
  intro k _ X _ q _ N hN J x U hxc hxU hJ h
  set φ := toSubscheme J with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor N)).ShortExact := Twist.shortExact_map hN hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ N) → z = x := by
    intro z hzU hz
    rw [support_twist hN] at hz
    have := mem_support_iff.1 hz
    refine (hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial
  have hx : x ∈ J.support := (hJ x hxU).2 rfl
  obtain ⟨c, hc⟩ := exists_chart hN x
  let one : Γ(QCoh.structureModule X, ⊤) := (structureModuleSectionsEquiv ⊤).symm 1
  obtain ⟨b, hb, hb0⟩ := IsolatedSecZero.exists_germ_eq_zero_of_isolated hxc hxU hQ
    ((stalkEquiv S.X₃ hN c hc).symm
      (stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨secOfTwist (𝟙 _) a, ?_, ?_⟩
  · have hm : x ∈ ⊤ ⊓ N.U c := ⟨trivial, hc⟩
    replace hb := (stalkEquiv_germ hN c hc (V := ⊤) trivial _).symm.trans
      ((LinearEquiv.eq_symm_apply _).1 hb)
    have h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm
        (coord (F := QCoh.structureModule X) a c)) =
        stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one) :=
      (stalkLinear_germ S.g x hm _).trans hb
    have h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one -
        (QCoh.structureModule X).presheaf.germ _ x hm (coord (F := QCoh.structureModule X) a c)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
      exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hx _ h₂
    rw [map_sub] at h₃
    erw [structureModuleStalkEquiv_germ, structureModuleStalkEquiv_germ] at h₃
    have h1 : structureModuleSectionsEquiv ⊤ one = 1 := by simp [one]
    rw [h1, map_one] at h₃
    have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
    refine basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)
    erw [secOfTwist_f]
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
  · intro y hy hyx hmem
    obtain ⟨d, hd⟩ := Opens.mem_iSup.1 hmem
    have hyd : y ∈ N.U d := X.basicOpen_le _ hd
    have hm : y ∈ ⊤ ⊓ N.U d := ⟨trivial, hyd⟩
    have e0 := hb0 y hyx
    have h₁ : stalkLinear S.g y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      have := (stalkEquiv_germ hN d hyd (V := ⊤) trivial _).symm.trans
        (congrArg (stalkEquiv S.X₃ hN d hyd) e0)
      rw [map_zero] at this
      exact (stalkLinear_germ S.g y hm _).trans this
    have h₂ : stalkLinear φ y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply]
      exact (congrArg _ h₁).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hy _ h₂
    rw [structureModuleStalkEquiv_germ] at h₃
    apply h₃
    erw [secOfTwist_f] at hd
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hyd _)).mp
      ((X.mem_basicOpen _ y hyd).1 hd)
end GlobalTheory
