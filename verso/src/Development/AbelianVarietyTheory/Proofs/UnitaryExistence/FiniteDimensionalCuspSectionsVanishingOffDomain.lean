import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstMinimumLowerBoundNearMax
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPosLowerBoundNearMax

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFinData

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Use `⟨X.dom, Set.Subsingleton.finite ?_, fun P _ hP x hx => hP x hx⟩` and prove the remaining obligations. Introduce `a _ b _`. Use function extensionality and compare the values at `τ i`. Conclude with `i.elim0`.

Take `⟨ε, hε, hla1⟩` from `_root_.GlobalTheory.exists_lower_bound_half_max_norm E r X la hr`. Take `⟨K, hK, hKdom, hKmove⟩` from `_root_.GlobalTheory.FlagMahler.mahler_compactness r X ε hε`. Take `⟨β, hβc, hβ⟩` from `_root_.GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt r X`. Establish `hcont : ContinuousOn (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) X.dom`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat`.

Use `fun_prop`. Use `set K' := (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) '' K with hK'`. Establish `hK'c : IsCompact K'` using `hK.image_of_continuousOn (hcont.mono hKdom)`. Establish `hK'dom : K' ⊆ X.dom`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `_root_.ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X (hKdom hx) (hβ x (hKdom hx)).1`. Use `set δ : ℝ := 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|)) with hδ`. Establish `hδpos : 0 < δ`. Rewrite using `[hδ]`. Apply `one_div_pos.mpr` to reduce the goal to its premises.

Establish `: (0 : ℝ) < (r : ℝ) ^ 2` using `by positivity`. Establish `: (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)|` using `by positivity`. Check the signs of the components of the expression. Take `⟨N, hNK, hNnear⟩` from `_root_.GlobalTheory.CuspNet.exists_finset_rmul_near_one X hK'c hK'dom hδpos`. Use `⟨(N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), N.finite_toSet, ?_⟩` and prove the remaining obligations.

Introduce `P hP hPN`. Establish `hP'` using `hP`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP'`. Take `⟨⟨hSec, C, hC⟩, -⟩` from `hP'`. Establish `hpz : ∀ x ∈ X.dom, X.pnorm la P x = 0`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨x0, hx0, hx0ne⟩` from `hne`. Establish `hx0pos : 0 < X.pnorm la P x0` using `lt_of_le_of_ne (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_nonneg X la P x0) (Ne.symm hx0ne)`. Use `set T : Set ℝ := (fun x => X.pnorm la P x) '' X.dom with hT`.

Establish `hTbdd : BddAbove T` using `⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩`. Establish `hTne : T.Nonempty` using `⟨_, x0, hx0, rfl⟩`. Use `set S := sSup T with hS`. Establish `hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S` using `fun x hx => le_csSup hTbdd ⟨x, hx, rfl⟩`. Establish `hSpos : 0 < S` using `lt_of_lt_of_le hx0pos (hle x0 hx0)`.

Take `⟨_, ⟨z, hz, rfl⟩, hzS⟩` from `exists_lt_of_lt_csSup hTne (half_lt_self hSpos)`. Establish `hzpos : 0 < X.pnorm la P z` using `lt_trans (half_pos hSpos) hzS`. Establish `hz2 : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z` using `fun x hx => by`. Combine the linear relations using `[hle x hx]`. Establish `hεz : ε ≤ X.la1 z` using `hla1 P hP z hz hz2 hzpos`.

Take `⟨γ, hγ, b, hb, hyK⟩` from `hKmove z hz hεz`. Use `set y := _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul z b) with hy`. Establish `hydom : y ∈ X.dom` using `hKdom hyK`. Establish `hpy : X.pnorm la P y = X.pnorm la P z` using `_root_.GlobalTheory.NormFactor.pnormInv_holds r X la P hSec γ hγ z hz b hb`. Take `⟨hβy, hnorm⟩` from `hβ y hydom`.

Use `set y' := _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (β y) with hy'`. Establish `hpy' : X.pnorm la P y' = X.pnorm la P y` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hSec.2.1 y hydom (β y) hβy`. Establish `hy'K : y' ∈ K'` using `⟨y, hyK, rfl⟩`. Take `⟨A, hA, hAN⟩` from `hNnear y' hy'K`. Establish `hnorm'` using `hnorm`.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hnorm'`. Establish `hhalf : S / 2 ≤ X.pnorm la P y'` using `by rw [hpy', hpy]; exact hzS.le`. Take `⟨-, hquarter⟩` from `_root_.GlobalTheory.pnorm_near_half_max X la P hSec.1 S hle y' hnorm' hhalf A hA`. Establish `hzero : X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y' A) = 0`. Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPN _ (Finset.mem_coe.mpr hAN)]`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx`. Establish `h` using `hpz x hx`. Rewrite `h` using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq]`.

Establish `hn` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay.nfac_pos X la hx`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `norm_eq_zero.mp h`. Conclude with `absurd h hn.ne'`.
-/
private lemma exists_finite_determining_set_SS
    {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    ∃ N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), N.Finite ∧
      ∀ P ∈ X.SS la, (∀ y ∈ N, P y = 0) → ∀ x ∈ X.dom, P x = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨X.dom, Set.Subsingleton.finite ?_, fun P _ hP x hx => hP x hx⟩
    intro a _ b _
    funext τ i
    exact i.elim0
  obtain ⟨ε, hε, hla1⟩ := _root_.GlobalTheory.exists_lower_bound_half_max_norm E r X la hr
  obtain ⟨K, hK, hKdom, hKmove⟩ := _root_.GlobalTheory.FlagMahler.mahler_compactness r X ε hε
  obtain ⟨β, hβc, hβ⟩ := _root_.GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt r X
  have hcont : ContinuousOn (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) X.dom := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    fun_prop
  set K' := (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) '' K with hK'
  have hK'c : IsCompact K' := hK.image_of_continuousOn (hcont.mono hKdom)
  have hK'dom : K' ⊆ X.dom := by
    rintro _ ⟨x, hx, rfl⟩
    exact _root_.ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X (hKdom hx) (hβ x (hKdom hx)).1
  set δ : ℝ := 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    apply one_div_pos.mpr
    have : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by positivity
    positivity
  obtain ⟨N, hNK, hNnear⟩ := _root_.GlobalTheory.CuspNet.exists_finset_rmul_near_one X hK'c hK'dom hδpos
  refine ⟨(N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), N.finite_toSet, ?_⟩
  intro P hP hPN
  have hP' := hP
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP'
  obtain ⟨⟨hSec, C, hC⟩, -⟩ := hP'
  have hpz : ∀ x ∈ X.dom, X.pnorm la P x = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨x0, hx0, hx0ne⟩ := hne
    have hx0pos : 0 < X.pnorm la P x0 := lt_of_le_of_ne (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_nonneg X la P x0) (Ne.symm hx0ne)
    set T : Set ℝ := (fun x => X.pnorm la P x) '' X.dom with hT
    have hTbdd : BddAbove T := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
    have hTne : T.Nonempty := ⟨_, x0, hx0, rfl⟩
    set S := sSup T with hS
    have hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S := fun x hx => le_csSup hTbdd ⟨x, hx, rfl⟩
    have hSpos : 0 < S := lt_of_lt_of_le hx0pos (hle x0 hx0)
    obtain ⟨_, ⟨z, hz, rfl⟩, hzS⟩ := exists_lt_of_lt_csSup hTne (half_lt_self hSpos)
    have hzpos : 0 < X.pnorm la P z := lt_trans (half_pos hSpos) hzS
    have hz2 : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z := fun x hx => by
      linarith [hle x hx]
    have hεz : ε ≤ X.la1 z := hla1 P hP z hz hz2 hzpos
    obtain ⟨γ, hγ, b, hb, hyK⟩ := hKmove z hz hεz
    set y := _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul z b) with hy
    have hydom : y ∈ X.dom := hKdom hyK
    have hpy : X.pnorm la P y = X.pnorm la P z :=
      _root_.GlobalTheory.NormFactor.pnormInv_holds r X la P hSec γ hγ z hz b hb
    obtain ⟨hβy, hnorm⟩ := hβ y hydom
    set y' := _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (β y) with hy'
    have hpy' : X.pnorm la P y' = X.pnorm la P y := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hSec.2.1 y hydom (β y) hβy
    have hy'K : y' ∈ K' := ⟨y, hyK, rfl⟩
    obtain ⟨A, hA, hAN⟩ := hNnear y' hy'K
    have hnorm' := hnorm
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hnorm'
    have hhalf : S / 2 ≤ X.pnorm la P y' := by rw [hpy', hpy]; exact hzS.le
    obtain ⟨-, hquarter⟩ := _root_.GlobalTheory.pnorm_near_half_max X la P hSec.1 S hle y' hnorm' hhalf A hA
    have hzero : X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y' A) = 0 := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPN _ (Finset.mem_coe.mpr hAN)]
      simp
    linarith
  intro x hx
  have h := hpz x hx
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq] at h
  have hn := _root_.ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay.nfac_pos X la hx
  rcases mul_eq_zero.mp h with h | h
  · exact norm_eq_zero.mp h
  · exact absurd h hn.ne'

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `E _ _ _ r Comp _ X la W hW hoff`. Use `choose N hNfin hN using fun k => exists_finite_determining_set_SS (X k) (la k)`. Use `haveI : ∀ k, Fintype (N k) := fun k => (hNfin k).fintype`. Set `L : W →ₗ[ℂ] ((k : Comp) → N k → ℂ)` to `{ toFun := fun P k y => P.1 k y map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hinj : Function.Injective L`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `P hP`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k x`. Use `show P.1 k x = 0`.

Establish `hcusp` using `_root_.GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub X la (hW P.2) k`. Distinguish the cases in `hx : x ∈ (X k).dom`. Conclude with `hN k _ hcusp (fun y hy => congrFun (congrFun hP k) ⟨y, hy⟩) x hx`. Conclude with `hoff P.1 P.2 k x hx`. Conclude with `Module.Finite.of_injective L hinj`.
-/
theorem _root_.GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (W : Submodule ℂ (_root_.Formalism.L2.PjFree.FDSec X)), W ≤ _root_.Formalism.L2.PjFree.holSub X la →
    (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  intro E _ _ _ r Comp _ X la W hW hoff
  choose N hNfin hN using fun k => exists_finite_determining_set_SS (X k) (la k)
  haveI : ∀ k, Fintype (N k) := fun k => (hNfin k).fintype
  let L : W →ₗ[ℂ] ((k : Comp) → N k → ℂ) :=
    { toFun := fun P k y => P.1 k y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    funext k x
    show P.1 k x = 0
    have hcusp := _root_.GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub X la (hW P.2) k
    by_cases hx : x ∈ (X k).dom
    · exact hN k _ hcusp (fun y hy => congrFun (congrFun hP k) ⟨y, hy⟩) x hx
    · exact hoff P.1 P.2 k x hx
  exact Module.Finite.of_injective L hinj

end GlobalTheory.CuspSecFinData
