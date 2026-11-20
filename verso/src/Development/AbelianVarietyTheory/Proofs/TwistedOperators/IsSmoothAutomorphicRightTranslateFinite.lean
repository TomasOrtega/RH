import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

variable {D : D7} (θ : InfFam D) (V : HSp D)

/- English proof (translation)
Establish `h1 : (GfC V).Normal` using `MonoidHom.normal_ker _`. Establish `h2 : (GinfC V).Normal` using `MonoidHom.normal_ker _`. Conclude with `Subgroup.commute_of_normal_of_disjoint (GfC V) (GinfC V) h1 h2 (Subgroup.disjoint_def.2 fun {x} hx hy => GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hx hy) a b ha hb`.
-/
theorem comm_fin_real {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GinfC V) : a * b = b * a := by
  have h1 : (GfC V).Normal := MonoidHom.normal_ker _
  have h2 : (GinfC V).Normal := MonoidHom.normal_ker _
  exact Subgroup.commute_of_normal_of_disjoint (GfC V) (GinfC V) h1 h2
    (Subgroup.disjoint_def.2 fun {x} hx hy => GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hx hy) a b ha hb

/- English proof (translation)
Unfold `atTau`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `(GinfC V).one_mem`.
-/
theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

/- English proof (translation)
The claim follows from `atTau_mem θ V τ _`.
-/
theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V :=
  atTau_mem θ V τ _

def rTrL (κ : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ fun g => g * κ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rTrL_apply (κ : GA D V) (φ : GA D V → ℂ) : rTrL V κ φ = rTr V κ φ := rfl

variable {κ : GA D V}

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [Rder, rTr]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[mul_assoc, mul_assoc, comm_fin_real V hκ (oneP_mem θ V τ X t)]`.
-/
theorem Rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ φ) = rTr V κ (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, comm_fin_real V hκ (oneP_mem θ V τ X t)]

/- English proof (translation)
Unfold `RderC`. Rewrite using `[Rder_rTr θ V hκ, Rder_rTr θ V hκ]`. Both sides reduce to the same expression.
-/
theorem RderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ φ) = rTr V κ (RderC θ V τ Z φ) := by
  unfold RderC
  rw [Rder_rTr θ V hκ, Rder_rTr θ V hκ]
  rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons f l ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih fun g hg => hl g (List.mem_cons_of_mem _ hg), hl f List.mem_cons_self]`.
-/
theorem foldr_comm {α : Type} (T : α → α) (l : List (α → α)) (hl : ∀ f ∈ l, ∀ x, f (T x) = T (f x)) (x : α) :
    l.foldr (fun f acc => f acc) (T x) = T (l.foldr (fun f acc => f acc) x) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldr_cons]
    rw [ih fun g hg => hl g (List.mem_cons_of_mem _ hg), hl f List.mem_cons_self]

/- English proof (translation)
Unfold `gelf`. Rewrite using `[← rTrL_apply V κ (∑ _, _), map_sum]`. Use `Finset.sum_congr rfl fun idx _ => ?_` and prove the remaining obligations. Rewrite using `[rTrL_apply]`. Use `foldr_comm (rTr V κ) _ ?_ φ` and prove the remaining obligations.

Introduce `f hf x`. Take `⟨a, rfl⟩` from `List.mem_ofFn.1 hf`. Conclude with `RderC_rTr θ V hκ τ _ x`.
-/
theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ φ) = rTr V κ (gelf θ V τ k φ) := by
  unfold gelf
  rw [← rTrL_apply V κ (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [rTrL_apply]
  refine foldr_comm (rTr V κ) _ ?_ φ
  intro f hf x
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact RderC_rTr θ V hκ τ _ x

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons p l ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih, Rder_rTr θ V hκ]`.
-/
theorem foldr_Rder_rTr (hκ : κ ∈ GfC V) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V κ φ) = rTr V κ (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih, Rder_rTr θ V hκ]

/- English proof (translation)
Use `GlobalTheory.AutFunCounterexample.topGroup_GA D V` as an intermediate fact. Use `⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const)⟩` and prove the remaining obligations. Simplify using `only [rTr]`. Rewrite using `[mul_assoc, h.left γ hγ]`. Take `⟨U, hU, hinv⟩` from `h.level`.

Use `⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun k : GA D V => κ⁻¹ * k * κ⁻¹⁻¹` using `(continuous_const.mul continuous_id).mul continuous_const`. Conclude with `hU.preimage hc`. Establish `hk' : κ⁻¹ * k * κ⁻¹⁻¹ ∈ U` using `hk`. Establish `hf : κ⁻¹ * k * κ⁻¹⁻¹ ∈ GfC V` using `(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hkf) ((GfC V).inv_mem ((GfC V).inv_mem hκ))`.

Simplify using `only [rTr]`. Rewrite using `[← hinv _ hk' hf (g * κ)]`. Use `congr 1`. Use `group`.
-/
theorem isAutFun_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (rTr V κ φ) := by
  have := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const)⟩
  · simp only [rTr]
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, hinv⟩ := h.level
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have hc : Continuous fun k : GA D V => κ⁻¹ * k * κ⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · have hk' : κ⁻¹ * k * κ⁻¹⁻¹ ∈ U := hk
      have hf : κ⁻¹ * k * κ⁻¹⁻¹ ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hkf) ((GfC V).inv_mem ((GfC V).inv_mem hκ))
      simp only [rTr]
      rw [← hinv _ hk' hf (g * κ)]
      congr 1
      group

/- English proof (translation)
Introduce `D θ V κ hκ φ h`. Use `⟨isAutFun_rTr V hκ h.toIsAutFun, fun k τs Xs hX g => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun t : Fin k → ℝ => rTr V κ φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) = fun t : Fin k → ℝ => φ (g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)`. Use function extensionality and compare the values at `t`. Establish `hm : (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V`.

Use `(GinfC V).list_prod_mem fun x hx => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `oneP_mem θ V _ _ _`. Simplify using `only [rTr]`. Rewrite using `[mul_assoc, mul_assoc, comm_fin_real V hκ hm]`.

Rewrite using `[e]`. Conclude with `h.smooth k τs Xs hX (g * κ)`. Take `⟨W, hW, hφ, hst⟩` from `h.zfin`. Use `⟨W.map (rTrL V κ), inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `τ k _ ⟨f, hf, rfl⟩`.

Conclude with `⟨gelf θ V τ k f, hst τ k f hf, (gelf_rTr θ V hκ τ k f).symm⟩`. Take `⟨N, hN⟩` from `h.growth`. Use `⟨N, fun l hl x => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hN l hl (x * κ)`. Use `⟨C, fun g hg => ?_⟩` and prove the remaining obligations.

Rewrite using `[foldr_Rder_rTr θ V hκ]`. Simplify using `only [rTr]`. Rewrite using `[mul_assoc, ← comm_fin_real V hκ hg, ← mul_assoc]`. Conclude with `hC g hg`.
-/
theorem isAutFunSm_rTr : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ,
    IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  intro D θ V κ hκ φ h
  refine ⟨isAutFun_rTr V hκ h.toIsAutFun, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · have e : (fun t : Fin k → ℝ => rTr V κ φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) =
        fun t : Fin k → ℝ => φ (g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
      funext t
      have hm : (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := by
        refine (GinfC V).list_prod_mem fun x hx => ?_
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
        exact oneP_mem θ V _ _ _
      simp only [rTr]
      rw [mul_assoc, mul_assoc, comm_fin_real V hκ hm]
    rw [e]
    exact h.smooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, hφ, hst⟩ := h.zfin
    refine ⟨W.map (rTrL V κ), inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨gelf θ V τ k f, hst τ k f hf, (gelf_rTr θ V hκ τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_rTr θ V hκ]
    simp only [rTr]
    rw [mul_assoc, ← comm_fin_real V hκ hg, ← mul_assoc]
    exact hC g hg

end GlobalTheory.FinTranslate

end
