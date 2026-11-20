import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaChain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Unfold `I2.polyDeriv`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `h` using `ContinuousLinearMap.iteratedFDeriv_comp_right g hG 0 (i := Multiset.card (Finsupp.toMultiset m)) le_top`. Rewrite using `[h, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]`.

Simplify using `only [hg]`. Rewrite using `[ContinuousMultilinearMap.map_smul_univ, ← hκ m hm, smul_eq_mul]`. Establish `: (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)), c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) = m.prod fun l k => c l ^ k`. Establish `e1 : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)), c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) = ∏ k : Fin (Finsupp.toMultiset m).toList.length, c ((Finsupp.toMultiset m).toList.get k)` using `Fintype.prod_equiv (finCongr (Multiset.length_toList _).symm) _ _ (fun _ => rfl)`. Rewrite using `[e1, ← List.prod_ofFn]`.

Establish `e2 : (List.ofFn fun k => c ((Finsupp.toMultiset m).toList.get k)) = (Finsupp.toMultiset m).toList.map c`. Rewrite using `[List.ofFn_comp' , List.ofFn_get]`. Rewrite using `[e2, Multiset.prod_map_toList]`. Rewrite using `[Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem polyDeriv_comp_clm {J V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Q : MvPolynomial J ℂ) (u : J → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (g : V →L[ℂ] V) (c : J → ℂ) (hg : ∀ l, g (u l) = c l • u l) (κ : ℂ)
    (hκ : ∀ m ∈ Q.support, (m.prod fun l k => c l ^ k) = κ) :
    I2.polyDeriv Q u (G ∘ g) 0 = κ * I2.polyDeriv Q u G 0 := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right g hG 0
    (i := Multiset.card (Finsupp.toMultiset m)) le_top
  rw [h, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hg]
  rw [ContinuousMultilinearMap.map_smul_univ, ← hκ m hm, smul_eq_mul]
  have : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      m.prod fun l k => c l ^ k := by
    have e1 : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      ∏ k : Fin (Finsupp.toMultiset m).toList.length, c ((Finsupp.toMultiset m).toList.get k) :=
      Fintype.prod_equiv (finCongr (Multiset.length_toList _).symm) _ _ (fun _ => rfl)
    rw [e1, ← List.prod_ofFn]
    have e2 : (List.ofFn fun k => c ((Finsupp.toMultiset m).toList.get k)) = (Finsupp.toMultiset m).toList.map c := by
      rw [List.ofFn_comp' , List.ofFn_get]
    rw [e2, Multiset.prod_map_toList]
    classical
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
  rw [this]; ring

/- English proof (translation)
Unfold `I2.Hf I2.act`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`. Rewrite using `[← h i.1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_act_act {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (M : ℂ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M) (v w : I2.Vsp dim) :
    I2.Hf (I2.act β v) (I2.act β w) = M * I2.Hf v w := by
  unfold I2.Hf I2.act
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  rw [← h i.1]; ring

/- English proof (translation)
Unfold `I2.PT.U I2.HC I2.s0`. Simplify using `only [hf_act_act β M h, ← Finset.mul_sum]`. Use `congr 1`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `_`. Use extensionality with `i`.

Simplify using `[PullbackSections.vspActL, I2.act]`. Rewrite using `[← h' i.1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem translate_eq_comp {E : Type} [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M)
    (h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M) (s : (Fin 1 → I2.Vsp X.dim) → ℂ)
    (a v : Fin n → I2.Vsp X.dim) :
    X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) v =
      X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s) (fun b => I2.act β (v b)) := by
  unfold I2.PT.U I2.HC I2.s0
  simp only [hf_act_act β M h, ← Finset.mul_sum]
  congr 1
  · congr 1; push_cast; ring
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext _
    ext i
    simp [PullbackSections.vspActL, I2.act]
    rw [← h' i.1]; ring

def colMap {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (n : ℕ) :
    (Fin n → I2.Vsp dim) →L[ℂ] (Fin n → I2.Vsp dim) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun b => (vspActL β).comp (LinearMap.proj b))

/- English proof (translation)
Establish `hp : Differentiable ℂ p` using `(LinearMap.toContinuousLinearMap p).differentiable`. Establish `h1 : Differentiable ℂ (I2.s0 X (n` using `n) p s) := by`. Unfold `I2.s0`. Establish `hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => p (v k)` using `fun k => hs.comp (differentiable_pi.2 fun _ => hp.comp (differentiable_apply k))`. Conclude with `fun v => (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (hk k v).hasFDerivAt).differentiableAt`.

Establish `h2 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v a`. Unfold `I2.HC I2.Hf`. Use `Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun i _ => Differentiable.mul_const ?_ _` and prove the remaining obligations. Conclude with `(EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp (differentiable_apply k)`. Unfold `I2.PT.U`.

Conclude with `(((h2.const_mul _).sub_const _).cexp).mul (h1.comp (differentiable_id.sub_const a))`.
-/
theorem differentiable_translate {E : Type} [Field E] [NumberField E] (X : I2.PT E) (q n : ℕ)
    (p : I2.Vsp X.dim →ₗ[ℂ] I2.Vsp X.dim) (s : (Fin 1 → I2.Vsp X.dim) → ℂ) (hs : Differentiable ℂ s)
    (a : Fin n → I2.Vsp X.dim) : Differentiable ℂ (X.U q a (I2.s0 X p s)) := by
  have hp : Differentiable ℂ p := (LinearMap.toContinuousLinearMap p).differentiable
  have h1 : Differentiable ℂ (I2.s0 X (n := n) p s) := by
    unfold I2.s0
    have hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => p (v k) := fun k =>
      hs.comp (differentiable_pi.2 fun _ => hp.comp (differentiable_apply k))
    exact fun v => (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (hk k v).hasFDerivAt).differentiableAt
  have h2 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v a := by
    unfold I2.HC I2.Hf
    refine Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun i _ => Differentiable.mul_const ?_ _
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp (differentiable_apply k)
  unfold I2.PT.U
  exact (((h2.const_mul _).sub_const _).cexp).mul (h1.comp (differentiable_id.sub_const a))

/- English proof (translation)
Introduce `E _ _ _ X α β M n hβ hα s hs a Io P u sc κ hu hκ`. Establish `hbar : ∀ τ : E →+* ℂ, τ (β : E) = (starRingEnd ℂ) (τ (α : E))` using `fun τ => by`. Rewrite using `[hβ, IsCMField.complexEmbedding_complexConj]`. Establish `h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M`. Introduce `τ`.

Use `congrArg (fun a : 𝓞 E => τ (a : E)) hα` as an intermediate fact. Simplify using `using this`. Establish `h'' : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M`. Introduce `τ`. Rewrite using `[← h' τ, hbar, Complex.conj_conj, mul_comm]`.

Establish `hfun : X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) = (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) ∘ colMap β n`. Use function extensionality and compare the values at `v`. Rewrite using `[translate_eq_comp X α β M n h'' h']`. Both sides reduce to the same expression. Rewrite using `[hfun]`.

Use `polyDeriv_comp_clm P u _ ?_ (colMap β n) sc (fun l => funext fun b => hu l b) κ hκ` and prove the remaining obligations. Conclude with `GlobalTheory.SCV.contDiff_of_differentiable (differentiable_translate X M n (vspActL α) s hs _) ⊤`.
-/
theorem polyDeriv_levelSq_eq_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ), (β : E) = IsCMField.complexConj E (α : E) → α * β = (M : 𝓞 E) → ∀ s : (Fin 1 → I2.Vsp X.dim) → ℂ, Differentiable ℂ s → ∀ (a : Fin n → I2.Vsp X.dim) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → I2.Vsp X.dim) (sc : Io → ℂ) (κ : ℂ), (∀ ℓ b, I2.act β (u ℓ b) = sc ℓ • u ℓ b) → (∀ m ∈ P.support, (m.prod fun ℓ e => sc ℓ ^ e) = κ) → I2.polyDeriv P u (X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s)) 0 = κ * I2.polyDeriv P u (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) 0 := by
  intro E _ _ _ X α β M n hβ hα s hs a Io P u sc κ hu hκ
  have hbar : ∀ τ : E →+* ℂ, τ (β : E) = (starRingEnd ℂ) (τ (α : E)) := fun τ => by
    rw [hβ, IsCMField.complexEmbedding_complexConj]
  have h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M := by
    intro τ
    have := congrArg (fun a : 𝓞 E => τ (a : E)) hα
    simpa using this
  have h'' : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M := by
    intro τ
    rw [← h' τ, hbar, Complex.conj_conj, mul_comm]
  have hfun : X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) =
      (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) ∘ colMap β n := by
    funext v
    rw [translate_eq_comp X α β M n h'' h']
    rfl
  rw [hfun]
  refine polyDeriv_comp_clm P u _ ?_ (colMap β n) sc (fun l => funext fun b => hu l b) κ hκ
  exact GlobalTheory.SCV.contDiff_of_differentiable (differentiable_translate X M n (vspActL α) s hs _) ⊤

end GlobalTheory.AlphaChain
