import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLStable
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestricStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

section VecGen
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (a n : ℕ)

def vecS : (Fin a → Fin n → K) →ₛₗ[φ] (Fin a → Fin n → L) where
  toFun v := fun b j => φ (v b j)
  map_add' u v := by funext b j; simp
  map_smul' c v := by funext b j; simp

variable {φ a n}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vecS_apply (v : Fin a → Fin n → K) (b : Fin a) (j : Fin n) : vecS φ a n v b j = φ (v b j) := rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hx`.

Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem span_vecS_span (S : Set (Fin a → Fin n → K)) :
    Submodule.span L (vecS φ a n '' (Submodule.span K S : Set (Fin a → Fin n → K))) =
      Submodule.span L (vecS φ a n '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Set `b` to `Module.finBasis K W`. Set `g : Fin (Module.finrank K W) → (Fin a → Fin n → L)` to `fun i => vecS φ a n (b i)`. Establish `hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Establish `h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K)`. Use `congrArg W.subtype (b.sum_repr ⟨w, hw⟩)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Conclude with `this.symm`. Rewrite using `[h, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h1` using `Submodule.finrank_mono hle`. Establish `h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W`.

Use `finrank_range_le_card (R := L) g` as an intermediate fact. Simplify `this` using `[Set.finrank]`. Conclude with `h1.trans h2`.
-/
theorem finrank_span_vecS_le (W : Submodule K (Fin a → Fin n → K)) :
    finrank L (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))) ≤ finrank K W := by
  let b := Module.finBasis K W
  let g : Fin (Module.finrank K W) → (Fin a → Fin n → L) := fun i => vecS φ a n (b i)
  have hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K) := by
      have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
      rw [map_sum] at this
      exact this.symm
    rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W := by
    have := finrank_range_le_card (R := L) g
    simpa [Set.finrank] using this
  exact h1.trans h2

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `u _`. Establish `e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0)`. Use function extensionality and compare the values at `b' j'`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite, mul_one, mul_zero, ite_and]`.

Simplify using `[Finset.sum_ite_eq, Finset.sum_ite_eq']`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`.
-/
theorem span_vecS_top : Submodule.span L (Set.range (vecS φ a n)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0) := by
    funext b' j'
    simp only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite,
      mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/- English proof (translation)
Use `set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))`. Use `set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))`. Establish `hsup : A ⊔ B = ⊤`. Rewrite using `[eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`.

Establish `hv : v ∈ W ⊔ W'` using `by rw [h.sup_eq_top]; trivial`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`. Conclude with `add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩)) (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))`. Establish `h1 : finrank L A ≤ finrank K W` using `finrank_span_vecS_le W`.

Establish `h2 : finrank L B ≤ finrank K W'` using `finrank_span_vecS_le W'`. Establish `h3` using `Submodule.finrank_add_eq_of_isCompl h`. Establish `h4` using `Submodule.finrank_sup_add_finrank_inf_eq A B`. Rewrite `h4` using `[hsup, finrank_top]`. Establish `hK : finrank K (Fin a → Fin n → K) = a * n`.

Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Module.finrank_fin_fun]`. Establish `hL : finrank L (Fin a → Fin n → L) = a * n`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Module.finrank_fin_fun]`.

Establish `hinf : A ⊓ B = ⊥`. Rewrite using `[← Submodule.finrank_eq_zero]`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩`.
-/
theorem isCompl_span_vecS {W W' : Submodule K (Fin a → Fin n → K)} (h : IsCompl W W') :
    IsCompl (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))))
      (Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))) := by
  set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))
  set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))
  have h1 : finrank L A ≤ finrank K W := finrank_span_vecS_le W
  have h2 : finrank L B ≤ finrank K W' := finrank_span_vecS_le W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top] at h4
  have hK : finrank K (Fin a → Fin n → K) = a * n := by
    rw [Module.finrank_pi_fintype]; simp [Module.finrank_fin_fun]
  have hL : finrank L (Fin a → Fin n → L) = a * n := by
    rw [Module.finrank_pi_fintype]; simp [Module.finrank_fin_fun]
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; omega
  exact ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩

end VecGen

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩`. Establish `hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV '' (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i)))`. Rewrite using `[span_vecS_span]`. Both sides reduce to the same expression. Use `⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl, Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩` and prove the remaining obligations.

Introduce `g u hu`. Establish `hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤ (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap ((sumG i w hw r Xs hr x).ρ g)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈ Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))`.

Rewrite using `[sumG_vecL]`. Conclude with `Submodule.subset_span ⟨_, hC _ v hv, rfl⟩`. Conclude with `hle hu`. Establish `key : IsCompl (spanL i w hw Y) (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))))`. Rewrite using `[hspan]`.

Conclude with `isCompl_span_vecS hYC`. Use `key using 1` and compare the differences between its conclusion and the goal. Conclude with `Submodule.range_subtype _`.
-/
theorem isSummandTw_XG : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y),
    (∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧
    IsCompl (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))) C) →
    IsSummandTw i w hw r Xs (XG i w hw r Xs hr x Y hst) := by
  intro D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩
  have hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV ''
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i))) := by
    rw [span_vecS_span]; rfl
  refine ⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl,
    Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩
  · intro g u hu
    have hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap
          ((sumG i w hw r Xs hr x).ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈
        Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))
      rw [sumG_vecL]
      exact Submodule.subset_span ⟨_, hC _ v hv, rfl⟩
    exact hle hu
  · have key : IsCompl (spanL i w hw Y)
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))) := by
      rw [hspan]
      exact isCompl_span_vecS hYC
    convert key using 1
    exact Submodule.range_subtype _

end GlobalTheory.Pass.LocDual.OneX

end
