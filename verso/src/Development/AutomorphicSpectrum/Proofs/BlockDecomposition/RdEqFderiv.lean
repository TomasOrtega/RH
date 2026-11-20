import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZJoint

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Establish `hc : Continuous (fun g : Mat n => g.det)` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne.preimage hc`.
-/
theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

/- English proof (translation)
The claim follows from `isOpen_univ.prod (isOpen_GLs n)`.
-/
theorem isOpen_dom (n : ℕ) : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) :=
  isOpen_univ.prod (isOpen_GLs n)

def Pres (Φ : (Mat n → V) → (Mat n → V)) : Prop :=
  ∀ U : ℝ → Mat n → V, ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
    ContDiffOn ℝ ∞ (Function.uncurry fun t => Φ (U t)) (Set.univ ×ˢ GLs n)

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (Function.uncurry U) (t, g)` using `(hU.contDiffAt ((isOpen_dom n).mem_nhds ⟨Set.mem_univ _, hg⟩)).differentiableAt (by simp)`. Establish `hi : HasFDerivAt (fun x : Mat n => (t, x)) (ContinuousLinearMap.inr ℝ ℝ (Mat n)) g` using `hasFDerivAt_prodMk_right t g`. Establish `h2 : HasFDerivAt (U t) ((fderiv ℝ (Function.uncurry U) (t, g)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) g` using `HasFDerivAt.comp g (f := fun x : Mat n => (t, x)) (g := Function.uncurry U) hd.hasFDerivAt hi`. Simplify using `[Rd, h2.fderiv]`.
-/
theorem rd_eq_fderiv (U : ℝ → Mat n → V)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) {t : ℝ} {g : Mat n}
    (hg : g ∈ GLs n) (X : Mat n) :
    Rd X (U t) g = fderiv ℝ (Function.uncurry U) (t, g) ((0 : ℝ), g * X) := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, g) :=
    (hU.contDiffAt ((isOpen_dom n).mem_nhds ⟨Set.mem_univ _, hg⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun x : Mat n => (t, x)) (ContinuousLinearMap.inr ℝ ℝ (Mat n)) g :=
    hasFDerivAt_prodMk_right t g
  have h2 : HasFDerivAt (U t)
      ((fderiv ℝ (Function.uncurry U) (t, g)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) g :=
    HasFDerivAt.comp g (f := fun x : Mat n => (t, x)) (g := Function.uncurry U) hd.hasFDerivAt hi
  simp [Rd, h2.fderiv]

/- English proof (translation)
Introduce `U hU`. Establish `h1` using `hU.fderiv_of_isOpen (m := ∞) (isOpen_dom n) (by simp)`. Set `L : Mat n →ₗ[ℝ] Mat n` to `LinearMap.mulRight ℝ X`. Establish `hL : ContDiff ℝ ∞ (fun x : Mat n => x * X)` using `(L.toContinuousLinearMap).contDiff`. Establish `hl : ContDiff ℝ ∞ (fun p : ℝ × Mat n => ((0 : ℝ), p.2 * X))` using `contDiff_const.prodMk (hL.comp contDiff_snd)`.

Use `(h1.clm_apply hl.contDiffOn).congr ?_` and prove the remaining obligations. Introduce and unpack `⟨t, g⟩ ⟨-, hg⟩`. Conclude with `rd_eq_fderiv U hU hg X`.
-/
theorem pres_Rd (X : Mat n) : Pres (V := V) (Rd X) := by
  intro U hU
  have h1 := hU.fderiv_of_isOpen (m := ∞) (isOpen_dom n) (by simp)
  let L : Mat n →ₗ[ℝ] Mat n := LinearMap.mulRight ℝ X
  have hL : ContDiff ℝ ∞ (fun x : Mat n => x * X) := (L.toContinuousLinearMap).contDiff
  have hl : ContDiff ℝ ∞ (fun p : ℝ × Mat n => ((0 : ℝ), p.2 * X)) :=
    contDiff_const.prodMk (hL.comp contDiff_snd)
  refine (h1.clm_apply hl.contDiffOn).congr ?_
  rintro ⟨t, g⟩ ⟨-, hg⟩
  exact rd_eq_fderiv U hU hg X

/- English proof (translation)
Introduce `U hU` and use `(h U hU).add (k U hU)`.
-/
theorem Pres.add {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Pres Φ) (k : Pres Ψ) :
    Pres (fun f => Φ f + Ψ f) :=
  fun U hU => (h U hU).add (k U hU)

/- English proof (translation)
Introduce `U hU` and use `(h U hU).const_smul c`.
-/
theorem Pres.smul {Φ : (Mat n → V) → (Mat n → V)} (c : ℂ) (h : Pres Φ) :
    Pres (fun f => c • Φ f) :=
  fun U hU => (h U hU).const_smul c

/- English proof (translation)
Introduce `U hU` and use `h (fun t => Ψ (U t)) (k U hU)`.
-/
theorem Pres.comp {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Pres Φ) (k : Pres Ψ) :
    Pres (fun f => Φ (Ψ f)) :=
  fun U hU => h (fun t => Ψ (U t)) (k U hU)

/- English proof (translation)
Introduce `U hU`. Establish `e : (Function.uncurry fun t => ∑ i ∈ s, Φ i (U t)) = fun p => ∑ i ∈ s, (Function.uncurry fun t => Φ i (U t)) p`. Use function extensionality and compare the values at `p`. Simplify using `[Function.uncurry, Finset.sum_apply]`. Rewrite using `[e]`.

Conclude with `ContDiffOn.sum fun i _ => h i U hU`.
-/
theorem pres_sum {ι : Type} (s : Finset ι) (Φ : ι → (Mat n → V) → (Mat n → V))
    (h : ∀ i, Pres (Φ i)) : Pres (fun f => ∑ i ∈ s, Φ i f) := by
  intro U hU
  have e : (Function.uncurry fun t => ∑ i ∈ s, Φ i (U t)) =
      fun p => ∑ i ∈ s, (Function.uncurry fun t => Φ i (U t)) p := by
    funext p
    simp [Function.uncurry, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun i _ => h i U hU

/- English proof (translation)
The claim follows from `Pres.smul (1 / 2 : ℂ) ((pres_Rd _).add (Pres.smul _ (pres_Rd _)))`.
-/
theorem pres_Eu (s : Bool) (a b : Fin n) : Pres (V := V) (Eu s a b) :=
  Pres.smul (1 / 2 : ℂ) ((pres_Rd _).add (Pres.smul _ (pres_Rd _)))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b U hU`. Distinguish the cases in `hab : a = b`. Simplify `hU` using `[Epow, hab]`.

Establish `e : (Function.uncurry fun t => Epow (V` using `V) s 0 a b (U t)) = fun _ => 0 := by`. Use function extensionality and compare the values at `p`. Simplify using `[Epow, hab, Function.uncurry]`. Rewrite using `[e]`. Conclude with `contDiffOn_const`.

Consider the case `succ m ih`. Introduce `a b`. Conclude with `pres_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f)) fun c => (pres_Eu s a c).comp (ih c b)`.
-/
theorem pres_Epow (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Pres (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b U hU
    by_cases hab : a = b
    · simpa [Epow, hab] using hU
    · have e : (Function.uncurry fun t => Epow (V := V) s 0 a b (U t)) = fun _ => 0 := by
        funext p
        simp [Epow, hab, Function.uncurry]
      rw [e]
      exact contDiffOn_const
  | succ m ih =>
    intro a b
    exact pres_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f))
      fun c => (pres_Eu s a c).comp (ih c b)

/- English proof (translation)
The claim follows from `pres_sum Finset.univ (fun a f => Epow s m a a f) fun a => pres_Epow s m a a`.
-/
theorem pres_gel (s : Bool) (m : ℕ) : Pres (V := V) (gel (n := n) s m) :=
  pres_sum Finset.univ (fun a f => Epow s m a a f) fun a => pres_Epow s m a a

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact fun U hU => hU`. Consider the case `cons p w ih => exact (pres_gel p.1 p.2).comp ih`.
-/
theorem pres_zOp (w : List (Bool × ℕ)) : Pres (V := V) (zOp (n := n) w) := by
  induction w with
  | nil => exact fun U hU => hU
  | cons p w ih => exact (pres_gel p.1 p.2).comp ih

/- English proof (translation)
The claim follows from `pres_zOp w U h`.
-/
theorem zOp_joint (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (U : ℝ → Mat n → V)
    (w : List (Bool × ℕ)) (h : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t => zOp w (U t)) (Set.univ ×ˢ GLs n) :=
  pres_zOp w U h

end GlobalTheory.CompanionTheory.WaveMult.ZJoint
