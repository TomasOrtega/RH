import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.GelfandEvenSmoothness.GelfEven

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveWords

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Mult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `hc : Continuous (fun g : Mat n => g.det)` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne_fun hc continuous_const`.
-/
theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun hc continuous_const

section Good

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Good (T : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ f, ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (T f) (GLs n)) ∧
  (∀ (f h : Mat n → V) (a b : ℂ), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) →
    ∀ x ∈ GLs n, T (fun y => a • f y + b • h y) x = a • T f x + b • T h x) ∧
  (∀ f f', Set.EqOn f f' (GLs n) → Set.EqOn (T f) (T f') (GLs n))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ h => h, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ h => h⟩`.
-/
theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ h => h⟩

/- English proof (translation)
Use `⟨fun _ _ => contDiffOn_const, fun _ _ a b _ _ x _ => by simp, fun _ _ _ _ _ => rfl⟩` and prove the remaining obligations.
-/
theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun _ _ => contDiffOn_const, fun _ _ a b _ _ x _ => by simp, fun _ _ _ _ _ => rfl⟩

/- English proof (translation)
Use `⟨fun f hf => ((hR n).1 V f hf).1 X, ?_, ?_⟩` and prove the remaining obligations. Introduce `f h a b hf hh x hx`. Establish `hn : GLs n ∈ nhds x` using `(isOpen_GLs n).mem_nhds hx`. Establish `df : DifferentiableAt ℝ f x` using `(hf.contDiffAt hn).differentiableAt (by simp)`. Establish `dh : DifferentiableAt ℝ h x` using `(hh.contDiffAt hn).differentiableAt (by simp)`.

Establish `key : HasFDerivAt (fun y => a • f y + b • h y) (a • fderiv ℝ f x + b • fderiv ℝ h x) x` using `(df.hasFDerivAt.const_smul a).add (dh.hasFDerivAt.const_smul b)`. Simplify using `only [Rd]`. Rewrite using `[key.fderiv]`. Simplify using the standard rewrite rules. Introduce `f f' hE x hx`.

Establish `hn : GLs n ∈ nhds x` using `(isOpen_GLs n).mem_nhds hx`. Establish `: f =ᶠ[nhds x] f'` using `Filter.eventuallyEq_of_mem hn hE`. Simplify using `only [Rd]`. Rewrite using `[this.fderiv_eq]`.
-/
theorem good_Rd (hR : RCalc) (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun f hf => ((hR n).1 V f hf).1 X, ?_, ?_⟩
  · intro f h a b hf hh x hx
    have hn : GLs n ∈ nhds x := (isOpen_GLs n).mem_nhds hx
    have df : DifferentiableAt ℝ f x := (hf.contDiffAt hn).differentiableAt (by simp)
    have dh : DifferentiableAt ℝ h x := (hh.contDiffAt hn).differentiableAt (by simp)
    have key : HasFDerivAt (fun y => a • f y + b • h y)
        (a • fderiv ℝ f x + b • fderiv ℝ h x) x :=
      (df.hasFDerivAt.const_smul a).add (dh.hasFDerivAt.const_smul b)
    simp only [Rd]
    rw [key.fderiv]
    simp
  · intro f f' hE x hx
    have hn : GLs n ∈ nhds x := (isOpen_GLs n).mem_nhds hx
    have : f =ᶠ[nhds x] f' := Filter.eventuallyEq_of_mem hn hE
    simp only [Rd]
    rw [this.fderiv_eq]

/- English proof (translation)
Use `⟨fun f hf => hT.1 _ (hT'.1 f hf), ?_, fun f f' hE => hT.2.2 _ _ (hT'.2.2 f f' hE)⟩` and prove the remaining obligations. Introduce `f h a b hf hh x hx`. Establish `e : Set.EqOn (T' (fun y => a • f y + b • h y)) (fun y => a • T' f y + b • T' h y) (GLs n)` using `fun y hy => hT'.2.1 f h a b hf hh y hy`. Use `beta_reduce`. Rewrite using `[hT.2.2 _ _ e hx]`.

Conclude with `hT.2.1 _ _ a b (hT'.1 f hf) (hT'.1 h hh) x hx`.
-/
theorem good_comp {T T' : (Mat n → V) → (Mat n → V)} (hT : Good T) (hT' : Good T') :
    Good (fun f => T (T' f)) := by
  refine ⟨fun f hf => hT.1 _ (hT'.1 f hf), ?_, fun f f' hE => hT.2.2 _ _ (hT'.2.2 f f' hE)⟩
  intro f h a b hf hh x hx
  have e : Set.EqOn (T' (fun y => a • f y + b • h y)) (fun y => a • T' f y + b • T' h y) (GLs n) :=
    fun y hy => hT'.2.1 f h a b hf hh y hy
  beta_reduce
  rw [hT.2.2 _ _ e hx]
  exact hT.2.1 _ _ a b (hT'.1 f hf) (hT'.1 h hh) x hx

/- English proof (translation)
Use `⟨fun f hf => (hT.1 f hf).add (hT'.1 f hf), ?_, ?_⟩` and prove the remaining obligations. Introduce `f h a b hf hh x hx`. Simplify using `only [Pi.add_apply]`. Rewrite using `[hT.2.1 f h a b hf hh x hx, hT'.2.1 f h a b hf hh x hx]`. Use `module`.

Introduce `f f' hE x hx`. Simplify using `only [Pi.add_apply]`. Rewrite using `[hT.2.2 f f' hE hx, hT'.2.2 f f' hE hx]`.
-/
theorem good_add {T T' : (Mat n → V) → (Mat n → V)} (hT : Good T) (hT' : Good T') :
    Good (fun f => T f + T' f) := by
  refine ⟨fun f hf => (hT.1 f hf).add (hT'.1 f hf), ?_, ?_⟩
  · intro f h a b hf hh x hx
    simp only [Pi.add_apply]
    rw [hT.2.1 f h a b hf hh x hx, hT'.2.1 f h a b hf hh x hx]
    module
  · intro f f' hE x hx
    simp only [Pi.add_apply]
    rw [hT.2.2 f f' hE hx, hT'.2.2 f f' hE hx]

/- English proof (translation)
Use `⟨fun f hf => (hT.1 f hf).const_smul c, ?_, ?_⟩` and prove the remaining obligations. Introduce `f h a b hf hh x hx`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[hT.2.1 f h a b hf hh x hx]`. Use `module`.

Introduce `f f' hE x hx`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[hT.2.2 f f' hE hx]`.
-/
theorem good_smul (c : ℂ) {T : (Mat n → V) → (Mat n → V)} (hT : Good T) :
    Good (fun f => c • T f) := by
  refine ⟨fun f hf => (hT.1 f hf).const_smul c, ?_, ?_⟩
  · intro f h a b hf hh x hx
    simp only [Pi.smul_apply]
    rw [hT.2.1 f h a b hf hh x hx]
    module
  · intro f f' hE x hx
    simp only [Pi.smul_apply]
    rw [hT.2.2 f f' hE hx]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using good_zero`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `good_add (h a) ih`.
-/
theorem good_sum {ι : Type} (s : Finset ι) (T : ι → (Mat n → V) → (Mat n → V))
    (h : ∀ i, Good (T i)) : Good (fun f => ∑ i ∈ s, T i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

/- English proof (translation)
The claim follows from `good_smul (1 / 2 : ℂ) (good_add (good_Rd hR _) (good_smul _ (good_Rd hR _)))`.
-/
theorem good_Eu (hR : RCalc) (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul (1 / 2 : ℂ) (good_add (good_Rd hR _) (good_smul _ (good_Rd hR _)))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b`. Distinguish the cases in `h : a = b`. Establish `e : Epow (n` using `n) (V := V) s 0 a b = fun f => f := by`.

Use function extensionality and compare the values at `f`. Simplify using `[Epow, h]`. Rewrite using `[e]`. Conclude with `good_id`. Establish `e : Epow (n` using `n) (V := V) s 0 a b = fun _ => 0 := by`.

Use function extensionality and compare the values at `f`. Simplify using `[Epow, h]`. Rewrite using `[e]`. Conclude with `good_zero`. Consider the case `succ m ih`.

Introduce `a b`. Conclude with `good_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f)) (fun c => good_comp (good_Eu hR s a c) (ih c b))`.
-/
theorem good_Epow (hR : RCalc) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Good (n := n) (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b
    by_cases h : a = b
    · have e : Epow (n := n) (V := V) s 0 a b = fun f => f := by
        funext f; simp [Epow, h]
      rw [e]; exact good_id
    · have e : Epow (n := n) (V := V) s 0 a b = fun _ => 0 := by
        funext f; simp [Epow, h]
      rw [e]; exact good_zero
  | succ m ih =>
    intro a b
    exact good_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f))
      (fun c => good_comp (good_Eu hR s a c) (ih c b))

/- English proof (translation)
The claim follows from `good_sum Finset.univ (fun a => Epow s m a a) (fun a => good_Epow hR s m a a)`.
-/
theorem good_gel (hR : RCalc) (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ (fun a => Epow s m a a) (fun a => good_Epow hR s m a a)

/- English proof (translation)
The claim follows from `good_smul (2 : ℂ) (good_add (good_gel hR true 2) (good_gel hR false 2))`.
-/
theorem good_Om (hR : RCalc) : Good (n := n) (V := V) Om :=
  good_smul (2 : ℂ) (good_add (good_gel hR true 2) (good_gel hR false 2))

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact good_id`. Consider the case `cons p w ih`. Establish `e : zOp (n` using `n) (V := V) (p :: w) = fun f => gel p.1 p.2 (zOp w f) := rfl`. Rewrite using `[e]`.

Conclude with `good_comp (good_gel hR p.1 p.2) ih`.
-/
theorem good_zOp (hR : RCalc) (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    have e : zOp (n := n) (V := V) (p :: w) = fun f => gel p.1 p.2 (zOp w f) := rfl
    rw [e]
    exact good_comp (good_gel hR p.1 p.2) ih

end Good

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons p w ih => exact (hR n).2.1 E _ ih p.1 p.2`.
-/
theorem zOp_mem_CE (hR : RCalc) (E : KMod n) (w : List (Bool × ℕ)) {f : Mat n → E.V}
    (hf : f ∈ CE E) : zOp w f ∈ CE E := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact (hR n).2.1 E _ ih p.1 p.2

/- English proof (translation)
Use `⟨(good_Om hR).1 f hf.1, ?_⟩` and prove the remaining obligations. Introduce `g hg k`. Establish `h1` using `((hR n).2.1 E f hf true 2).2 g hg k`. Establish `h2` using `((hR n).2.1 E f hf false 2).2 g hg k`. Simplify using `only [Om, Pi.smul_apply, Pi.add_apply, h1, h2, map_add, map_smul]`.
-/
theorem Om_mem_CE (hR : RCalc) (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) : Om f ∈ CE E := by
  refine ⟨(good_Om hR).1 f hf.1, ?_⟩
  intro g hg k
  have h1 := ((hR n).2.1 E f hf true 2).2 g hg k
  have h2 := ((hR n).2.1 E f hf false 2).2 g hg k
  simp only [Om, Pi.smul_apply, Pi.add_apply, h1, h2, map_add, map_smul]

/- English proof (translation)
Introduce `hR n`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `V _ _ w f h a b hf hh`. Conclude with `⟨(good_zOp hR w).1 f hf, (good_Om hR).1 f hf, fun x hx => ⟨(good_zOp hR w).2.1 f h a b hf hh x hx, (good_Om hR).2.1 f h a b hf hh x hx⟩⟩`. Introduce `V _ _ w f f' hE x hx`.

Conclude with `⟨(good_zOp hR w).2.2 f f' hE hx, (good_Om hR).2.2 f f' hE hx⟩`. Introduce `E w f hf`. Conclude with `⟨zOp_mem_CE hR E w hf, Om_mem_CE hR E hf⟩`.
-/
theorem zLin : ZLin := by
  intro hR n
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ w f h a b hf hh
    exact ⟨(good_zOp hR w).1 f hf, (good_Om hR).1 f hf, fun x hx =>
      ⟨(good_zOp hR w).2.1 f h a b hf hh x hx, (good_Om hR).2.1 f h a b hf hh x hx⟩⟩
  · intro V _ _ w f f' hE x hx
    exact ⟨(good_zOp hR w).2.2 f f' hE hx, (good_Om hR).2.2 f f' hE hx⟩
  · intro E w f hf
    exact ⟨zOp_mem_CE hR E w hf, Om_mem_CE hR E hf⟩

end GlobalTheory.CompanionTheory.WaveWords
