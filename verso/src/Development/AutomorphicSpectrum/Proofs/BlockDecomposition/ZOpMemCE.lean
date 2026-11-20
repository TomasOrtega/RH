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
Establish an intermediate fact. A detailed English derivation is pending.
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
Supply the required witnesses or components.
-/
theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ h => h⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations.
-/
theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun _ _ => contDiffOn_const, fun _ _ a b _ _ x _ => by simp, fun _ _ _ _ _ => rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem good_Eu (hR : RCalc) (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul (1 / 2 : ℂ) (good_add (good_Rd hR _) (good_smul _ (good_Rd hR _)))

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem good_gel (hR : RCalc) (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ (fun a => Epow s m a a) (fun a => good_Epow hR s m a a)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem good_Om (hR : RCalc) : Good (n := n) (V := V) Om :=
  good_smul (2 : ℂ) (good_add (good_gel hR true 2) (good_gel hR false 2))

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem zOp_mem_CE (hR : RCalc) (E : KMod n) (w : List (Bool × ℕ)) {f : Mat n → E.V}
    (hf : f ∈ CE E) : zOp w f ∈ CE E := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact (hR n).2.1 E _ ih p.1 p.2

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem Om_mem_CE (hR : RCalc) (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) : Om f ∈ CE E := by
  refine ⟨(good_Om hR).1 f hf.1, ?_⟩
  intro g hg k
  have h1 := ((hR n).2.1 E f hf true 2).2 g hg k
  have h2 := ((hR n).2.1 E f hf false 2).2 g hg k
  simp only [Om, Pi.smul_apply, Pi.add_apply, h1, h2, map_add, map_smul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
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
