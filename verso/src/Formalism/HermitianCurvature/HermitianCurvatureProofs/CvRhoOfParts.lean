import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def Xa (k r : ℕ) (c d : Fin (2 * r + k + 1)) : Mat k r := hpart1 (Hpk k r) (Matrix.single c d 1)

def Xb (k r : ℕ) (c d : Fin (2 * r + k + 1)) : Mat k r := hpart2 (Hpk k r) (Matrix.single c d 1)

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _`.
-/
theorem Xa_lie (c d : Fin (2 * r + k + 1)) : inLie k r (Xa k r c d) := Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _`.
-/
theorem Xb_lie (c d : Fin (2 * r + k + 1)) : inLie k r (Xb k r c d) := Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _

def EHc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (y : Mat k r) (c d : Fin (2 * r + k + 1))
    (f : Mat k r → E) : Mat k r → E :=
  fun g => RdV (y⁻¹ * Xa k r c d * y) f g + Complex.I • RdV (y⁻¹ * Xb k r c d * y) f g

def CapAdInv : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (y : Mat k r) (u : ℂ) (f : Mat k r → E),
    y ∈ GV k r → CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) f → ∀ h ∈ GV k r,
      qminorOp (EHc k r y) (Q.posL k r 0) (Q.posL k r 0) u f h =
        qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) u f h

section Transport

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem top_apply (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (g : Mat k r) :
    Top Eop u c d f g = (if c = d then u • f g else 0) + Eop c d f g := rfl

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U₁, f₁, hU₁, hg₁, hc₁, he₁⟩` from `hf g₀ hg₀`. Take `⟨U₂, f₂, hU₂, hg₂, hc₂, he₂⟩` from `hS c d m f hf g₀ hg₀`. Distinguish the cases in `hcd : c = d`. Use `⟨U₁ ∩ U₂, fun g => u • f₁ g + f₂ g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hle : ((m : ℕ∞) : WithTop ℕ∞) ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞)`. Conclude with `Nat.le_succ m` after adjusting the coercions. Conclude with `(((hc₁.of_le hle).const_smul u).mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right)`. Introduce `g hg hgG`. Rewrite using `[top_apply, if_pos hcd, he₁ g hg.1 hgG, he₂ g hg.2 hgG]`.

Use `⟨U₂, f₂, hU₂, hg₂, hc₂, ?_⟩` and prove the remaining obligations. Introduce `g hg hgG`. Rewrite using `[top_apply, if_neg hcd, zero_add, he₂ g hg hgG]`.
-/
theorem ckOn_top (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hS : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop c d f))
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    CkOn (m : ℕ∞) (GV k r) (Top Eop u c d f) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁, hU₁, hg₁, hc₁, he₁⟩ := hf g₀ hg₀
  obtain ⟨U₂, f₂, hU₂, hg₂, hc₂, he₂⟩ := hS c d m f hf g₀ hg₀
  by_cases hcd : c = d
  · refine ⟨U₁ ∩ U₂, fun g => u • f₁ g + f₂ g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
    · have hle : ((m : ℕ∞) : WithTop ℕ∞) ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast Nat.le_succ m
      exact (((hc₁.of_le hle).const_smul u).mono Set.inter_subset_left).add
        (hc₂.mono Set.inter_subset_right)
    · intro g hg hgG
      rw [top_apply, if_pos hcd, he₁ g hg.1 hgG, he₂ g hg.2 hgG]
  · refine ⟨U₂, f₂, hU₂, hg₂, hc₂, ?_⟩
    intro g hg hgG
    rw [top_apply, if_neg hcd, zero_add, he₂ g hg hgG]

/- English proof (translation)
Introduce `g hg`. Rewrite using `[top_apply, top_apply, h g hg, hC c d f f₂ h g hg]`.
-/
theorem top_congr (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hC : ∀ c d (f f₂ : Mat k r → E), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (u : ℂ) (c d : Fin (2 * r + k + 1)) {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, f g = f₂ g) :
    ∀ g ∈ GV k r, Top Eop u c d f g = Top Eop u c d f₂ g := by
  intro g hg
  rw [top_apply, top_apply, h g hg, hC c d f f₂ h g hg]

/- English proof (translation)
Proceed by induction on `ts with`. Consider the case `nil`. Introduce `m f hf`. Simplify using `using hf`. Consider the case `cons t ts ih`.

Introduce `m f hf`. Use `show CkOn (m : ℕ∞) (GV k r) (Top Eop t.1 t.2.1 t.2.2 ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) f))`. Apply `ckOn_top Eop hS` to reduce the goal to its premises. Apply `ih (m + 1) f` to reduce the goal to its premises. Establish `e : m + 1 + ts.length = m + (t :: ts).length`.

Simplify using `only [List.length_cons]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `hf`.
-/
theorem ckOn_fold (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hS : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop c d f))
    (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (m : ℕ) (f : Mat k r → E), CkOn ((m + ts.length : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) := by
  induction ts with
  | nil =>
    intro m f hf
    simpa using hf
  | cons t ts ih =>
    intro m f hf
    show CkOn (m : ℕ∞) (GV k r)
      (Top Eop t.1 t.2.1 t.2.2 ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) f))
    apply ckOn_top Eop hS
    apply ih (m + 1) f
    have e : m + 1 + ts.length = m + (t :: ts).length := by
      simp only [List.length_cons]
      omega
    rw [e]
    exact hf

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg, hc, he⟩` from `hf g₀ hg₀`. Conclude with `⟨U, f', hU, hg, hc.of_le (by exact_mod_cast h), he⟩`.
-/
private theorem ckOn_mono_lemma {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {m n : ℕ} (h : n ≤ m)
    {f : Mat k r → F} (hf : CkOn (m : ℕ∞) (GV k r) f) : CkOn (n : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hg, hc.of_le (by exact_mod_cast h), he⟩

/- English proof (translation)
Proceed by induction on `ts with`. Consider the case `nil`. Introduce `f _ g _`. Both sides reduce to the same expression. Consider the case `cons t ts ih`.

Introduce `f hf g hg`. Establish `hfl : CkOn ((ts.length + 1 : ℕ) : ℕ∞) (GV k r) f` using `by simpa using hf`. Establish `hf0 : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f` using `ckOn_mono_lemma (Nat.le_succ _) hfl`. Establish `hY : CkOn ((1 : ℕ) : ℕ∞) (GV k r) ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)` using `ckOn_fold Eop' hS' ts 1 f (by simpa [Nat.add_comm] using hfl)`. Establish `hX` using `ih f hf0`.

Use `show Top Eop t.1 t.2.1 t.2.2 ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) (trn L a b f)) g = trn L a b (Top Eop' t.1 t.2.1 t.2.2 ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)) g`. Rewrite using `[top_apply, hX g hg, hC t.2.1 t.2.2 _ _ hX g hg, hI t.2.1 t.2.2 _ hY g hg]`. Simplify using `only [trn, top_apply]`. Apply the tactic sequence `split_ifs <;> simp [map_add, map_smul]`.
-/
theorem fold_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E'))
    (Eop' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hI : ∀ c d (f : Mat k r → E), CkOn ((1 : ℕ) : ℕ∞) (GV k r) f →
      ∀ g ∈ GV k r, Eop c d (trn L a b f) g = trn L a b (Eop' c d f) g)
    (hC : ∀ c d (f f₂ : Mat k r → E'), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (hS' : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) (Eop' c d f))
    (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (f : Mat k r → E), CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r,
      (ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) (trn L a b f) g =
        trn L a b ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) g := by
  induction ts with
  | nil =>
    intro f _ g _
    rfl
  | cons t ts ih =>
    intro f hf g hg
    have hfl : CkOn ((ts.length + 1 : ℕ) : ℕ∞) (GV k r) f := by simpa using hf
    have hf0 : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f := ckOn_mono_lemma (Nat.le_succ _) hfl
    have hY : CkOn ((1 : ℕ) : ℕ∞) (GV k r)
        ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) :=
      ckOn_fold Eop' hS' ts 1 f (by simpa [Nat.add_comm] using hfl)
    have hX := ih f hf0
    show Top Eop t.1 t.2.1 t.2.2
        ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) (trn L a b f)) g =
      trn L a b (Top Eop' t.1 t.2.1 t.2.2
        ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)) g
    rw [top_apply, hX g hg, hC t.2.1 t.2.2 _ _ hX g hg, hI t.2.1 t.2.2 _ hY g hg]
    simp only [trn, top_apply]
    split_ifs <;> simp [map_add, map_smul]

/- English proof (translation)
Introduce `g hg`. Unfold `qminorOp`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, trn, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `e1 : ∀ (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E')), (List.ofFn fun j : Fin t => Top F (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)) = (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)).map (fun t => Top F t.1 t.2.1 t.2.2)`. Introduce `F`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Establish `e2 : ∀ (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)), (List.ofFn fun j : Fin t => Top F (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)) = (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)).map (fun t => Top F t.1 t.2.1 t.2.2)`.

Introduce `F`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Use `fold_trn L ha hb Eop Eop' hI hC hS' (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)) f (by simpa using hf) g hg` as an intermediate fact.

Simplify `this` using `[trn]`.
-/
theorem qminor_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E'))
    (Eop' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hI : ∀ c d (f : Mat k r → E), CkOn ((1 : ℕ) : ℕ∞) (GV k r) f →
      ∀ g ∈ GV k r, Eop c d (trn L a b f) g = trn L a b (Eop' c d f) g)
    (hC : ∀ c d (f f₂ : Mat k r → E'), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (hS' : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) (Eop' c d f))
    {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Eop p q u (trn L a b f) g = trn L a b (qminorOp Eop' p q u f) g := by
  intro g hg
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, trn, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∀ (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E')),
      (List.ofFn fun j : Fin t => Top F (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)) =
        (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)).map
          (fun t => Top F t.1 t.2.1 t.2.2) := by
    intro F; rw [List.map_ofFn]; rfl
  have e2 : ∀ (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)),
      (List.ofFn fun j : Fin t => Top F (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)) =
        (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)).map
          (fun t => Top F t.1 t.2.1 t.2.2) := by
    intro F; rw [List.map_ofFn]; rfl
  rw [e1, e2]
  have := fold_trn L ha hb Eop Eop' hI hC hS'
    (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)) f (by simpa using hf) g hg
  simpa [trn] using this

end Transport

section Letters

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

/- English proof (translation)
Unfold `Dx`. Simplify using the standard rewrite rules.
-/
theorem dx_false {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : Mat k r) (f : Mat k r → E) :
    RdV X f = Dx (false, X) f := by
  unfold Dx
  simp

/- English proof (translation)
Rewrite using `[← dx_false, ← dx_false]`. Both sides reduce to the same expression.
-/
theorem EH_eq (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) :
    Q.EH k r c d f = fun g => Dx (false, Xa k r c d) f g + Complex.I • Dx (false, Xb k r c d) f g := by
  rw [← dx_false, ← dx_false]; rfl

/- English proof (translation)
Unfold `EHc`. Simplify using `only [dx_false]`.
-/
theorem EHc_eq (y : Mat k r) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) :
    EHc k r y c d f = fun g => Dx (false, y⁻¹ * Xa k r c d * y) f g +
      Complex.I • Dx (false, y⁻¹ * Xb k r c d * y) f g := by
  unfold EHc
  simp only [dx_false]

/- English proof (translation)
Introduce `g hg`. Rewrite using `[EH_eq, EH_eq]`. Simplify using `only`. Rewrite using `[Dx_congr (x := (false, Xa k r c d)) (Xa_lie c d) h g hg, Dx_congr (x := (false, Xb k r c d)) (Xb_lie c d) h g hg]`.
-/
theorem EH_congr (c d : Fin (2 * r + k + 1)) (f f₂ : Mat k r → E) (h : ∀ g ∈ GV k r, f g = f₂ g) :
    ∀ g ∈ GV k r, Q.EH k r c d f g = Q.EH k r c d f₂ g := by
  intro g hg
  rw [EH_eq, EH_eq]
  simp only
  rw [Dx_congr (x := (false, Xa k r c d)) (Xa_lie c d) h g hg, Dx_congr (x := (false, Xb k r c d)) (Xb_lie c d) h g hg]

/- English proof (translation)
Rewrite using `[EH_eq]`. Establish `hf' : CkOn ((m : ℕ∞) + 1) (GV k r) f` using `by exact_mod_cast hf`. Conclude with `CkOn_add (CkOn_Dx (x := (false, Xa k r c d)) (Xa_lie c d) hf') (CkOn_smul _ (CkOn_Dx (x := (false, Xb k r c d)) (Xb_lie c d) hf'))`.
-/
theorem EH_ck (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (Q.EH k r c d f) := by
  rw [EH_eq]
  have hf' : CkOn ((m : ℕ∞) + 1) (GV k r) f := by exact_mod_cast hf
  exact CkOn_add (CkOn_Dx (x := (false, Xa k r c d)) (Xa_lie c d) hf')
    (CkOn_smul _ (CkOn_Dx (x := (false, Xb k r c d)) (Xb_lie c d) hf'))

/- English proof (translation)
Rewrite using `[EHc_eq]`. Establish `hf' : CkOn ((m : ℕ∞) + 1) (GV k r) f` using `by exact_mod_cast hf`. Conclude with `CkOn_add (CkOn_Dx (x := (false, _)) (lie_conj (Xa_lie c d) hy) hf') (CkOn_smul _ (CkOn_Dx (x := (false, _)) (lie_conj (Xb_lie c d) hy) hf'))`.
-/
theorem EHc_ck {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (EHc k r y c d f) := by
  rw [EHc_eq]
  have hf' : CkOn ((m : ℕ∞) + 1) (GV k r) f := by exact_mod_cast hf
  exact CkOn_add (CkOn_Dx (x := (false, _)) (lie_conj (Xa_lie c d) hy) hf')
    (CkOn_smul _ (CkOn_Dx (x := (false, _)) (lie_conj (Xb_lie c d) hy) hf'))

/- English proof (translation)
Introduce `g hg`. Establish `hf1 : CkOn 1 (GV k r) f` using `by exact_mod_cast hf`. Rewrite using `[EH_eq, EHc_eq]`. Simplify using `only`. Rewrite using `[Dx_trn L ha hb (X := Xa k r c d) (Xa_lie c d) hf1 g hg, Dx_trn L ha hb (X := Xb k r c d) (Xb_lie c d) hf1 g hg]`.

Simplify using `only [trn, map_add, map_smul]`.
-/
theorem EH_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, Q.EH k r c d (trn L a b f) g = trn L a b (EHc k r b c d f) g := by
  intro g hg
  have hf1 : CkOn 1 (GV k r) f := by exact_mod_cast hf
  rw [EH_eq, EHc_eq]
  simp only
  rw [Dx_trn L ha hb (X := Xa k r c d) (Xa_lie c d) hf1 g hg, Dx_trn L ha hb (X := Xb k r c d) (Xb_lie c d) hf1 g hg]
  simp only [trn, map_add, map_smul]

/- English proof (translation)
Rewrite using `[EHc_eq, EH_eq]`. Simplify using `only [inv_one, one_mul, mul_one]`.
-/
theorem EHc_one (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) : EHc k r 1 c d f = Q.EH k r c d f := by
  rw [EHc_eq, EH_eq]
  simp only [inv_one, one_mul, mul_one]

end Letters

/- English proof (translation)
Introduce `k r E _ _ Y f _ y _ g _`. Unfold `Q.CV Q.capL`. Conclude with `congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E (2 * r + k + 1) _ (Hpk k r) f (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) y) g`.
-/
theorem cvLeft : JF.CVLeft := by
  intro k r E _ _ Y f _ y _ g _
  unfold Q.CV Q.capL
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E (2 * r + k + 1) _ (Hpk k r) f (Q.posL k r 0) (Q.posL k r 0)
    (Q.uC k r 0 Y) y) g

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [trn, one_mul, mul_one]`.
-/
theorem trn_one_one {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (L : E →L[ℂ] E') (f : Mat k r → E) : trn L 1 1 f = fun x => L (f x) := by
  funext x
  simp only [trn, one_mul, mul_one]

/- English proof (translation)
Introduce `k r E E' _ _ _ _ Y Φ f hf g hg`. Establish `h1` using `qminor_trn (k := k) (r := r) Φ gv_one gv_one (Q.EH k r) (Q.EH k r) (fun c d f hf => by`. Introduce `g hg`. Rewrite using `[EH_trn Φ gv_one gv_one c d f hf g hg, EHc_one])`. Use the proof step `(fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EH_ck c d m f hf)`.

Use the proof step `(Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f (by simpa [Q.mdim] using hf) g hg`. Rewrite `h1` using `[trn_one_one, trn_one_one]`. Conclude with `h1`.
-/
theorem cvPost : JF.CVPost := by
  intro k r E E' _ _ _ _ Y Φ f hf g hg
  have h1 := qminor_trn (k := k) (r := r) Φ gv_one gv_one (Q.EH k r) (Q.EH k r)
    (fun c d f hf => by
      intro g hg
      rw [EH_trn Φ gv_one gv_one c d f hf g hg, EHc_one])
    (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EH_ck c d m f hf)
    (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f (by simpa [Q.mdim] using hf) g hg
  rw [trn_one_one, trn_one_one] at h1
  exact h1

/- English proof (translation)
Introduce `k r E _ _ Y f hf y hy g hg`. Establish `h1` using `qminor_trn (k := k) (r := r) (ContinuousLinearMap.id ℂ E) gv_one hy (Q.EH k r) (EHc k r y) (fun c d f hf => EH_trn _ gv_one hy c d f hf) (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EHc_ck hy c d m f hf) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f (by simpa [Q.md …`. Establish `e : trn (ContinuousLinearMap.id ℂ E) 1 y f = fun x => f (x * y)`. Use function extensionality and compare the values at `x`. Simplify using `[trn]`.

Rewrite `h1` using `[e]`. Unfold `Q.CV Q.capL`. Rewrite using `[h1]`. Simplify using `only [trn, ContinuousLinearMap.id_apply, Matrix.one_mul]`. Conclude with `hA k r E y _ f hy hf (g * y) (gv_mul hg hy)`.
-/
theorem cvRight_of (hA : CapAdInv) : JF.CVRight := by
  intro k r E _ _ Y f hf y hy g hg
  have h1 := qminor_trn (k := k) (r := r) (ContinuousLinearMap.id ℂ E) gv_one hy (Q.EH k r) (EHc k r y)
    (fun c d f hf => EH_trn _ gv_one hy c d f hf)
    (fun c d f f₂ h => EH_congr c d f f₂ h) (fun c d m f hf => EHc_ck hy c d m f hf)
    (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f (by simpa [Q.mdim] using hf) g hg
  have e : trn (ContinuousLinearMap.id ℂ E) 1 y f = fun x => f (x * y) := by
    funext x; simp [trn]
  rw [e] at h1
  unfold Q.CV Q.capL
  rw [h1]
  simp only [trn, ContinuousLinearMap.id_apply, Matrix.one_mul]
  exact hA k r E y _ f hy hf (g * y) (gv_mul hg hy)

def Lq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (p : SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show (D.π (Matrix.of p.1.1)).comp ((F (sgs p x)).comp (D.π' (Matrix.of p.2.1)⁻¹)) = (D.π (Matrix.of p.1.1)).comp ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))).comp (D.π' (Matrix.of p.2.1)⁻¹))`. Simplify using `only [sgs, Matrix.mul_assoc]`.
-/
theorem rho_eq_trn' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    rho D p F = trn (Lq D p) ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹) (Matrix.of p.2.2 * Matrix.of p.2.1) F := by
  funext x
  show (D.π (Matrix.of p.1.1)).comp ((F (sgs p x)).comp (D.π' (Matrix.of p.2.1)⁻¹)) =
    (D.π (Matrix.of p.1.1)).comp
      ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))).comp
        (D.π' (Matrix.of p.2.1)⁻¹))
  simp only [sgs, Matrix.mul_assoc]

/- English proof (translation)
Introduce `hL hR hP k r Wp Wq _ _ _ _ D Y f p hp hf g hg`. Take `⟨h1, h2, h3, h4⟩` from `hp`. Establish `ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r` using `gv_mul (gv_inv h1.1) (gv_inv h2.1)`. Establish `hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r` using `gv_mul h4.1 h3.1`. Use `set a := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹`.

Use `set b := Matrix.of p.2.2 * Matrix.of p.2.1`. Rewrite using `[rho_eq_trn', rho_eq_trn']`. Establish `hf1 : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (fun x => f (a * x * b))`. Use `CkOn_trn (ContinuousLinearMap.id ℂ _) ha hb hf` as an intermediate fact. Establish `e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) a b f = fun x => f (a * x * b)`.

Use function extensionality and compare the values at `x`. Simplify using `[trn]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hf2 : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (fun x => f (x * b))`. Use `CkOn_trn (ContinuousLinearMap.id ℂ _) gv_one hb hf` as an intermediate fact.

Establish `e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) 1 b f = fun x => f (x * b)`. Use function extensionality and compare the values at `x`. Simplify using `[trn]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `e1 : trn (Lq D p) a b f = fun x => Lq D p ((fun x => f (a * x * b)) x)` using `rfl`.

Rewrite using `[e1, hP k r _ _ Y (Lq D p) _ hf1 g hg]`. Establish `e2 : (fun x => f (a * x * b)) = fun x => (fun x => f (x * b)) (a * x)`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[e2, hL k r _ Y _ hf2 a ha g hg, hR k r _ Y f hf b hb (a * g) (gv_mul ha hg)]`.

Both sides reduce to the same expression.
-/
theorem cvRhoOfParts : JF.CVRhoOfParts := by
  intro hL hR hP k r Wp Wq _ _ _ _ D Y f p hp hf g hg
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    gv_mul (gv_inv h1.1) (gv_inv h2.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := gv_mul h4.1 h3.1
  set a := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹
  set b := Matrix.of p.2.2 * Matrix.of p.2.1
  rw [rho_eq_trn', rho_eq_trn']
  have hf1 : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (fun x => f (a * x * b)) := by
    have := CkOn_trn (ContinuousLinearMap.id ℂ _) ha hb hf
    have e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) a b f = fun x => f (a * x * b) := by
      funext x; simp [trn]
    rwa [e] at this
  have hf2 : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (fun x => f (x * b)) := by
    have := CkOn_trn (ContinuousLinearMap.id ℂ _) gv_one hb hf
    have e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) 1 b f = fun x => f (x * b) := by
      funext x; simp [trn]
    rwa [e] at this
  have e1 : trn (Lq D p) a b f = fun x => Lq D p ((fun x => f (a * x * b)) x) := rfl
  rw [e1, hP k r _ _ Y (Lq D p) _ hf1 g hg]
  have e2 : (fun x => f (a * x * b)) = fun x => (fun x => f (x * b)) (a * x) := by
    funext x; rfl
  rw [e2, hL k r _ Y _ hf2 a ha g hg, hR k r _ Y f hf b hb (a * g) (gv_mul ha hg)]
  rfl

/- English proof (translation)
The claim follows from `cvRhoOfParts cvLeft (cvRight_of hA) cvPost`.
-/
theorem cvRho_of (hA : CapAdInv) : JF.CVRho := cvRhoOfParts cvLeft (cvRight_of hA) cvPost

end Formalism.FourierDecayAlt.P.JFxB
