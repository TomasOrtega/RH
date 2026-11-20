import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup in
/- English proof (translation)
Simplify using `[ps, qA]`.
-/
theorem ps_zero : ps W 0 = W.π₀ + lA W := by
  simp [ps, qA]

open Formalism.MainNotions.ArcLiftingSetup in
/- English proof (translation)
Simplify using `only [ps, pow_succ', AlgHom.mul_apply]`.
-/
theorem ps_succ (s : ℕ) : ps W (s + 1) = W.φA (ps W s) := by
  simp only [ps, pow_succ', AlgHom.mul_apply]

/- English proof (translation)
Unfold `Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs`. Rewrite using `[show a - ((s + 1 : ℕ) : ZMod n) = a - 1 - (s : ZMod n) by push_cast; ring, show e + 1 - (s + 1) = e - s by omega]`.
-/
theorem hs_succ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (a : ZMod n) (e s : ℕ) :
    A.Hs a (e + 1) (s + 1) = A.Hs (a - 1) e s := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  rw [show a - ((s + 1 : ℕ) : ZMod n) = a - 1 - (s : ZMod n) by push_cast; ring,
    show e + 1 - (s + 1) = e - s by omega]

def LamUp (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) : LetA O n :=
  W.φA (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e)

/- English proof (translation)
Unfold `LamUp`. Use `conv_lhs => unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂`. Rewrite using `[Finset.prod_range_succ', mul_comm]`. Use `congr 1`. Unfold `Formalism.MainNotions.ArcLiftingSetup.abelian₂`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← ps_succ, hs_succ]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_succ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) :
    Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) =
      Formalism.MainNotions.ArcLiftingSetup.ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 * LamUp W A c' e := by
  unfold LamUp
  conv_lhs => unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, ← ps_succ, hs_succ]
  congr 2
  push_cast; ring

def Cop (x z : LetA O n) : Prop :=
  ∃ m : ℕ, ∃ r ∈ W.AΔ, ∃ s ∈ W.AΔ, Formalism.MainNotions.ArcLiftingSetup.lA W ^ m = r * x + s * z

/- English proof (translation)
The claim follows from `W.AΔ.pow_mem (W.AΔ.natCast_mem _) m`.
-/
theorem lA_mem (m : ℕ) : Formalism.MainNotions.ArcLiftingSetup.lA W ^ m ∈ W.AΔ :=
  W.AΔ.pow_mem (W.AΔ.natCast_mem _) m

/- English proof (translation)
Take `⟨m, r, hr, s, hs, e⟩` from `h`. Conclude with `⟨m, s, hs, r, hr, by rw [e]; ring⟩`.
-/
theorem cop_symm {x z : LetA O n} (h : Cop W x z) : Cop W z x := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, s, hs, r, hr, by rw [e]; ring⟩

/- English proof (translation)
Take `⟨a, r, hr, s, hs, e1⟩` from `h1`. Take `⟨b, r', hr', s', hs', e2⟩` from `h2`. Use `⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩` and prove the remaining obligations. Establish `hy : r' * y ∈ W.AΔ`. Establish `: r' * y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ b - s' * z` using `by rw [e2]; ring`.

Rewrite using `[this]`. Conclude with `W.AΔ.sub_mem (lA_mem W b) (W.AΔ.mul_mem hs' hz)`. Use `W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_) (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `W.AΔ.mul_mem hs hy`.

Rewrite using `[pow_add, e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cop_mul {x y z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h1 : Cop W x z) (h2 : Cop W y z) : Cop W (x * y) z := by
  obtain ⟨a, r, hr, s, hs, e1⟩ := h1
  obtain ⟨b, r', hr', s', hs', e2⟩ := h2
  refine ⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩
  · have hy : r' * y ∈ W.AΔ := by
      have : r' * y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ b - s' * z := by rw [e2]; ring
      rw [this]; exact W.AΔ.sub_mem (lA_mem W b) (W.AΔ.mul_mem hs' hz)
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_)
      (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)
    rw [mul_assoc]; exact W.AΔ.mul_mem hs hy
  · rw [pow_add, e1, e2]; ring

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩`. Consider the case `succ N ih => rw [pow_succ]`. Conclude with `cop_mul W (W.AΔ.pow_mem hx N) hz ih h`.
-/
theorem cop_pow {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : Cop W x z) :
    ∀ N : ℕ, Cop W (x ^ N) z := by
  intro N
  induction N with
  | zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih => rw [pow_succ]; exact cop_mul W (W.AΔ.pow_mem hx N) hz ih h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, mul_comm]`. Conclude with `cop_mul W (W.AΔ.prod_mem fun i _ => hx i) hz (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s))`.
-/
theorem cop_prod {ι : Type} (s : Finset ι) (x : ι → LetA O n) {z : LetA O n}
    (hx : ∀ i, x i ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : ∀ i ∈ s, Cop W (x i) z) :
    Cop W (∏ i ∈ s, x i) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact cop_mul W (W.AΔ.prod_mem fun i _ => hx i) hz (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      (h a (Finset.mem_insert_self a s))

/- English proof (translation)
Take `⟨m, r, hr, s, hs, e⟩` from `h`. Conclude with `⟨m, r * x, W.AΔ.mul_mem hr hx, s * z, W.AΔ.mul_mem hs hz, e, ⟨r, hr, mul_comm _ _⟩, ⟨s, hs, mul_comm _ _⟩⟩`.
-/
theorem crt {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : Cop W x z) :
    ∃ m : ℕ, ∃ u₀ ∈ W.AΔ, ∃ u₁ ∈ W.AΔ, Formalism.MainNotions.ArcLiftingSetup.lA W ^ m = u₀ + u₁ ∧
      (∃ r ∈ W.AΔ, u₀ = x * r) ∧ ∃ s ∈ W.AΔ, u₁ = z * s := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, r * x, W.AΔ.mul_mem hr hx, s * z, W.AΔ.mul_mem hs hz, e, ⟨r, hr, mul_comm _ _⟩,
    ⟨s, hs, mul_comm _ _⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, -1, W.AΔ.neg_mem W.AΔ.one_mem, 1, W.AΔ.one_mem, by rw [ps_zero]; ring⟩`.
-/
theorem coprime_uniformizer_first_factor : Cop W W.π₀ (Formalism.MainNotions.ArcLiftingSetup.ps W 0) :=
  ⟨1, -1, W.AΔ.neg_mem W.AΔ.one_mem, 1, W.AΔ.one_mem, by rw [ps_zero]; ring⟩

variable [IsDomain O]

/- English proof (translation)
Take `⟨a, ha⟩` from `Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_qP hR s hs`. Establish `hq : Formalism.MainNotions.WachCoordinates.qP W = Formalism.MainNotions.ArcLiftingSetup.ps W 0`. Rewrite using `[ps_zero]`. Both sides reduce to the same expression. Establish `haΔ : a ∈ W.AΔ`.

Use `Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0) ?_` and prove the remaining obligations. Rewrite using `[← ha]`. Conclude with `Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1`. Establish `e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀` using `Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s`. Use `⟨1, 1, W.AΔ.one_mem, -a, W.AΔ.neg_mem haΔ, ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[hq]`. Take the linear combination `(-1 : LetA O n) * e1 - ha`.
-/
theorem coprime_frobenius_uniformizer_powers (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    Cop W (Formalism.MainNotions.ArcLiftingSetup.ps W s) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) := by
  obtain ⟨a, ha⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_qP hR s hs
  have hq : Formalism.MainNotions.WachCoordinates.qP W = Formalism.MainNotions.ArcLiftingSetup.ps W 0 := by
    rw [ps_zero]; rfl
  have haΔ : a ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
      (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0) ?_
    rw [← ha]; exact Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1
  have e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s
  refine ⟨1, 1, W.AΔ.one_mem, -a, W.AΔ.neg_mem haΔ, ?_⟩
  rw [hq] at ha
  linear_combination (-1 : LetA O n) * e1 - ha

/- English proof (translation)
Establish `hp0Δ : Formalism.MainNotions.ArcLiftingSetup.ps W 0 ∈ W.AΔ` using `Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 0`. Establish `hps : ∀ s, Formalism.MainNotions.ArcLiftingSetup.ps W s ∈ W.AΔ` using `Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1`. Establish `hU : Cop W (LamUp W A c' e) (Formalism.MainNotions.ArcLiftingSetup.ps W 0)`. Unfold `LamUp Formalism.MainNotions.ArcLiftingSetup.abelian₂`. Rewrite using `[map_prod]`.

Use `cop_prod W _ _ (fun s => ?_) hp0Δ fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← ps_succ]`. Conclude with `W.AΔ.pow_mem (hps _) _`. Rewrite using `[map_pow, ← ps_succ]`. Conclude with `cop_pow W (hps _) hp0Δ (coprime_frobenius_uniformizer_powers W hR hp0 (s + 1) (by omega)) _`.

Establish `hUΔ : LamUp W A c' e ∈ W.AΔ` using `Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A _ e)`. Establish `h1 : Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0)` using `cop_mul W hR.1 hp0Δ (coprime_uniformizer_first_factor W) (cop_pow W hUΔ hp0Δ hU 2)`. Establish `hxΔ : W.π₀ * LamUp W A c' e ^ 2 ∈ W.AΔ` using `W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hUΔ 2)`. Conclude with `cop_symm W (cop_pow W hp0Δ hxΔ (cop_symm W h1) N)`.
-/
theorem cop_lamUp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e N : ℕ) :
    Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0 ^ N) := by
  have hp0Δ : Formalism.MainNotions.ArcLiftingSetup.ps W 0 ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 0
  have hps : ∀ s, Formalism.MainNotions.ArcLiftingSetup.ps W s ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1
  have hU : Cop W (LamUp W A c' e) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) := by
    unfold LamUp Formalism.MainNotions.ArcLiftingSetup.abelian₂
    rw [map_prod]
    refine cop_prod W _ _ (fun s => ?_) hp0Δ fun s _ => ?_
    · rw [map_pow, ← ps_succ]; exact W.AΔ.pow_mem (hps _) _
    · rw [map_pow, ← ps_succ]
      exact cop_pow W (hps _) hp0Δ (coprime_frobenius_uniformizer_powers W hR hp0 (s + 1) (by omega)) _
  have hUΔ : LamUp W A c' e ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A _ e)
  have h1 : Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) :=
    cop_mul W hR.1 hp0Δ (coprime_uniformizer_first_factor W) (cop_pow W hUΔ hp0Δ hU 2)
  have hxΔ : W.π₀ * LamUp W A c' e ^ 2 ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hUΔ 2)
  exact cop_symm W (cop_pow W hp0Δ hxΔ (cop_symm W h1) N)

end Formalism.MainNotions.UnusedSlot80.LevC
