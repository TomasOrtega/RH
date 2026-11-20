import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M

noncomputable section

structure EnergyStep.Data {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (n + 1) X)
    (Om : KaehlerForm A) where

  w : X → ℝ

  v : X → ℝ

  f : Fin n → X → ℝ

  M : ℝ
  w_smooth : A.Smooth w
  w_psh : IsPsh A (Om.pot + LocPot.ofFun w)
  v_smooth : A.Smooth v
  v_nonpos : ∀ x, v x ≤ 0
  le_v : ∀ x, -M ≤ v x
  f_smooth : ∀ i, A.Smooth (f i)
  f_psh : ∀ i, IsPsh A (Om.pot + LocPot.ofFun (f i))

def EnergyStep.Data.T {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas (n + 1) X}
    {Om : KaehlerForm A} (d : EnergyStep.Data A Om) : Fin n → LocPot X :=
  fun i => Om.pot + LocPot.ofFun (d.f i)

def EnergyStep.Statement : Prop :=
  ∀ {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (d : EnergyStep.Data A Om),
    mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -d.w x) ≤
      mInt A (Fin.cons Om.pot d.T) (fun x => -d.w x) + d.M * Om.vol

/- English proof (translation)
Introduce `x j y hy z`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Simplify using `[levi]`. Conclude with `(Om.pos x j y hy z hz).le`.
-/
theorem KaehlerForm.isPsh {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    (Om : KaehlerForm A) : IsPsh A Om.pot := by
  intro x j y hy z
  by_cases hz : z = 0
  · subst hz
    simp [levi]
  · exact (Om.pos x j y hy z hz).le

/- English proof (translation)
Establish `h : fderiv ℝ (fun y' => g y' + c) = fderiv ℝ g` using `funext fun y' => fderiv_add_const c`. Unfold `levi`. Rewrite using `[h]`.
-/
theorem levi_add_const {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (c : ℝ) (y z : ι → ℂ) :
    levi (fun y' => g y' + c) y z = levi g y z := by
  have h : fderiv ℝ (fun y' => g y' + c) = fderiv ℝ g := funext fun y' => fderiv_add_const c
  unfold levi
  rw [h]

/- English proof (translation)
Introduce `x j y hy z`. Establish `h : (P + LocPot.ofFun fun _ => c).φ x ∘ (A.chart j).symm = fun y' => (P.φ x ∘ (A.chart j).symm) y' + c` using `rfl`. Rewrite using `[h, levi_add_const]`. Conclude with `hP x j y ⟨hy.1, hy.2.1⟩ z`.
-/
theorem isPsh_add_const {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {P : LocPot X} (hP : IsPsh A P) (c : ℝ) : IsPsh A (P + LocPot.ofFun fun _ => c) := by
  intro x j y hy z
  have h : (P + LocPot.ofFun fun _ => c).φ x ∘ (A.chart j).symm =
      fun y' => (P.φ x ∘ (A.chart j).symm) y' + c := rfl
  rw [h, levi_add_const]
  exact hP x j y ⟨hy.1, hy.2.1⟩ z

/- English proof (translation)
Establish `h` using `mIntLinear A Φ hΦ (-1) g (fun _ => 0) hg (mIntegrableCont A Φ hΦ _ continuous_const)`. Simplify using `only [neg_one_mul, add_zero, st_mInt_zero] at h`. Conclude with `h`.
-/
theorem mInt_neg {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas n X) (Φ : Fin n → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ)
    (hg : MIntegrable A Φ g) : mInt A Φ (fun x => -g x) = -mInt A Φ g := by
  have h := mIntLinear A Φ hΦ (-1) g (fun _ => 0) hg (mIntegrableCont A Φ hΦ _ continuous_const)
  simp only [neg_one_mul, add_zero, st_mInt_zero] at h
  exact h

/- English proof (translation)
Introduce `n X _ _ _ A Om d`. Establish `hT : ∀ i, IsPotential A (d.T i)` using `fun i => isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (d.f_smooth i))`. Establish `hcons : ∀ P, IsPotential A P → ∀ i, IsPotential A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i)`. Introduce `P hP i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `using hP`. Simplify using `using hT i`. Establish `hw` using `isPotential_ofFun A _ d.w_smooth`. Establish `hv` using `isPotential_ofFun A _ d.v_smooth`. Establish `hOw` using `isPotentialAdd A _ _ Om.isPot hw`.

Establish `cw` using `st_smooth_continuous A d.w_smooth`. Establish `cv` using `st_smooth_continuous A d.v_smooth`. Establish `int : ∀ P, IsPotential A P → ∀ g : X → ℝ, Continuous g → MIntegrable A (Fin.cons P d.T) g` using `fun P hP g hg => mIntegrableCont A _ (hcons P hP) g hg`. Establish `h1` using `mIntAdd A Om.pot (LocPot.ofFun d.v) d.T Om.isPot hv hT (fun x => -d.w x) (int _ Om.isPot _ cw.neg) (int _ hv _ cw.neg)`. Establish `h2` using `mInt_neg A _ (hcons _ hv) d.w (int _ hv _ cw)`.

Establish `h3` using `(byPartsSymm A d.v d.w d.v_smooth d.w_smooth d.T hT).symm`. Establish `h4` using `mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT d.v (int _ Om.isPot _ cv) (int _ hw _ cv)`. Establish `hpsh : ∀ P, IsPsh A P → ∀ i, IsPsh A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i)`. Introduce `P hP i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `using hP`. Conclude with `d.f_psh i`. Establish `h5` using `mIntNonneg A _ (hcons _ Om.isPot) (hpsh _ Om.isPsh) (fun x => -d.v x) fun x => by have := d.v_nonpos x; linarith`. Rewrite `h5` using `[mInt_neg A _ (hcons _ Om.isPot) d.v (int _ Om.isPot _ cv)]`. Establish `h6` using `mIntLinear A _ (hcons _ hOw) d.M (fun _ => 1) d.v (int _ hOw _ continuous_const) (int _ hOw _ cv)`.

Use `beta_reduce at h6`. Establish `h7` using `mIntNonneg A _ (hcons _ hOw) (hpsh _ d.w_psh) (fun x => d.M * 1 + d.v x) fun x => by have := d.le_v x; linarith`. Rewrite `h7` using `[h6]`. Establish `h8` using `mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT (fun _ => 1) (int _ Om.isPot _ continuous_const) (int _ hw _ continuous_const)`. Establish `h9` using `stokes A d.w d.w_smooth d.T hT`.

Establish `h10` using `massIndep A (fun _ => Om.pot) (Fin.cons (fun _ => 0) d.f) (fun _ => Om.isPot) (by`. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `using st_smooth_const A 0`. Simplify using `using d.f_smooth i)`.

Establish `h11 : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) = mInt A (fun i => Om.pot + LocPot.ofFun ((Fin.cons (fun _ => 0) d.f : Fin (n + 1) → X → ℝ) i)) (fun _ => 1)`. Apply `st_mInt_congr_phi` to reduce the goal to its premises. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use function extensionality and compare the values at `x y show Om.pot.φ x y = Om.pot.φ x y + 0`.

Expand and normalize the polynomial expressions, which then agree. Both sides reduce to the same expression. Establish `hV : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) = Om.vol`. Rewrite using `[h11, h10]`. Both sides reduce to the same expression.

Rewrite `h7` using `[h8, h9, add_zero, hV]`. Rewrite using `[h1, h2, h3]`. Combine the linear relations using `[h4, h5, h7]`.
-/
theorem EnergyStep.proof : EnergyStep.Statement := by
  intro n X _ _ _ A Om d
  have hT : ∀ i, IsPotential A (d.T i) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (d.f_smooth i))
  have hcons : ∀ P, IsPotential A P → ∀ i, IsPotential A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · simpa using hT i
  have hw := isPotential_ofFun A _ d.w_smooth
  have hv := isPotential_ofFun A _ d.v_smooth
  have hOw := isPotentialAdd A _ _ Om.isPot hw
  have cw := st_smooth_continuous A d.w_smooth
  have cv := st_smooth_continuous A d.v_smooth
  have int : ∀ P, IsPotential A P → ∀ g : X → ℝ, Continuous g →
      MIntegrable A (Fin.cons P d.T) g := fun P hP g hg => mIntegrableCont A _ (hcons P hP) g hg

  have h1 := mIntAdd A Om.pot (LocPot.ofFun d.v) d.T Om.isPot hv hT (fun x => -d.w x)
    (int _ Om.isPot _ cw.neg) (int _ hv _ cw.neg)
  have h2 := mInt_neg A _ (hcons _ hv) d.w (int _ hv _ cw)
  have h3 := (byPartsSymm A d.v d.w d.v_smooth d.w_smooth d.T hT).symm
  have h4 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT d.v
    (int _ Om.isPot _ cv) (int _ hw _ cv)
  have hpsh : ∀ P, IsPsh A P → ∀ i, IsPsh A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · exact d.f_psh i

  have h5 := mIntNonneg A _ (hcons _ Om.isPot) (hpsh _ Om.isPsh) (fun x => -d.v x)
    fun x => by have := d.v_nonpos x; linarith
  rw [mInt_neg A _ (hcons _ Om.isPot) d.v (int _ Om.isPot _ cv)] at h5

  have h6 := mIntLinear A _ (hcons _ hOw) d.M (fun _ => 1) d.v (int _ hOw _ continuous_const)
    (int _ hOw _ cv)
  beta_reduce at h6
  have h7 := mIntNonneg A _ (hcons _ hOw) (hpsh _ d.w_psh) (fun x => d.M * 1 + d.v x)
    fun x => by have := d.le_v x; linarith
  rw [h6] at h7

  have h8 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT (fun _ => 1)
    (int _ Om.isPot _ continuous_const) (int _ hw _ continuous_const)
  have h9 := stokes A d.w d.w_smooth d.T hT
  have h10 := massIndep A (fun _ => Om.pot) (Fin.cons (fun _ => 0) d.f) (fun _ => Om.isPot)
    (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using st_smooth_const A 0
      · simpa using d.f_smooth i)
  have h11 : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) =
      mInt A (fun i => Om.pot + LocPot.ofFun ((Fin.cons (fun _ => 0) d.f : Fin (n + 1) → X → ℝ) i))
        (fun _ => 1) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      show Om.pot.φ x y = Om.pot.φ x y + 0
      ring
    · rfl
  have hV : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) = Om.vol := by
    rw [h11, h10]
    rfl
  rw [h8, h9, add_zero, hV] at h7
  rw [h1, h2, h3]
  linarith [h4, h5, h7]

def projectiveLineEnergyData : EnergyStep.Data p1 projectiveLineKaehler where
  w _ := -1
  v _ := -1 / 2
  f := Fin.elim0
  M := 1
  w_smooth := st_smooth_const p1 (-1)
  w_psh := isPsh_add_const projectiveLineKaehler.isPsh (-1)
  v_smooth := st_smooth_const p1 (-1 / 2)
  v_nonpos _ := by norm_num
  le_v _ := by norm_num
  f_smooth i := Fin.elim0 i
  f_psh i := Fin.elim0 i

/- English proof (translation)
The claim follows from `EnergyStep.proof p1 projectiveLineKaehler projectiveLineEnergyData`.
-/
theorem projectiveLine_energy_inequality :
    mInt p1 (Fin.cons (projectiveLineKaehler.pot + LocPot.ofFun projectiveLineEnergyData.v) projectiveLineEnergyData.T)
        (fun x => -projectiveLineEnergyData.w x) ≤
      mInt p1 (Fin.cons projectiveLineKaehler.pot projectiveLineEnergyData.T) (fun x => -projectiveLineEnergyData.w x) +
        projectiveLineEnergyData.M * projectiveLineKaehler.vol :=
  EnergyStep.proof p1 projectiveLineKaehler projectiveLineEnergyData

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
