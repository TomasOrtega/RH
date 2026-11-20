import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEEnergy
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

/- English proof (translation)
Use `set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσdef`. Establish `hσ : ∀ i : Fin n, σ i.succ ≠ j`. Introduce `i h`. Establish `h' : σ (σ i.succ) = σ j` using `congrArg σ h`. Rewrite `h'` using `[Equiv.swap_apply_self, hσdef, Equiv.swap_apply_right]`.

Conclude with `Fin.succ_ne_zero i h'`. Set `d : EnergyStep.Data A Om` to `{ w := w, v := u j, f := fun i => u (σ i.succ), M := 1, w_smooth := hw, w_psh := hwp, v_smooth := hu j, v_nonpos := fun x => (hj x).2, le_v := fun x => (hj x).1, f_smooth := fun _ => hu _, f_psh := fun _ => hpsh _ }`. Establish `h` using `EnergyStep.proof A Om d`. Rewrite using `[← mIntSymm A _ σ, ← mIntSymm A (fun i => potForm Om.pot (Function.update u j 0 i)) σ]`. Establish `e1 : mInt A ((fun i => potForm Om.pot (u i)) ∘ σ) (fun x => -w x) = mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -w x)`.

Apply `st_mInt_congr_phi` to reduce the goal to its premises. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[σ, d, potForm]`. Simplify using `[d, EnergyStep.Data.T, potForm]`.

Establish `e2 : mInt A ((fun i => potForm Om.pot (Function.update u j 0 i)) ∘ σ) (fun x => -w x) = mInt A (Fin.cons Om.pot d.T) (fun x => -w x)`. Apply `st_mInt_congr_phi` to reduce the goal to its premises. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use function extensionality and compare the values at `x y`.

Simplify using `[σ, potForm, locPot_add_φ, LocPot.ofFun]`. Simplify using `[d, EnergyStep.Data.T, potForm, Function.update_of_ne (hσ i)]`. Rewrite using `[e1, e2]`. Simplify `h` using `[d]`.
-/
theorem lemmaEEnergy_step {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (u : Fin (n + 1) → X → ℝ) (w : X → ℝ)
    (hu : ∀ i, A.Smooth (u i)) (hpsh : ∀ i, IsPsh A (potForm Om.pot (u i))) (j : Fin (n + 1))
    (hj : ∀ x, -1 ≤ u j x ∧ u j x ≤ 0) (hw : A.Smooth w) (hwp : IsPsh A (potForm Om.pot w)) :
    mInt A (fun i => potForm Om.pot (u i)) (fun x => -w x) ≤
      mInt A (fun i => potForm Om.pot (Function.update u j 0 i)) (fun x => -w x) + Om.vol := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσdef
  have hσ : ∀ i : Fin n, σ i.succ ≠ j := by
    intro i h
    have h' : σ (σ i.succ) = σ j := congrArg σ h
    rw [Equiv.swap_apply_self, hσdef, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'
  let d : EnergyStep.Data A Om :=
    { w := w, v := u j, f := fun i => u (σ i.succ), M := 1, w_smooth := hw, w_psh := hwp,
      v_smooth := hu j, v_nonpos := fun x => (hj x).2, le_v := fun x => (hj x).1,
      f_smooth := fun _ => hu _, f_psh := fun _ => hpsh _ }
  have h := EnergyStep.proof A Om d
  rw [← mIntSymm A _ σ, ← mIntSymm A (fun i => potForm Om.pot (Function.update u j 0 i)) σ]
  have e1 : mInt A ((fun i => potForm Om.pot (u i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [σ, d, potForm]
    · simp [d, EnergyStep.Data.T, potForm]
  have e2 : mInt A ((fun i => potForm Om.pot (Function.update u j 0 i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons Om.pot d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      simp [σ, potForm, locPot_add_φ, LocPot.ofFun]
    · simp [d, EnergyStep.Data.T, potForm, Function.update_of_ne (hσ i)]
  rw [e1, e2]
  simpa [d] using h

/- English proof (translation)
Introduce `D X _ _ _ A Om v w hv hpsh hb hw hwp`. Consider the cases of `D with`. Consider the case `zero`. Establish `e : (fun i : Fin 0 => potForm Om.pot (v i)) = fun _ => Om.pot` using `funext fun i => i.elim0`. Simplify using `[e]`.

Consider the case `succ n`. Set `u : ℕ → Fin (n + 1) → X → ℝ` to `fun k i => if (i : ℕ) < k then v i else 0`. Establish `hu : ∀ k i, A.Smooth (u k i)` using `fun k i => by dsimp only [u]; split_ifs exacts [hv i, st_smooth_const A 0]`. Establish `hup : ∀ k i, IsPsh A (potForm Om.pot (u k i))` using `fun k i => by dsimp only [u]; split_ifs exacts [hpsh i, isPsh_add_const Om.isPsh 0]`. Establish `key : ∀ k ≤ n + 1, mInt A (fun i => potForm Om.pot (u k i)) (fun x => -w x) ≤ mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) + k * Om.vol`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk`. Establish `hupd : Function.update (u (k + 1)) ⟨k, hk⟩ 0 = u k`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = ⟨k, hk⟩`. Substitute `h` using the available equality.

Simplify using `[u]`. Rewrite using `[Function.update_of_ne h]`. Establish `hik : (i : ℕ) ≠ k` using `fun e => h (Fin.ext e)`. Distinguish the cases in `hlt : (i : ℕ) < k`. Simplify using `[u, hlt, Nat.lt_succ_of_lt hlt]`.

Establish `: ¬ (i : ℕ) < k + 1` using `by omega`. Simplify using `[u, hlt, this]`. Establish `step` using `lemmaEEnergy_step A Om (u (k + 1)) w (hu _) (hup _) ⟨k, hk⟩ (fun x => by simpa [u] using hb ⟨k, hk⟩ x) hw hwp`. Rewrite `step` using `[hupd]`. Use `ih (by omega)` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `key (n + 1) le_rfl`. Establish `e1 : (fun i => potForm Om.pot (u (n + 1) i)) = fun i => potForm Om.pot (v i)`. Use function extensionality and compare the values at `fun i => by simp [u, i.isLt]`.

Establish `e0 : mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) = mInt A (fun _ => Om.pot) (fun x => -w x)`. Apply `st_mInt_congr_phi` to reduce the goal to its premises. Introduce `i`. Use function extensionality and compare the values at `x y`. Simplify using `[u, potForm, locPot_add_φ, LocPot.ofFun]`.

Rewrite `h1` using `[e1, e0]`. Simplify using `using h1`.
-/
theorem LemmaEEnergy.proof : LemmaEEnergy.Statement := by
  intro D X _ _ _ A Om v w hv hpsh hb hw hwp
  cases D with
  | zero =>
    have e : (fun i : Fin 0 => potForm Om.pot (v i)) = fun _ => Om.pot := funext fun i => i.elim0
    simp [e]
  | succ n =>
    let u : ℕ → Fin (n + 1) → X → ℝ := fun k i => if (i : ℕ) < k then v i else 0
    have hu : ∀ k i, A.Smooth (u k i) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hv i, st_smooth_const A 0]
    have hup : ∀ k i, IsPsh A (potForm Om.pot (u k i)) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hpsh i, isPsh_add_const Om.isPsh 0]
    have key : ∀ k ≤ n + 1, mInt A (fun i => potForm Om.pot (u k i)) (fun x => -w x) ≤
        mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) + k * Om.vol := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hupd : Function.update (u (k + 1)) ⟨k, hk⟩ 0 = u k := by
          funext i
          by_cases h : i = ⟨k, hk⟩
          · subst h; simp [u]
          · rw [Function.update_of_ne h]
            have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
            by_cases hlt : (i : ℕ) < k
            · simp [u, hlt, Nat.lt_succ_of_lt hlt]
            · have : ¬ (i : ℕ) < k + 1 := by omega
              simp [u, hlt, this]
        have step := lemmaEEnergy_step A Om (u (k + 1)) w (hu _) (hup _) ⟨k, hk⟩
          (fun x => by simpa [u] using hb ⟨k, hk⟩ x) hw hwp
        rw [hupd] at step
        have := ih (by omega)
        push_cast
        linarith
    have h1 := key (n + 1) le_rfl
    have e1 : (fun i => potForm Om.pot (u (n + 1) i)) = fun i => potForm Om.pot (v i) :=
      funext fun i => by simp [u, i.isLt]
    have e0 : mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) =
        mInt A (fun _ => Om.pot) (fun x => -w x) := by
      apply st_mInt_congr_phi
      intro i
      funext x y
      simp [u, potForm, locPot_add_φ, LocPot.ofFun]
    rw [e1, e0] at h1
    simpa using h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
