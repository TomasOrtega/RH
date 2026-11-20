import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceStatements
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Finset
open ReciprocityTheory.AnForm.M

noncomputable section

namespace WeightCocycle

variable {X : Type} [TopologicalSpace X]

def tupleOfList (n : ℕ) (L : List (LocPot X)) : Fin n → LocPot X :=
  fun i => L.getD i (LocPot.ofFun fun _ => 0)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp [tupleOfList]`.
-/
theorem tupleOfList_cons (e : ℕ) (x : LocPot X) (L : List (LocPot X)) :
    tupleOfList (e + 1) (x :: L) = Fin.cons x (tupleOfList e L) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [tupleOfList]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => intro n _`. Conclude with `⟨1, rfl⟩`. Consider the case `cons x h ih`. Introduce `n hn`.

Simplify using `only [List.length_cons] at hn`. Substitute `hn` using the available equality. Take `⟨σ, hσ⟩` from `ih _ rfl`. Use `⟨Equiv.Perm.decomposeFin.symm (0, σ), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[tupleOfList]`. Use `congrFun hσ i` as an intermediate fact. Simplify using `only [tupleOfList, Function.comp_apply] at this`. Rewrite using `[Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]`.

Simplify using `only [tupleOfList, Fin.val_succ, List.getD_cons_succ]`. Conclude with `this`. Consider the case `swap x y l`. Introduce `n hn`. Simplify using `only [List.length_cons] at hn`.

Substitute `hn` using the available equality. Use `⟨Equiv.swap 0 1, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[tupleOfList]`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[tupleOfList]`. Establish `h0 : (i.succ.succ : Fin (l.length + 1 + 1)) ≠ 0` using `Fin.succ_ne_zero _`. Establish `h1 : (i.succ.succ : Fin (l.length + 1 + 1)) ≠ 1` using `Fin.succ_succ_ne_one _`. Simplify using `[tupleOfList, Equiv.swap_apply_of_ne_of_ne h0 h1]`.

Consider the case `trans h₁ _ ih₁ ih₂`. Introduce `n hn`. Take `⟨σ₁, e₁⟩` from `ih₁ n hn`. Take `⟨σ₂, e₂⟩` from `ih₂ n (h₁.length_eq ▸ hn)`. Conclude with `⟨σ₁ * σ₂, by rw [e₂, e₁]; rfl⟩`.
-/
theorem tupleOfList_perm {L L' : List (LocPot X)} (h : L.Perm L') :
    ∀ n, L.length = n → ∃ σ : Equiv.Perm (Fin n), tupleOfList n L' = tupleOfList n L ∘ σ := by
  induction h with
  | nil => intro n _; exact ⟨1, rfl⟩
  | cons x h ih =>
    intro n hn
    simp only [List.length_cons] at hn
    subst hn
    obtain ⟨σ, hσ⟩ := ih _ rfl
    refine ⟨Equiv.Perm.decomposeFin.symm (0, σ), ?_⟩
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [tupleOfList]
    · have := congrFun hσ i
      simp only [tupleOfList, Function.comp_apply] at this
      rw [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
        Equiv.refl_apply]
      simp only [tupleOfList, Fin.val_succ, List.getD_cons_succ]
      exact this
  | swap x y l =>
    intro n hn
    simp only [List.length_cons] at hn
    subst hn
    refine ⟨Equiv.swap 0 1, ?_⟩
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [tupleOfList]
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [tupleOfList]
      · have h0 : (i.succ.succ : Fin (l.length + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
        have h1 : (i.succ.succ : Fin (l.length + 1 + 1)) ≠ 1 := Fin.succ_succ_ne_one _
        simp [tupleOfList, Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans h₁ _ ih₁ ih₂ =>
    intro n hn
    obtain ⟨σ₁, e₁⟩ := ih₁ n hn
    obtain ⟨σ₂, e₂⟩ := ih₂ n (h₁.length_eq ▸ hn)
    exact ⟨σ₁ * σ₂, by rw [e₂, e₁]; rfl⟩

/- English proof (translation)
Take `⟨σ, hσ⟩` from `tupleOfList_perm h n hn`. Rewrite using `[hσ]`. Conclude with `mIntSymm A _ σ g`.
-/
theorem mInt_perm {n : ℕ} (A : FinHolAtlas n X) {L L' : List (LocPot X)} (h : L.Perm L')
    (hn : L.length = n) (g : X → ℝ) :
    mInt A (tupleOfList n L') g = mInt A (tupleOfList n L) g := by
  obtain ⟨σ, hσ⟩ := tupleOfList_perm h n hn
  rw [hσ]
  exact mIntSymm A _ σ g

/- English proof (translation)
Unfold `tupleOfList`. Rewrite using `[List.getD_eq_getElem?_getD]`. Consider the cases of `h : L[(i : ℕ)]? with`. Consider the case `none => simpa using isPotential_ofFun A _ (st_smooth_const A 0)`. Consider the case `some x => simpa using hL x (List.mem_of_getElem? h)`.
-/
theorem isPotential_tupleOfList {d : ℕ} (A : FinHolAtlas d X) {n : ℕ} {L : List (LocPot X)}
    (hL : ∀ x ∈ L, IsPotential A x) (i : Fin n) : IsPotential A (tupleOfList n L i) := by
  unfold tupleOfList
  rw [List.getD_eq_getElem?_getD]
  cases h : L[(i : ℕ)]? with
  | none => simpa using isPotential_ofFun A _ (st_smooth_const A 0)
  | some x => simpa using hL x (List.mem_of_getElem? h)

/- English proof (translation)
Introduce `_ hx` and use `(List.eq_of_mem_replicate hx) ▸ hP`.
-/
theorem pot_replicate {d : ℕ} (A : FinHolAtlas d X) {P : LocPot X} (hP : IsPotential A P) (k : ℕ) :
    ∀ x ∈ List.replicate k P, IsPotential A x := fun _ hx => (List.eq_of_mem_replicate hx) ▸ hP

/- English proof (translation)
Introduce `x hx` and use `(List.mem_append.1 hx).elim (h x) (h' x)`.
-/
theorem pot_append {d : ℕ} (A : FinHolAtlas d X) {L L' : List (LocPot X)}
    (h : ∀ x ∈ L, IsPotential A x) (h' : ∀ x ∈ L', IsPotential A x) :
    ∀ x ∈ L ++ L', IsPotential A x := fun x hx => (List.mem_append.1 hx).elim (h x) (h' x)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hi` using `i.isLt`. Unfold `tupleOfList`. Rewrite using `[List.getD_eq_getElem?_getD]`. Distinguish the cases in `h : (i : ℕ) < k`.

Rewrite using `[if_pos h, List.getElem?_append_left (by simpa using h), List.getElem?_replicate, if_pos h]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, List.getElem?_append_right (by simp; omega), List.getElem?_replicate, List.length_replicate, if_pos (by omega)]`. Both sides reduce to the same expression.
-/
theorem ite_eq_tupleOfList_replicate (n k : ℕ) (hk : k ≤ n) (P Q : LocPot X) :
    (fun i : Fin n => if (i : ℕ) < k then P else Q) =
      tupleOfList n (List.replicate k P ++ List.replicate (n - k) Q) := by
  funext i
  have hi := i.isLt
  unfold tupleOfList
  rw [List.getD_eq_getElem?_getD]
  by_cases h : (i : ℕ) < k
  · rw [if_pos h, List.getElem?_append_left (by simpa using h), List.getElem?_replicate, if_pos h]
    rfl
  · rw [if_neg h, List.getElem?_append_right (by simp; omega), List.getElem?_replicate,
      List.length_replicate, if_pos (by omega)]
    rfl

variable [CompactSpace X] [T2Space X]

/- English proof (translation)
Establish `hw` using `isPotential_ofFun A v hv`. Establish `h1` using `isPotential_tupleOfList (n := e + 1) A (L := a :: L) (by`. Introduce `x hx`. Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Conclude with `ha`.

Conclude with `hL x hx)`. Establish `h2` using `isPotential_tupleOfList (n := e + 1) A (L := LocPot.ofFun v :: L) (by`. Introduce `x hx`. Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Conclude with `hw`.

Conclude with `hL x hx)`. Rewrite `h1`, `h2` using `[tupleOfList_cons]`. Rewrite using `[tupleOfList_cons, tupleOfList_cons, tupleOfList_cons, ← mIntAdd A a (LocPot.ofFun v) _ ha hw (isPotential_tupleOfList A hL) g (mIntegrableCont A _ h1 g hg) (mIntegrableCont A _ h2 g hg)]`. Apply `st_mInt_congr_phi` to reduce the goal to its premises. Introduce `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use function extensionality and compare the values at `z y`. Simplify using `only [Fin.cons_zero]`. Rewrite using `[hqv]`. Both sides reduce to the same expression.

Both sides reduce to the same expression.
-/
theorem mInt_cons_split {e : ℕ} (A : FinHolAtlas (e + 1) X) {a q : LocPot X} {v : X → ℝ}
    (ha : IsPotential A a) (hv : A.Smooth v) (hqv : ∀ z y, q.φ z y = a.φ z y + v y)
    (L : List (LocPot X)) (hL : ∀ x ∈ L, IsPotential A x) (g : X → ℝ) (hg : Continuous g) :
    mInt A (tupleOfList (e + 1) (q :: L)) g =
      mInt A (tupleOfList (e + 1) (a :: L)) g + mInt A (tupleOfList (e + 1) (LocPot.ofFun v :: L)) g := by
  have hw := isPotential_ofFun A v hv
  have h1 := isPotential_tupleOfList (n := e + 1) A (L := a :: L) (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hL x hx)
  have h2 := isPotential_tupleOfList (n := e + 1) A (L := LocPot.ofFun v :: L) (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hw
    · exact hL x hx)
  rw [tupleOfList_cons] at h1 h2
  rw [tupleOfList_cons, tupleOfList_cons, tupleOfList_cons,
    ← mIntAdd A a (LocPot.ofFun v) _ ha hw (isPotential_tupleOfList A hL) g
      (mIntegrableCont A _ h1 g hg) (mIntegrableCont A _ h2 g hg)]
  apply st_mInt_congr_phi
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · funext z y
    simp only [Fin.cons_zero]
    rw [hqv]
    rfl
  · rfl

/- English proof (translation)
Take `⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun j => mInt A (tupleOfList (e + 1) (P ++ List.replicate j q ++ List.replicate (m - j) a)) g` from `⟨_, rfl⟩`. Establish `step : ∀ j ∈ range m, f (j + 1) - f j = mInt A (tupleOfList (e + 1) (LocPot.ofFun v :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g`. Introduce `j hj`. Rewrite `hj` using `[mem_range]`. Establish `hR : ∀ x ∈ P ++ List.replicate j q ++ List.replicate (m - 1 - j) a, IsPotential A x` using `pot_append A (pot_append A hP (pot_replicate A hq j)) (pot_replicate A ha _)`.

Establish `hRl : (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a).length = e`. Simplify using `only [List.length_append, List.length_replicate]`. Use linear arithmetic over natural numbers and integers. Establish `e1 : f (j + 1) = mInt A (tupleOfList (e + 1) (q :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g`. Establish `hl : P ++ List.replicate (j + 1) q ++ List.replicate (m - (j + 1)) a = (P ++ List.replicate j q) ++ q :: List.replicate (m - 1 - j) a`.

Rewrite using `[List.replicate_succ', show m - (j + 1) = m - 1 - j by omega]`. Simplify using the standard rewrite rules. Simplify using `only [hf]`. Rewrite using `[hl]`. Conclude with `mInt_perm A List.perm_middle.symm (by`.

Simplify using `only [List.length_cons, List.length_append, List.length_replicate]`. Use the proof step `omega) g`. Establish `e2 : f j = mInt A (tupleOfList (e + 1) (a :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g`. Establish `hl : P ++ List.replicate j q ++ List.replicate (m - j) a = (P ++ List.replicate j q) ++ a :: List.replicate (m - 1 - j) a`. Rewrite using `[show m - j = m - 1 - j + 1 by omega, List.replicate_succ]`.

Simplify using `only [hf]`. Rewrite using `[hl]`. Conclude with `mInt_perm A List.perm_middle.symm (by`. Simplify using `only [List.length_cons, List.length_append, List.length_replicate]`. Use the proof step `omega) g`.

Rewrite using `[e1, e2, mInt_cons_split A ha hv hqv _ hR g hg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Finset.sum_congr rfl step, Finset.sum_range_sub]`. Establish `hfm : f m = mInt A (tupleOfList (e + 1) (P ++ List.replicate m q)) g`. Simplify using `[hf]`.

Establish `hf0 : f 0 = mInt A (tupleOfList (e + 1) (P ++ List.replicate m a)) g`. Simplify using `[hf]`. Rewrite using `[hfm, hf0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tele {e : ℕ} (A : FinHolAtlas (e + 1) X) {a q : LocPot X} {v : X → ℝ}
    (ha : IsPotential A a) (hq : IsPotential A q) (hv : A.Smooth v)
    (hqv : ∀ z y, q.φ z y = a.φ z y + v y) (P : List (LocPot X)) (hP : ∀ x ∈ P, IsPotential A x)
    (m : ℕ) (hm : P.length + m = e + 1) (g : X → ℝ) (hg : Continuous g) :
    mInt A (tupleOfList (e + 1) (P ++ List.replicate m q)) g =
      mInt A (tupleOfList (e + 1) (P ++ List.replicate m a)) g +
        ∑ j ∈ range m, mInt A (tupleOfList (e + 1)
          (LocPot.ofFun v :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun j =>
      mInt A (tupleOfList (e + 1) (P ++ List.replicate j q ++ List.replicate (m - j) a)) g := ⟨_, rfl⟩
  have step : ∀ j ∈ range m, f (j + 1) - f j = mInt A (tupleOfList (e + 1)
      (LocPot.ofFun v :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g := by
    intro j hj
    rw [mem_range] at hj
    have hR : ∀ x ∈ P ++ List.replicate j q ++ List.replicate (m - 1 - j) a, IsPotential A x :=
      pot_append A (pot_append A hP (pot_replicate A hq j)) (pot_replicate A ha _)
    have hRl : (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a).length = e := by
      simp only [List.length_append, List.length_replicate]
      omega
    have e1 : f (j + 1) = mInt A (tupleOfList (e + 1)
        (q :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g := by
      have hl : P ++ List.replicate (j + 1) q ++ List.replicate (m - (j + 1)) a =
          (P ++ List.replicate j q) ++ q :: List.replicate (m - 1 - j) a := by
        rw [List.replicate_succ', show m - (j + 1) = m - 1 - j by omega]
        simp
      simp only [hf]
      rw [hl]
      exact mInt_perm A List.perm_middle.symm (by
        simp only [List.length_cons, List.length_append, List.length_replicate]; omega) g
    have e2 : f j = mInt A (tupleOfList (e + 1)
        (a :: (P ++ List.replicate j q ++ List.replicate (m - 1 - j) a))) g := by
      have hl : P ++ List.replicate j q ++ List.replicate (m - j) a =
          (P ++ List.replicate j q) ++ a :: List.replicate (m - 1 - j) a := by
        rw [show m - j = m - 1 - j + 1 by omega, List.replicate_succ]
      simp only [hf]
      rw [hl]
      exact mInt_perm A List.perm_middle.symm (by
        simp only [List.length_cons, List.length_append, List.length_replicate]; omega) g
    rw [e1, e2, mInt_cons_split A ha hv hqv _ hR g hg]
    ring
  rw [← Finset.sum_congr rfl step, Finset.sum_range_sub]
  have hfm : f m = mInt A (tupleOfList (e + 1) (P ++ List.replicate m q)) g := by
    simp [hf]
  have hf0 : f 0 = mInt A (tupleOfList (e + 1) (P ++ List.replicate m a)) g := by
    simp [hf]
  rw [hfm, hf0]
  ring

/- English proof (translation)
Establish `h : ∀ g : ℕ → ℕ → ℝ, ∑ k ∈ range (n + 1), ∑ j ∈ range (n - k), g k j = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1), if k + j < n then g k j else 0`. Introduce `g`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter]`. Use `congr 1`.

Use extensionality with `j`. Simplify using `only [mem_range, mem_filter]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h f, h (fun k j => f j k), Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Nat.add_comm j k]`.
-/
theorem dsum_swap (n : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ k ∈ range (n + 1), ∑ j ∈ range (n - k), f k j =
      ∑ k ∈ range (n + 1), ∑ j ∈ range (n - k), f j k := by
  have h : ∀ g : ℕ → ℕ → ℝ, ∑ k ∈ range (n + 1), ∑ j ∈ range (n - k), g k j =
      ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1), if k + j < n then g k j else 0 := by
    intro g
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [mem_range, mem_filter]
    omega
  rw [h f, h (fun k j => f j k), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.add_comm j k]

/- English proof (translation)
Establish `cu` using `st_smooth_continuous A hu`. Establish `cv` using `st_smooth_continuous A hv`. Establish `S1 : ∀ k ∈ range (e + 1 + 1), mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) q)) u = mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) a)) u + ∑ j ∈ range (e + 1 - k), mInt A (tupleOfList (e + 1) (LocPot.ofFun v :: (List. …`. Introduce `k hk`. Rewrite `hk` using `[mem_range]`.

Conclude with `tele A ha hq hv hqv _ (pot_replicate A hp k) (e + 1 - k) (by simp; omega) u cu`. Establish `S2 : ∀ k ∈ range (e + 1 + 1), mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) p)) v = mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) a)) v + ∑ j ∈ range (e + 1 - k), mInt A (tupleOfList (e + 1) (LocPot.ofFun u :: (List. …`. Introduce `k hk`. Rewrite `hk` using `[mem_range]`. Conclude with `tele A ha hp hu hpu _ (pot_replicate A hq k) (e + 1 - k) (by simp; omega) v cv`.

Establish `S3 : ∀ k j, k + j < e + 1 → mInt A (tupleOfList (e + 1) (LocPot.ofFun u :: (List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a))) v = mInt A (tupleOfList (e + 1) (LocPot.ofFun v :: (List.replicate j p ++ List.replicate k q ++ List.replicate (e + 1 - …`. Introduce `k j hkj`. Establish `hL : ∀ x ∈ List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a, IsPotential A x` using `pot_append A (pot_append A (pot_replicate A hq k) (pot_replicate A hp j)) (pot_replicate A ha _)`. Establish `h1` using `byPartsSymm A u v hu hv _ (isPotential_tupleOfList (n := e) A hL)`. Rewrite using `[tupleOfList_cons, ← h1, ← tupleOfList_cons, show e + 1 - j - 1 - k = e + 1 - k - 1 - j by omega]`.

Use `mInt_perm A (List.Perm.cons _ (List.perm_append_comm.append_right _)) ?_ u` and prove the remaining obligations. Simplify using `only [List.length_cons, List.length_append, List.length_replicate]`. Use linear arithmetic over natural numbers and integers. Establish `lin : ∀ L : List (LocPot X), (∀ x ∈ L, IsPotential A x) → mInt A (tupleOfList (e + 1) L) (fun z => u z - v z) = mInt A (tupleOfList (e + 1) L) u - mInt A (tupleOfList (e + 1) L) v`. Introduce `L hL`.

Establish `hΦ` using `isPotential_tupleOfList (n := e + 1) A hL`. Establish `h` using `mIntLinear A _ hΦ (-1) v u (mIntegrableCont A _ hΦ v cv) (mIntegrableCont A _ hΦ u cu)`. Establish `hfun : (fun z => u z - v z) = fun z => -1 * v z + u z`. Use function extensionality and compare the values at `z`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfun, h]`. Expand and normalize the polynomial expressions, which then agree. Establish `S5 : ∑ k ∈ range (e + 1 + 1), mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) q)) v = ∑ k ∈ range (e + 1 + 1), mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) p)) v`. Rewrite using `[← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Rewrite `hk` using `[mem_range]`. Rewrite using `[show e + 1 + 1 - 1 - k = e + 1 - k by omega, show e + 1 - (e + 1 - k) = k by omega]`. Use `mInt_perm A List.perm_append_comm ?_ v` and prove the remaining obligations. Simplify using `only [List.length_append, List.length_replicate]`. Use linear arithmetic over natural numbers and integers.

Establish `T : ∑ k ∈ range (e + 1 + 1), ∑ j ∈ range (e + 1 - k), mInt A (tupleOfList (e + 1) (LocPot.ofFun u :: (List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a))) v = ∑ k ∈ range (e + 1 + 1), ∑ j ∈ range (e + 1 - k), mInt A (tupleOfList (e + 1) (LocPot.ofFu …`. Use `Eq.trans ?_ (dsum_swap (e + 1) (fun k j => mInt A (tupleOfList (e + 1) (LocPot.ofFun v :: (List.replicate k p ++ List.replicate j q ++ List.replicate (e + 1 - k - 1 - j) a))) u)).symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hk`, `hj` using `[mem_range]`. Conclude with `S3 k j (by omega)`.

Rewrite using `[Finset.sum_congr rfl fun k _ => lin _ (pot_append A (pot_replicate A hp k) (pot_replicate A hq _)), Finset.sum_sub_distrib, S5, Finset.sum_congr rfl S1, Finset.sum_congr rfl S2, Finset.sum_add_distrib, Finset.sum_add_distrib, T]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core {e : ℕ} (A : FinHolAtlas (e + 1) X) (a p q : LocPot X) (u v : X → ℝ)
    (ha : IsPotential A a) (hp : IsPotential A p) (hq : IsPotential A q) (hu : A.Smooth u)
    (hv : A.Smooth v) (hpu : ∀ z y, p.φ z y = a.φ z y + u y)
    (hqv : ∀ z y, q.φ z y = a.φ z y + v y) :
    (∑ k ∈ range (e + 1 + 1),
        mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) a)) u) -
      (∑ k ∈ range (e + 1 + 1),
        mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) a)) v) =
      ∑ k ∈ range (e + 1 + 1),
        mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) q))
          (fun z => u z - v z) := by
  have cu := st_smooth_continuous A hu
  have cv := st_smooth_continuous A hv
  have S1 : ∀ k ∈ range (e + 1 + 1),
      mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) q)) u =
        mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) a)) u +
        ∑ j ∈ range (e + 1 - k), mInt A (tupleOfList (e + 1) (LocPot.ofFun v ::
          (List.replicate k p ++ List.replicate j q ++ List.replicate (e + 1 - k - 1 - j) a))) u := by
    intro k hk
    rw [mem_range] at hk
    exact tele A ha hq hv hqv _ (pot_replicate A hp k) (e + 1 - k) (by simp; omega) u cu
  have S2 : ∀ k ∈ range (e + 1 + 1),
      mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) p)) v =
        mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) a)) v +
        ∑ j ∈ range (e + 1 - k), mInt A (tupleOfList (e + 1) (LocPot.ofFun u ::
          (List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a))) v := by
    intro k hk
    rw [mem_range] at hk
    exact tele A ha hp hu hpu _ (pot_replicate A hq k) (e + 1 - k) (by simp; omega) v cv
  have S3 : ∀ k j, k + j < e + 1 →
      mInt A (tupleOfList (e + 1) (LocPot.ofFun u ::
          (List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a))) v =
        mInt A (tupleOfList (e + 1) (LocPot.ofFun v ::
          (List.replicate j p ++ List.replicate k q ++ List.replicate (e + 1 - j - 1 - k) a))) u := by
    intro k j hkj
    have hL : ∀ x ∈ List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a,
        IsPotential A x :=
      pot_append A (pot_append A (pot_replicate A hq k) (pot_replicate A hp j)) (pot_replicate A ha _)
    have h1 := byPartsSymm A u v hu hv _ (isPotential_tupleOfList (n := e) A hL)
    rw [tupleOfList_cons, ← h1, ← tupleOfList_cons, show e + 1 - j - 1 - k = e + 1 - k - 1 - j by omega]
    refine mInt_perm A (List.Perm.cons _ (List.perm_append_comm.append_right _)) ?_ u
    simp only [List.length_cons, List.length_append, List.length_replicate]
    omega
  have lin : ∀ L : List (LocPot X), (∀ x ∈ L, IsPotential A x) →
      mInt A (tupleOfList (e + 1) L) (fun z => u z - v z) =
        mInt A (tupleOfList (e + 1) L) u - mInt A (tupleOfList (e + 1) L) v := by
    intro L hL
    have hΦ := isPotential_tupleOfList (n := e + 1) A hL
    have h := mIntLinear A _ hΦ (-1) v u (mIntegrableCont A _ hΦ v cv)
      (mIntegrableCont A _ hΦ u cu)
    have hfun : (fun z => u z - v z) = fun z => -1 * v z + u z := by
      funext z
      ring
    rw [hfun, h]
    ring
  have S5 : ∑ k ∈ range (e + 1 + 1),
      mInt A (tupleOfList (e + 1) (List.replicate k p ++ List.replicate (e + 1 - k) q)) v =
      ∑ k ∈ range (e + 1 + 1),
      mInt A (tupleOfList (e + 1) (List.replicate k q ++ List.replicate (e + 1 - k) p)) v := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [show e + 1 + 1 - 1 - k = e + 1 - k by omega, show e + 1 - (e + 1 - k) = k by omega]
    refine mInt_perm A List.perm_append_comm ?_ v
    simp only [List.length_append, List.length_replicate]
    omega
  have T : ∑ k ∈ range (e + 1 + 1), ∑ j ∈ range (e + 1 - k),
      mInt A (tupleOfList (e + 1) (LocPot.ofFun u ::
        (List.replicate k q ++ List.replicate j p ++ List.replicate (e + 1 - k - 1 - j) a))) v =
      ∑ k ∈ range (e + 1 + 1), ∑ j ∈ range (e + 1 - k),
      mInt A (tupleOfList (e + 1) (LocPot.ofFun v ::
        (List.replicate k p ++ List.replicate j q ++ List.replicate (e + 1 - k - 1 - j) a))) u := by
    refine Eq.trans ?_ (dsum_swap (e + 1) (fun k j => mInt A (tupleOfList (e + 1) (LocPot.ofFun v ::
        (List.replicate k p ++ List.replicate j q ++ List.replicate (e + 1 - k - 1 - j) a))) u)).symm
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun j hj => ?_
    rw [mem_range] at hk hj
    exact S3 k j (by omega)
  rw [Finset.sum_congr rfl fun k _ => lin _ (pot_append A (pot_replicate A hp k)
      (pot_replicate A hq _)), Finset.sum_sub_distrib, S5, Finset.sum_congr rfl S1,
    Finset.sum_congr rfl S2, Finset.sum_add_distrib, Finset.sum_add_distrib, T]
  ring

/- English proof (translation)
Rewrite using `[Subsingleton.elim Ψ Φ, Subsingleton.elim Θ Φ]`. Establish `hΦ : ∀ i, IsPotential A (Φ i)` using `fun i => i.elim0`. Establish `h` using `mIntLinear A Φ hΦ (-1) v u (mIntegrableCont A Φ hΦ v cv) (mIntegrableCont A Φ hΦ u cu)`. Establish `hfun : (fun z => u z - v z) = fun z => -1 * v z + u z`. Use function extensionality and compare the values at `z`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zero_case (A : FinHolAtlas 0 X) (Φ Ψ Θ : Fin 0 → LocPot X) {u v : X → ℝ}
    (cu : Continuous u) (cv : Continuous v) :
    mInt A Φ u - mInt A Ψ v = mInt A Θ (fun z => u z - v z) := by
  rw [Subsingleton.elim Ψ Φ, Subsingleton.elim Θ Φ]
  have hΦ : ∀ i, IsPotential A (Φ i) := fun i => i.elim0
  have h := mIntLinear A Φ hΦ (-1) v u (mIntegrableCont A Φ hΦ v cv) (mIntegrableCont A Φ hΦ u cu)
  have hfun : (fun z => u z - v z) = fun z => -1 * v z + u z := by
    funext z
    ring
  rw [hfun, h]
  ring

end WeightCocycle

section Family

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

/- English proof (translation)
The claim follows from `st_smooth_sum A Finset.univ fun i => st_smooth_mul A (st_smooth_const A (x (some i))) ((F.sys i).smooth t ht.1 (ht.2 i))`.
-/
theorem Family.coefWeight_smooth (F : Family A) (x : Option (Fin F.m) → ℝ) {t : ℝ}
    (ht : F.Admissible t) : A.Smooth (F.coefWeight x t) :=
  st_smooth_sum A Finset.univ fun i =>
    st_smooth_mul A (st_smooth_const A (x (some i))) ((F.sys i).smooth t ht.1 (ht.2 i))

/- English proof (translation)
The claim follows from `isPotentialAdd A _ _ (isPotential_lincomb _ _ _ fun i => (F.R i).θ_pot) (isPotentialRsmul A _ a ha)`.
-/
theorem Family.coefRefForm_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) : IsPotential A (F.coefRefForm a x) :=
  isPotentialAdd A _ _ (isPotential_lincomb _ _ _ fun i => (F.R i).θ_pot)
    (isPotentialRsmul A _ a ha)

/- English proof (translation)
Simplify using `only [Family.coefForm, Family.coefRefForm, Family.coefWeight, Family.chernForm, locPot_add_φ, lincomb_φ, LocPot.rsmul, LocPot.ofFun, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Family.coefForm_φ (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ)
    (z y : X) : (F.coefForm a x t).φ z y = (F.coefRefForm a x).φ z y + F.coefWeight x t y := by
  simp only [Family.coefForm, Family.coefRefForm, Family.coefWeight, Family.chernForm, locPot_add_φ,
    lincomb_φ, LocPot.rsmul, LocPot.ofFun, mul_add, Finset.sum_add_distrib]
  ring

end Family

open WeightCocycle in
/- English proof (translation)
Introduce `X _ _ _ D A F a ha x t t' ht ht'`. Establish `hu` using `F.coefWeight_smooth x ht`. Establish `hv` using `F.coefWeight_smooth x ht'`. Consider the cases of `D with`. Consider the case `zero`.

Simplify using `only [Family.weightEnergy, zero_add, Finset.sum_range_one]`. Conclude with `zero_case A _ _ _ (st_smooth_continuous A hu) (st_smooth_continuous A hv)`. Consider the case `succ e`. Establish `key` using `core A (F.coefRefForm a x) (F.coefForm a x t) (F.coefForm a x t') (F.coefWeight x t) (F.coefWeight x t') (F.coefRefForm_isPotential ha x) (F.coefForm_isPotential ha x ht) (F.coefForm_isPotential ha x ht') hu hv (F.coefForm_φ a x t) (F.coefForm_φ a x t')`. Establish `e1 : ∀ s : ℝ, F.Admissible s → F.weightEnergy a x s = ∑ k ∈ range (e + 1 + 1), mInt A (tupleOfList (e + 1) (List.replicate k (F.coefForm a x s) ++ List.replicate (e + 1 - k) (F.coefRefForm a x))) (F.coefWeight x s)`.

Introduce `s _`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[mem_range]`. Rewrite using `[ite_eq_tupleOfList_replicate _ _ (by omega)]`. Establish `e2 : ∀ k ∈ range (e + 1 + 1), mInt A (F.mixedProduct a x t t' k) (fun p => F.coefWeight x t p - F.coefWeight x t' p) = mInt A (tupleOfList (e + 1) (List.replicate k (F.coefForm a x t) ++ List.replicate (e + 1 - k) (F.coefForm a x t'))) (fun p => F.coefWeight x t p - F.coefWeight …`.

Introduce `k hk`. Rewrite `hk` using `[mem_range]`. Unfold `Family.mixedProduct`. Rewrite using `[ite_eq_tupleOfList_replicate _ _ (by omega)]`. Rewrite using `[e1 t ht, e1 t' ht', Finset.sum_congr rfl e2]`.

Conclude with `key`.
-/
theorem WeightCocycle.proof : WeightCocycle.Statement := by
  intro X _ _ _ D A F a ha x t t' ht ht'
  have hu := F.coefWeight_smooth x ht
  have hv := F.coefWeight_smooth x ht'
  cases D with
  | zero =>
    simp only [Family.weightEnergy, zero_add, Finset.sum_range_one]
    exact zero_case A _ _ _ (st_smooth_continuous A hu) (st_smooth_continuous A hv)
  | succ e =>
    have key := core A (F.coefRefForm a x) (F.coefForm a x t) (F.coefForm a x t')
      (F.coefWeight x t) (F.coefWeight x t') (F.coefRefForm_isPotential ha x)
      (F.coefForm_isPotential ha x ht) (F.coefForm_isPotential ha x ht') hu hv
      (F.coefForm_φ a x t) (F.coefForm_φ a x t')
    have e1 : ∀ s : ℝ, F.Admissible s → F.weightEnergy a x s = ∑ k ∈ range (e + 1 + 1),
        mInt A (tupleOfList (e + 1) (List.replicate k (F.coefForm a x s) ++
          List.replicate (e + 1 - k) (F.coefRefForm a x))) (F.coefWeight x s) := by
      intro s _
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [ite_eq_tupleOfList_replicate _ _ (by omega)]
    have e2 : ∀ k ∈ range (e + 1 + 1), mInt A (F.mixedProduct a x t t' k)
        (fun p => F.coefWeight x t p - F.coefWeight x t' p) =
        mInt A (tupleOfList (e + 1) (List.replicate k (F.coefForm a x t) ++
          List.replicate (e + 1 - k) (F.coefForm a x t'))) (fun p => F.coefWeight x t p - F.coefWeight x t' p) := by
      intro k hk
      rw [mem_range] at hk
      unfold Family.mixedProduct
      rw [ite_eq_tupleOfList_replicate _ _ (by omega)]
    rw [e1 t ht, e1 t' ht', Finset.sum_congr rfl e2]
    exact key

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
