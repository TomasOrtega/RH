import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ProdSmulPowT
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightLatticeComparison
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Unfold `ex`. Rewrite using `[dif_pos s.2]`.
-/
theorem ex_val {n' : ℕ} {TT : Finset (Fin n')} (f : TT → ℕ) (s : TT) : ex f s.val = f s := by
  unfold ex
  rw [dif_pos s.2]

/- English proof (translation)
Establish `hl : (Fin.last m) ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Use function extensionality and compare the values at `i`. Establish `r0 : i.rev = 0 ↔ i = Fin.last m` using `by rw [← Fin.rev_last, Fin.rev_inj]`. Establish `rl : i.rev = Fin.last m ↔ i = 0` using `by rw [← Fin.rev_zero, Fin.rev_inj]`. Unfold `lamAt flatW wtPQ`. Distinguish the cases in `he : Even s.val.val`.

Simplify using `only [he, if_true, s.2, dite_true]`. Simplify using `only [he, if_false, s.2, dite_true, r0, rl]`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality. Simplify using `[hl.symm]`.

Distinguish the cases in `h1 : i = Fin.last m`. Substitute `h1` using the available equality. Simplify using `[hl]`. Simplify using `[h0, h1]`.
-/
theorem lamAt_flat_top {n' : ℕ} (m : ℕ) (hm : 1 ≤ m) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : TT) :
    lamAt (flatW m al be) s.val =
      wtPQ m (if Even s.val.val then al s else be s) (if Even s.val.val then be s else al s) := by
  have hl : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  funext i
  have r0 : i.rev = 0 ↔ i = Fin.last m := by rw [← Fin.rev_last, Fin.rev_inj]
  have rl : i.rev = Fin.last m ↔ i = 0 := by rw [← Fin.rev_zero, Fin.rev_inj]
  unfold lamAt flatW wtPQ
  by_cases he : Even s.val.val
  · simp only [he, if_true, s.2, dite_true]
  · simp only [he, if_false, s.2, dite_true, r0, rl]
    by_cases h0 : i = 0
    · subst h0
      simp [hl.symm]
    · by_cases h1 : i = Fin.last m
      · subst h1
        simp [hl]
      · simp [h0, h1]

/- English proof (translation)
Apply `tn_lamAt_zero` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `[flatW, hs]`.
-/
theorem lamAt_flat_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    lamAt (flatW m al be) s = 0 := by
  apply tn_lamAt_zero
  funext i
  simp [flatW, hs]

/- English proof (translation)
Introduce `p n' R m hm TT a A B hdeg`. Set `Ps : TT → ℕ` to `fun s => if Even s.val.val then A s else B s`. Set `Qs : TT → ℕ` to `fun s => if Even s.val.val then B s else A s`. Establish `hdeg' : ∀ s, Ps s + Qs s + 1 ≤ 8 * a` using `fun s => by`. Use `hdeg s` as an intermediate fact.

Simplify using `only [Ps, Qs]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hmin : ∀ s, min (Ps s) (Qs s) = min (A s) (B s)` using `fun s => by`. Simplify using `only [Ps, Qs]`. Use `split_ifs`.

Both sides reduce to the same expression. Conclude with `min_comm _ _`. Use `choose i1 pr1 hsum1 hrange1 hlat1 using fun s : TT => h p n' R m hm a (Ps s) (Qs s) (hdeg' s)`. Use `choose IO hIO using fun j : TT → ℕ => hIOe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => i1 s (j s))`. Use `choose PR hPR using fun j : TT → ℕ => hPRe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => pr1 s (j s))`.

Use `set Jf := Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)) with hJf`. Set `lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ` to `fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)`. Establish `hjle : ∀ j ∈ Jf, ∀ s, j s ≤ min (Ps s) (Qs s)` using `fun j hj s => by`. Rewrite using `[hmin]`. Conclude with `Nat.lt_succ_iff.1 (Finset.mem_range.1 ((Fintype.mem_piFinset.1 hj) s))`.

Establish `hwt : ∀ (j : TT → ℕ) (s : TT), lamAt (lamj j) s.val = wtPQ m (Ps s - j s) (Qs s - j s)` using `fun j s => by`. Rewrite using `[lamAt_flat_top m (by omega)]`. Simplify using `only [Ps, Qs]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hoff : ∀ (j : TT → ℕ) (s : Fin n'), s ∉ TT → lamAt (lamj j) s = 0` using `fun j s hs => lamAt_flat_off m _ _ s hs`.

Establish `hhh : ∀ (s : TT) (b : Bool), hhWt m TT (ex A) (ex B) (s, b) = letterWt m (if b then Ps s else Qs s) b`. Introduce `s b`. Unfold `hhWt hhDeg`. Apply the tactic sequence `cases b <;> simp [ex_val, Ps, Qs]`. Establish `hdom : ∀ j, IsDominant (lamj j)` using `fun j => flattened_weight_dominant m _ _`.

Establish `hVHH : VHH (m` using `m) R.Kf TT (ex A) (ex B) = tensorLat R.Kf R.Kf (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) := rfl`. Establish `htwoSp : ∀ s : TT, tensorLat R.Kf R.Kf (fun b : Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) (s, b)))) = twoSp R.Kf m (Ps s) (Qs s)` using `fun s => by`. Unfold `twoSp`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Rewrite using `[hhh]`. Establish `hioV : ∀ j ∈ Jf, ∀ y ∈ Vsp R.Kf (lamj j), IO j y ∈ VHH (m` using `m) R.Kf TT (ex A) (ex B) := by`. Introduce `j hj y hy`. Rewrite `hy` using `[Vsp_eq R.Kf _ (hdom j)]`. Use `ioMem (A := R.Kf) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j) _ (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1 (fun s y hy => by` as an intermediate fact.

Rewrite using `[one_smul, htwoSp]`. Rewrite `hy` using `[hwt]`. Conclude with `((hrange1 s (j s) (hjle j hj s)).2 y hy))`. Use the proof step `(fun s hs y hy => by`. Rewrite `hy` using `[hoff j s hs, nuOf_zero]`.

Conclude with `⟨_, tn_const _ _ y hy⟩) y hy`. Rewrite `this` using `[one_pow, one_smul]`. Conclude with `this`. Establish `hprV : ∀ j ∈ Jf, ∀ x ∈ VHH (m` using `m) R.Kf TT (ex A) (ex B), PR j x ∈ Vsp R.Kf (lamj j) := by`. Introduce `j hj x hx`.

Rewrite using `[Vsp_eq R.Kf _ (hdom j)]`. Use `prMem (A := R.Kf) TT (fun s => pr1 s (j s)) (PR j) (hPR j) (fun s => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt (lamj j) s))) (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1 (fun s x hx => by` as an intermediate fact. Rewrite using `[one_smul, hwt]`. Rewrite `hx` using `[htwoSp]`. Conclude with `((hrange1 s (j s) (hjle j hj s)).1 x hx))`.

Use the proof step `(fun s hs => by`. Rewrite using `[hoff j s hs, nuOf_zero]`. Conclude with `one_mem_dualWeyl _ _ _) x hx`. Rewrite `this` using `[one_pow, one_smul]`. Conclude with `this`.

Establish `hsumA : ∀ x ∈ VHH (m` using `m) R.Kf TT (ex A) (ex B), ∑ j ∈ Jf, IO j (PR j x) = x := by`. Introduce `x hx`. Rewrite `hx` using `[hVHH]`. Use `Submodule.span_induction (p := fun x _ => ∑ j ∈ Jf, IO j (PR j x) = x) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Rewrite using `[genRegroupT]`. Use `set Y : TT → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf := fun s => ∏ b, blockEmb R.Kf b (F (s, b)) with hY`. Establish `hYm : ∀ s, Y s ∈ twoSp R.Kf m (Ps s) (Qs s)` using `fun s => by`. Rewrite using `[← htwoSp]`. Conclude with `Submodule.subset_span ⟨fun b => F (s, b), fun b => hF _, rfl⟩`.

Establish `e1 : ∀ j, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) = ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (i1 s (j s) (pr1 s (j s) (Y s)))`. Introduce `j`. Rewrite using `[hPR j, prodTopsT TT (fun s => pr1 s (j s) (Y s))]`. Use `hIO j (fun s => if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1) (fun s hs => by rw [dif_neg hs])` as an intermediate fact. Rewrite using `[show (∏ s : Fin n', blockEmb R.Kf s (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)) = ∏ s : Fin n', rename (fun v => (s, v)) (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1) from rfl, this]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos s.2]`. Use `show ∑ j ∈ Jf, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) = ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s)`. Simplify using `only [e1]`. Rewrite using `[hJf, ← Finset.prod_univ_sum (fun s : TT => Finset.range (min (A s) (B s) + 1)) (fun s j => rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (i1 s j (pr1 s j (Y s))))]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← map_sum, ← hmin s, hsum1 s (Y s) (hYm s)]`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Simplify using `only [map_add, Finset.sum_add_distrib, hx, hy]`.

Introduce `c x _ hx`. Simplify using `only [map_smul]`. Rewrite using `[← Finset.smul_sum, hx]`. Use `⟨fun j => if hj : j ∈ Jf then LinearMap.codRestrict _ ((IO j).comp (Submodule.subtype _)) (fun y => hioV j hj y.1 y.2) else 0, fun j => if hj : j ∈ Jf then LinearMap.codRestrict _ ((PR j).comp (Submodule.subtype _)) (fun x => hprV j hj x.1 x.2) else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hsumA x.1 x.2]`. Rewrite using `[Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Simplify using `only [dif_pos hj]`.

Both sides reduce to the same expression. Introduce `M hM j hj`. Simplify using `only [dif_pos hj]`. Establish `hpow : (p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊) = ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) ^ TT.card` using `by rw [← pow_mul, mul_comm]`. Establish `htwoLat : ∀ s : TT, tensorLat R.O R.Kf (fun b : Bool => H0 R.O m (hhWt m TT (ex A) (ex B) (s, b)) (M s.val)) = twoLat R.O m (Ps s) (Qs s) (M s.val)` using `fun s => by`.

Unfold `twoLat`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[hhh]`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Use `prMem (A := R.O) TT (fun s => pr1 s (j s)) (PR j) (hPR j) (fun s => H0 R.O m (lamAt (lamj j) s) (M s)) (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val)) ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) (fun s x hx => by` as an intermediate fact. Rewrite using `[hwt]`. Rewrite `hx` using `[htwoLat]`. Conclude with `((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).1 x hx))`.

Use the proof step `(fun s hs => by`. Rewrite using `[hoff j s hs]`. Conclude with `(invariant_sections_zero_weight_iff m (M s) (hM s) 1).2 ⟨1, by simp⟩) x.1 hx`. Rewrite `this` using `[← hpow]`. Conclude with `this`.

Introduce `y hy`. Use `ioMem (A := R.O) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j) (fun s => H0 R.O m (lamAt (lamj j) s) (M s)) (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val)) ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) (fun s y hy => by` as an intermediate fact. Rewrite using `[htwoLat]`. Rewrite `hy` using `[hwt]`. Conclude with `((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).2 y hy))`.

Use the proof step `(fun s hs y hy => by`. Rewrite `hy` using `[hoff j s hs]`. Conclude with `(invariant_sections_zero_weight_iff m (M s) (hM s) y).1 hy) y.1 hy`. Rewrite `this` using `[← hpow]`. Conclude with `this`.
-/
theorem functor_comparison_of_single_weight (hIOe : ExistsIO) (hPRe : ExistsPR) (hK2 : RegroupP) (h : SingleWeightLatticeComparison) : LatticeFunctorComparison := by
  classical
  intro p n' R m hm TT a A B hdeg
  let Ps : TT → ℕ := fun s => if Even s.val.val then A s else B s
  let Qs : TT → ℕ := fun s => if Even s.val.val then B s else A s
  have hdeg' : ∀ s, Ps s + Qs s + 1 ≤ 8 * a := fun s => by
    have := hdeg s
    simp only [Ps, Qs]
    split_ifs <;> omega
  have hmin : ∀ s, min (Ps s) (Qs s) = min (A s) (B s) := fun s => by
    simp only [Ps, Qs]
    split_ifs
    · rfl
    · exact min_comm _ _
  choose i1 pr1 hsum1 hrange1 hlat1 using fun s : TT => h p n' R m hm a (Ps s) (Qs s) (hdeg' s)
  choose IO hIO using fun j : TT → ℕ =>
    hIOe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => i1 s (j s))
  choose PR hPR using fun j : TT → ℕ =>
    hPRe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => pr1 s (j s))
  set Jf := Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)) with hJf
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  have hjle : ∀ j ∈ Jf, ∀ s, j s ≤ min (Ps s) (Qs s) := fun j hj s => by
    rw [hmin]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 ((Fintype.mem_piFinset.1 hj) s))
  have hwt : ∀ (j : TT → ℕ) (s : TT), lamAt (lamj j) s.val = wtPQ m (Ps s - j s) (Qs s - j s) := fun j s => by
    rw [lamAt_flat_top m (by omega)]
    simp only [Ps, Qs]
    split_ifs <;> rfl
  have hoff : ∀ (j : TT → ℕ) (s : Fin n'), s ∉ TT → lamAt (lamj j) s = 0 := fun j s hs => lamAt_flat_off m _ _ s hs
  have hhh : ∀ (s : TT) (b : Bool), hhWt m TT (ex A) (ex B) (s, b) = letterWt m (if b then Ps s else Qs s) b := by
    intro s b
    unfold hhWt hhDeg
    cases b <;> simp [ex_val, Ps, Qs]
  have hdom : ∀ j, IsDominant (lamj j) := fun j => flattened_weight_dominant m _ _

  have hVHH : VHH (m := m) R.Kf TT (ex A) (ex B) = tensorLat R.Kf R.Kf
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) := rfl
  have htwoSp : ∀ s : TT, tensorLat R.Kf R.Kf
      (fun b : Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) (s, b)))) =
      twoSp R.Kf m (Ps s) (Qs s) := fun s => by
    unfold twoSp
    congr 1
    funext b
    rw [hhh]
  have hioV : ∀ j ∈ Jf, ∀ y ∈ Vsp R.Kf (lamj j), IO j y ∈ VHH (m := m) R.Kf TT (ex A) (ex B) := by
    intro j hj y hy
    rw [Vsp_eq R.Kf _ (hdom j)] at hy
    have := ioMem (A := R.Kf) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j) _
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1
      (fun s y hy => by
        rw [one_smul, htwoSp]
        rw [hwt] at hy
        exact ((hrange1 s (j s) (hjle j hj s)).2 y hy))
      (fun s hs y hy => by
        rw [hoff j s hs, nuOf_zero] at hy
        exact ⟨_, tn_const _ _ y hy⟩) y hy
    rw [one_pow, one_smul] at this
    exact this
  have hprV : ∀ j ∈ Jf, ∀ x ∈ VHH (m := m) R.Kf TT (ex A) (ex B), PR j x ∈ Vsp R.Kf (lamj j) := by
    intro j hj x hx
    rw [Vsp_eq R.Kf _ (hdom j)]
    have := prMem (A := R.Kf) TT (fun s => pr1 s (j s)) (PR j) (hPR j)
      (fun s => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt (lamj j) s)))
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1
      (fun s x hx => by
        rw [one_smul, hwt]
        rw [htwoSp] at hx
        exact ((hrange1 s (j s) (hjle j hj s)).1 x hx))
      (fun s hs => by
        rw [hoff j s hs, nuOf_zero]
        exact one_mem_dualWeyl _ _ _) x hx
    rw [one_pow, one_smul] at this
    exact this

  have hsumA : ∀ x ∈ VHH (m := m) R.Kf TT (ex A) (ex B), ∑ j ∈ Jf, IO j (PR j x) = x := by
    intro x hx
    rw [hVHH] at hx
    refine Submodule.span_induction (p := fun x _ => ∑ j ∈ Jf, IO j (PR j x) = x) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨F, hF, rfl⟩
      rw [genRegroupT]
      set Y : TT → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf :=
        fun s => ∏ b, blockEmb R.Kf b (F (s, b)) with hY
      have hYm : ∀ s, Y s ∈ twoSp R.Kf m (Ps s) (Qs s) := fun s => by
        rw [← htwoSp]
        exact Submodule.subset_span ⟨fun b => F (s, b), fun b => hF _, rfl⟩
      have e1 : ∀ j, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) =
          ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2))
            (i1 s (j s) (pr1 s (j s) (Y s))) := by
        intro j
        rw [hPR j, prodTopsT TT (fun s => pr1 s (j s) (Y s))]
        have := hIO j (fun s => if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)
          (fun s hs => by rw [dif_neg hs])
        rw [show (∏ s : Fin n', blockEmb R.Kf s (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)) =
          ∏ s : Fin n', rename (fun v => (s, v)) (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1) from rfl,
          this]
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [dif_pos s.2]
      show ∑ j ∈ Jf, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) =
        ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s)
      simp only [e1]
      rw [hJf, ← Finset.prod_univ_sum (fun s : TT => Finset.range (min (A s) (B s) + 1))
        (fun s j => rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (i1 s j (pr1 s j (Y s))))]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← map_sum, ← hmin s, hsum1 s (Y s) (hYm s)]
    · simp
    · intro x y _ _ hx hy
      simp only [map_add, Finset.sum_add_distrib, hx, hy]
    · intro c x _ hx
      simp only [map_smul]
      rw [← Finset.smul_sum, hx]
  refine ⟨fun j => if hj : j ∈ Jf then
      LinearMap.codRestrict _ ((IO j).comp (Submodule.subtype _)) (fun y => hioV j hj y.1 y.2) else 0,
    fun j => if hj : j ∈ Jf then
      LinearMap.codRestrict _ ((PR j).comp (Submodule.subtype _)) (fun x => hprV j hj x.1 x.2) else 0, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    rw [← hsumA x.1 x.2]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [dif_pos hj]
    rfl
  · intro M hM j hj
    simp only [dif_pos hj]
    have hpow : (p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊) =
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) ^ TT.card := by rw [← pow_mul, mul_comm]
    have htwoLat : ∀ s : TT, tensorLat R.O R.Kf
        (fun b : Bool => H0 R.O m (hhWt m TT (ex A) (ex B) (s, b)) (M s.val)) =
        twoLat R.O m (Ps s) (Qs s) (M s.val) := fun s => by
      unfold twoLat
      congr 1
      funext b
      rw [hhh]
    constructor
    · intro x hx
      have := prMem (A := R.O) TT (fun s => pr1 s (j s)) (PR j) (hPR j)
        (fun s => H0 R.O m (lamAt (lamj j) s) (M s))
        (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val))
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊)
        (fun s x hx => by
          rw [hwt]
          rw [htwoLat] at hx
          exact ((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).1 x hx))
        (fun s hs => by
          rw [hoff j s hs]
          exact (invariant_sections_zero_weight_iff m (M s) (hM s) 1).2 ⟨1, by simp⟩) x.1 hx
      rw [← hpow] at this
      exact this
    · intro y hy
      have := ioMem (A := R.O) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j)
        (fun s => H0 R.O m (lamAt (lamj j) s) (M s))
        (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val))
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊)
        (fun s y hy => by
          rw [htwoLat]
          rw [hwt] at hy
          exact ((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).2 y hy))
        (fun s hs y hy => by
          rw [hoff j s hs] at hy
          exact (invariant_sections_zero_weight_iff m (M s) (hM s) y).1 hy) y.1 hy
      rw [← hpow] at this
      exact this

end Formalism.MainNotions.flipOneThree.Pf

end
