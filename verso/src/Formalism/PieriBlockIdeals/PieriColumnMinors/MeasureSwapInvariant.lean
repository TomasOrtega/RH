import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
Introduce `K V J _ _ _ T TT E hE v hv t0 ht0 hv0`. Use `choose! tt htt1 htt2 using hE`. Take `⟨f, t, htE, -, hsum⟩` from `(Submodule.mem_span_iff_exists_finset_subset).1 hv`. Use `clear hv`. Proceed by induction on `t using Finset.induction_on generalizing f v with`.

Consider the case `empty => simpa using hsum.symm`. Consider the case `insert e0 t' he0 ih`. Establish `he0E : e0 ∈ E` using `htE (by simp)`. Establish `hne : tt e0 ≠ t0` using `fun h => ht0 (h ▸ htt1 e0 he0E)`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hne`.

Establish `h1 : (t0 j - tt e0 j) • v = ∑ a ∈ t', (f a * (tt a j - tt e0 j)) • a`. Establish `h3 : T j v - tt e0 j • v = ∑ a ∈ insert e0 t', f a • (T j a - tt e0 j • a)`. Rewrite using `[← hsum]`. Simplify using `only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]`. Use `congr 1`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Use `intros`. Rewrite using `[smul_comm]`. Rewrite using `[sub_smul, ← hv0 j, h3, Finset.sum_insert he0, htt2 e0 he0E j, sub_self, smul_zero, zero_add]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `a ha`. Rewrite using `[htt2 a (htE (by simp [ha])) j, ← sub_smul, smul_smul]`. Establish `h2` using `ih ((t0 j - tt e0 j) • v) (fun i => by rw [map_smul, hv0 i, smul_comm]) (fun a => f a * (tt a j - tt e0 j)) (fun a ha => htE (by simp at ha ⊢; exact Or.inr ha)) h1.symm`. Conclude with `(smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hj))`.
-/
theorem no_bad_tuple : NoTuple := by
  intro K V J _ _ _ T TT E hE v hv t0 ht0 hv0
  classical
  choose! tt htt1 htt2 using hE
  obtain ⟨f, t, htE, -, hsum⟩ := (Submodule.mem_span_iff_exists_finset_subset).1 hv
  clear hv
  induction t using Finset.induction_on generalizing f v with
  | empty => simpa using hsum.symm
  | insert e0 t' he0 ih =>
    have he0E : e0 ∈ E := htE (by simp)
    have hne : tt e0 ≠ t0 := fun h => ht0 (h ▸ htt1 e0 he0E)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have h1 : (t0 j - tt e0 j) • v = ∑ a ∈ t', (f a * (tt a j - tt e0 j)) • a := by
      have h3 : T j v - tt e0 j • v = ∑ a ∈ insert e0 t', f a • (T j a - tt e0 j • a) := by
        rw [← hsum]
        simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intros
        rw [smul_comm]
      rw [sub_smul, ← hv0 j, h3, Finset.sum_insert he0, htt2 e0 he0E j, sub_self, smul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro a ha
      rw [htt2 a (htE (by simp [ha])) j, ← sub_smul, smul_smul]
    have h2 := ih ((t0 j - tt e0 j) • v) (fun i => by rw [map_smul, hv0 i, smul_comm])
      (fun a => f a * (tt a j - tt e0 j)) (fun a ha => htE (by simp at ha ⊢; exact Or.inr ha)) h1.symm
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hj))

/- English proof (translation)
Introduce `n col j hj hlt`. Use `set b : Fin n := ⟨j.val + 1, hj⟩ with hb`. Establish `hjb : j ≠ b`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `[hb] at this`. Establish `hsplit : ∀ F : Fin n → ℕ, ∑ l, F l = F j + (F b + ∑ l ∈ (Finset.univ.erase j).erase b, F l)`. Introduce `F`. Rewrite using `[Finset.add_sum_erase _ F (by simp [hjb.symm]), Finset.add_sum_erase _ F (by simp)]`. Unfold `meas`.

Rewrite using `[hsplit, hsplit (fun l => (n - l.val) * col l)]`. Establish `hrest : ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * (col ∘ Equiv.swap j b) l = ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * col l`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [Finset.mem_erase, Finset.mem_univ, and_true] at hl`.

Simplify using `[Function.comp, Equiv.swap_apply_of_ne_of_ne hl.2 hl.1]`. Rewrite using `[hrest]`. Simplify using `only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Take `⟨w, hw⟩ : ∃ w, n - b.val = w` from `⟨_, rfl⟩`. Establish `hw' : n - j.val = w + 1`.

Establish `: b.val = j.val + 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hw, hw']`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem measure_swap_invariant : MeasSwap := by
  intro n col j hj hlt
  set b : Fin n := ⟨j.val + 1, hj⟩ with hb
  have hjb : j ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [hb] at this
  have hsplit : ∀ F : Fin n → ℕ, ∑ l, F l = F j + (F b + ∑ l ∈ (Finset.univ.erase j).erase b, F l) := by
    intro F
    rw [Finset.add_sum_erase _ F (by simp [hjb.symm]), Finset.add_sum_erase _ F (by simp)]
  unfold meas
  rw [hsplit, hsplit (fun l => (n - l.val) * col l)]
  have hrest : ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * (col ∘ Equiv.swap j b) l =
      ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * col l := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hl.2 hl.1]
  rw [hrest]
  simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  obtain ⟨w, hw⟩ : ∃ w, n - b.val = w := ⟨_, rfl⟩
  have hw' : n - j.val = w + 1 := by
    have : b.val = j.val + 1 := rfl
    omega
  rw [hw, hw']
  nlinarith

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ _ EM n lam2 hp tau ⟨b, j0, hj0, hcol⟩ z hz`. Establish `key : ∀ N : ℕ, ∀ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ → meas (colSeq κ ρ) = N → ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (cseq κ ρ) z → toSym K z = 0`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`.

Introduce `κ ρ hpath hN z hz`. Distinguish the cases in `hdesc : ∃ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j`. Take `⟨j, hj, hlt⟩` from `hdesc`. Take `⟨h2, κ', hpath', hc', hcol'⟩` from `hSwap q n lam2 tau κ ρ hpath j hj hlt`. Use `hGood K P M q EM n lam2 (cseq κ ρ) j hj h2 ?_ z hz` and prove the remaining obligations.

Introduce `z' hz'`. Rewrite `hz'` using `[← hc']`. Use `ih _ ?_ κ' _ hpath' rfl z' hz'` and prove the remaining obligations. Rewrite using `[hcol', ← hN]`. Conclude with `hMeas n _ j hj hlt`.

Use `push Not at hdesc`. Take `⟨i, hi, hrun⟩` from `hMono q n lam2 tau κ ρ hpath hdesc (Fintype.card P) j0 hcol`. Use `hAnti K (Fin q) P M n i hi z ?_` and prove the remaining obligations. Introduce `j hj h1 h2`. Establish `hc : colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j`.

Rewrite using `[hrun j h1 (by omega), hrun ⟨j.val + 1, hj⟩ (by simp only []; omega) (by simp only []; omega)]`. Take `⟨ha, hb⟩` from `hSame q n lam2 tau κ ρ hpath j hj hc`. Conclude with `hAntiStep K P M q EM n lam2 hp _ z j hj hz ha hb`. Establish `hle : PathSpace K (P` using `P) EM n lam2 tau ≤ LinearMap.ker (toSym K) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨κ, ρ, hpath, hy⟩`. Conclude with `LinearMap.mem_ker.2 (key _ κ ρ hpath rfl y ((hWt K P M q EM n lam2 κ ρ hpath.start hpath.step y).1 hy))`. Conclude with `LinearMap.mem_ker.1 (hle hz)`.
-/
theorem ColumnsFromPieri_of (hSwap : SwapPath) (hSame : SameCol) (hMeas : MeasSwap) (hMono : MonoRun)
    (hWt : WtIff) (hGood : GoodSwap) (hAntiStep : AntiStep) (hAnti : Anti) : ColumnsFromPieri := by
  intro K P M q _ _ _ _ _ _ EM n lam2 hp tau ⟨b, j0, hj0, hcol⟩ z hz
  have key : ∀ N : ℕ, ∀ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
      meas (colSeq κ ρ) = N → ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (cseq κ ρ) z → toSym K z = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro κ ρ hpath hN z hz
      by_cases hdesc : ∃ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j
      · obtain ⟨j, hj, hlt⟩ := hdesc
        obtain ⟨h2, κ', hpath', hc', hcol'⟩ := hSwap q n lam2 tau κ ρ hpath j hj hlt
        refine hGood K P M q EM n lam2 (cseq κ ρ) j hj h2 ?_ z hz
        intro z' hz'
        rw [← hc'] at hz'
        refine ih _ ?_ κ' _ hpath' rfl z' hz'
        rw [hcol', ← hN]
        exact hMeas n _ j hj hlt
      · push Not at hdesc
        obtain ⟨i, hi, hrun⟩ := hMono q n lam2 tau κ ρ hpath hdesc (Fintype.card P) j0 hcol
        refine hAnti K (Fin q) P M n i hi z ?_
        intro j hj h1 h2
        have hc : colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j := by
          rw [hrun j h1 (by omega), hrun ⟨j.val + 1, hj⟩ (by simp only []; omega) (by simp only []; omega)]
        obtain ⟨ha, hb⟩ := hSame q n lam2 tau κ ρ hpath j hj hc
        exact hAntiStep K P M q EM n lam2 hp _ z j hj hz ha hb
  have hle : PathSpace K (P := P) EM n lam2 tau ≤ LinearMap.ker (toSym K) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨κ, ρ, hpath, hy⟩
    exact LinearMap.mem_ker.2 (key _ κ ρ hpath rfl y ((hWt K P M q EM n lam2 κ ρ hpath.start hpath.step y).1 hy))
  exact LinearMap.mem_ker.1 (hle hz)

/- English proof (translation)
Introduce `O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL xi lam l e i' hl hu h1 h2 h3 h4 h5 h6 h7 h8 h9`. Conclude with `depth_skeleton_third_form_holds O K V P q S B n w lam2 DelL xi lam l e i' hl hu ⟨h1, h2, h3, h4, h5, h6, h7, h K P S.W q S.EW n lam2 h7, h8, h9⟩`.
-/
theorem LemmaDSkeleton4_of (h : ColumnsFromPieri) : LemmaDSkeleton4 := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL xi lam l e i' hl hu h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact depth_skeleton_third_form_holds O K V P q S B n w lam2 DelL xi lam l e i' hl hu
    ⟨h1, h2, h3, h4, h5, h6, h7, h K P S.W q S.EW n lam2 h7, h8, h9⟩

end Formalism.CohomologicalDescent.LC
