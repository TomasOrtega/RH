import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `a b ha hb hbp`. Establish `hj : a.val + 1 < n` using `by have := b.isLt; omega`.

Establish `hb' : b = ⟨a.val + 1, hj⟩` using `Fin.ext (by simpa using hb)`. Rewrite using `[hb']; exact h a hj ha (by omega)`. Consider the case `succ d ih`. Introduce `a b ha hb hbp`. Establish `hc : a.val + d + 1 < n` using `by have := b.isLt; omega`.

Establish `hcb : (⟨a.val + d + 1, hc⟩ : Fin n).val + 1 < n` using `by have := b.isLt; simp only; omega`. Establish `hb' : b = ⟨(⟨a.val + d + 1, hc⟩ : Fin n).val + 1, hcb⟩` using `Fin.ext (by simp only; omega)`. Establish `h1 : permY K (Equiv.swap a ⟨a.val + d + 1, hc⟩) u = - u` using `ih a ⟨a.val + d + 1, hc⟩ ha rfl (by simp only; omega)`. Establish `h2 : permY K (Equiv.swap ⟨a.val + d + 1, hc⟩ b) u = - u`. Rewrite using `[hb']; exact h ⟨a.val + d + 1, hc⟩ hcb (by simp only; omega) (by simp only; omega)`.

Establish `hac : a ≠ ⟨a.val + d + 1, hc⟩`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.

Establish `hab : a ≠ b`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e : Equiv.swap a b = Equiv.swap ⟨a.val + d + 1, hc⟩ b * Equiv.swap a ⟨a.val + d + 1, hc⟩ * Equiv.swap ⟨a.val + d + 1, hc⟩ b`.

Rewrite using `[Equiv.swap_mul_swap_mul_swap hac hab, Equiv.swap_comm]`. Rewrite using `[e, permOnTensor_mul, permOnTensor_mul]`. Simplify using `only [Module.End.mul_apply, h1, h2, map_neg, neg_neg]`.
-/
theorem lcb_transp {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] {n : ℕ} (i p : ℕ) (u : Tens R P M n)
    (h : ∀ (j : Fin n) (hj : j.val + 1 < n), i ≤ j.val → j.val < i + p →
      permY K (Equiv.swap j ⟨j.val + 1, hj⟩) u = - u) :
    ∀ (d : ℕ) (a b : Fin n), i ≤ a.val → b.val = a.val + d + 1 → b.val ≤ i + p →
      permY K (Equiv.swap a b) u = - u := by
  intro d
  induction d with
  | zero =>
    intro a b ha hb hbp
    have hj : a.val + 1 < n := by have := b.isLt; omega
    have hb' : b = ⟨a.val + 1, hj⟩ := Fin.ext (by simpa using hb)
    rw [hb']; exact h a hj ha (by omega)
  | succ d ih =>
    intro a b ha hb hbp
    have hc : a.val + d + 1 < n := by have := b.isLt; omega
    have hcb : (⟨a.val + d + 1, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d + 1, hc⟩ : Fin n).val + 1, hcb⟩ := Fin.ext (by simp only; omega)
    have h1 : permY K (Equiv.swap a ⟨a.val + d + 1, hc⟩) u = - u := ih a ⟨a.val + d + 1, hc⟩ ha rfl (by simp only; omega)
    have h2 : permY K (Equiv.swap ⟨a.val + d + 1, hc⟩ b) u = - u := by
      rw [hb']; exact h ⟨a.val + d + 1, hc⟩ hcb (by simp only; omega) (by simp only; omega)
    have hac : a ≠ ⟨a.val + d + 1, hc⟩ := by
      intro e; have := congrArg Fin.val e; simp only at this; omega
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; omega
    have e : Equiv.swap a b = Equiv.swap ⟨a.val + d + 1, hc⟩ b * Equiv.swap a ⟨a.val + d + 1, hc⟩ *
        Equiv.swap ⟨a.val + d + 1, hc⟩ b := by
      rw [Equiv.swap_mul_swap_mul_swap hac hab, Equiv.swap_comm]
    rw [e, permOnTensor_mul, permOnTensor_mul]
    simp only [Module.End.mul_apply, h1, h2, map_neg, neg_neg]

/- English proof (translation)
Introduce `K R P M _ _ _ _ _ _ _ _ n i hi u h`. Establish `htr` using `lcb_transp (K := K) i (Fintype.card P) u h`. Establish `hex : ∀ x : Fin n → P, ∃ ab : Fin n × Fin n, i ≤ ab.1.val ∧ ab.1.val < ab.2.val ∧ ab.2.val ≤ i + Fintype.card P ∧ x ab.1 = x ab.2`. Introduce `x`. Establish `hcard : Fintype.card P < Fintype.card (Fin (Fintype.card P + 1))` using `by simp`.

Take `⟨s, t, hst, hx⟩` from `Fintype.exists_ne_map_eq_of_card_lt (fun s : Fin (Fintype.card P + 1) => x ⟨i + s.val, by have := s.isLt; omega⟩) hcard`. Establish `hs` using `s.isLt`. Establish `ht` using `t.isLt`. Establish `hst' : s.val ≠ t.val` using `fun e => hst (Fin.ext e)`. Break down `lt_or_gt_of_ne hst' with hlt | hlt` into its components or cases.

Conclude with `⟨(⟨i + s.val, by omega⟩, ⟨i + t.val, by omega⟩), by simp only; omega, by simp only; omega, by simp only; omega, hx⟩`. Conclude with `⟨(⟨i + t.val, by omega⟩, ⟨i + s.val, by omega⟩), by simp only; omega, by simp only; omega, by simp only; omega, hx.symm⟩`. Use `choose pr hpr using hex`. Use function extensionality and compare the values at `m`. Rewrite using `[toSym_apply_sum_fiber]`.

Set `xs : (Fin n → R × P) → Fin n → P` to `fun g s => (g s).2`. Set `inv : (Fin n → R × P) → (Fin n → R × P)` to `fun g => g ∘ Equiv.swap (pr (xs g)).1 (pr (xs g)).2`. Establish `hxs : ∀ g, xs (inv g) = xs g`. Introduce `g`. Use function extensionality and compare the values at `s`.

Take `⟨_, _, _, h4⟩` from `hpr (xs g)`. Use `show (g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).2 = (g s).2`. Distinguish the cases in `hs1 : s = (pr (xs g)).1`. Rewrite using `[hs1, Equiv.swap_apply_left]`. Conclude with `h4.symm`.

Distinguish the cases in `hs2 : s = (pr (xs g)).2`. Rewrite using `[hs2, Equiv.swap_apply_right]`. Conclude with `h4`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hs1 hs2]`. Establish `hu : ∀ g, u g + u (inv g) = 0`.

Introduce `g`. Take `⟨h1, h2, h3, h4⟩` from `hpr (xs g)`. Establish `key` using `congrFun (htr ((pr (xs g)).2.val - (pr (xs g)).1.val - 1) (pr (xs g)).1 (pr (xs g)).2 h1 (by omega) h3) g`. Rewrite `key` using `[permSecond_apply]`. Establish `e : (fun s => ((g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).1, (g s).2)) = inv g`.

Use function extensionality and compare the values at `s`. Use `congrFun (hxs g) s` as an intermediate fact. Conclude with `Prod.ext rfl this.symm`. Rewrite `key` using `[e]`. Rewrite using `[key]`.

Simplify using the standard rewrite rules. Use `show _ = (0 : M)`. Use `Finset.sum_involution (fun g _ => inv g) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `g _`. Conclude with `hu g`.

Introduce `g _ hne heq`. Apply `hne` to reduce the goal to its premises. Establish `h0` using `hu g`. Rewrite `h0` using `[heq]`. Establish `h2 : (2 : K) • u g = 0` using `by rw [two_smul]; exact h0`.

Conclude with `(smul_eq_zero.mp h2).resolve_left two_ne_zero`. Introduce `g hg`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢`. Use `show cont (g ∘ _) = m`. Rewrite using `[content_comp_perm_eq]`.

Conclude with `hg`. Introduce `g _ show (inv g) ∘ Equiv.swap (pr (xs (inv g))).1 (pr (xs (inv g))).2 = g`. Rewrite using `[hxs g]`. Use function extensionality and compare the values at `s`. Simplify using `[inv]`.
-/
theorem antitone_shapes : Anti := by
  intro K R P M _ _ _ _ _ _ _ _ n i hi u h
  classical
  have htr := lcb_transp (K := K) i (Fintype.card P) u h
  have hex : ∀ x : Fin n → P, ∃ ab : Fin n × Fin n, i ≤ ab.1.val ∧ ab.1.val < ab.2.val ∧
      ab.2.val ≤ i + Fintype.card P ∧ x ab.1 = x ab.2 := by
    intro x
    have hcard : Fintype.card P < Fintype.card (Fin (Fintype.card P + 1)) := by simp
    obtain ⟨s, t, hst, hx⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun s : Fin (Fintype.card P + 1) => x ⟨i + s.val, by have := s.isLt; omega⟩) hcard
    have hs := s.isLt
    have ht := t.isLt
    have hst' : s.val ≠ t.val := fun e => hst (Fin.ext e)
    rcases lt_or_gt_of_ne hst' with hlt | hlt
    · exact ⟨(⟨i + s.val, by omega⟩, ⟨i + t.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx⟩
    · exact ⟨(⟨i + t.val, by omega⟩, ⟨i + s.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx.symm⟩
  choose pr hpr using hex
  funext m
  rw [toSym_apply_sum_fiber]
  let xs : (Fin n → R × P) → Fin n → P := fun g s => (g s).2
  let inv : (Fin n → R × P) → (Fin n → R × P) := fun g => g ∘ Equiv.swap (pr (xs g)).1 (pr (xs g)).2
  have hxs : ∀ g, xs (inv g) = xs g := by
    intro g; funext s
    obtain ⟨_, _, _, h4⟩ := hpr (xs g)
    show (g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).2 = (g s).2
    by_cases hs1 : s = (pr (xs g)).1
    · rw [hs1, Equiv.swap_apply_left]; exact h4.symm
    · by_cases hs2 : s = (pr (xs g)).2
      · rw [hs2, Equiv.swap_apply_right]; exact h4
      · rw [Equiv.swap_apply_of_ne_of_ne hs1 hs2]
  have hu : ∀ g, u g + u (inv g) = 0 := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hpr (xs g)
    have key := congrFun (htr ((pr (xs g)).2.val - (pr (xs g)).1.val - 1) (pr (xs g)).1 (pr (xs g)).2 h1
      (by omega) h3) g
    rw [permSecond_apply] at key
    have e : (fun s => ((g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).1, (g s).2)) = inv g := by
      funext s
      have := congrFun (hxs g) s
      exact Prod.ext rfl this.symm
    rw [e] at key
    rw [key]; simp
  show _ = (0 : M)
  refine Finset.sum_involution (fun g _ => inv g) ?_ ?_ ?_ ?_
  · intro g _; exact hu g
  · intro g _ hne heq
    apply hne
    have h0 := hu g
    rw [heq] at h0
    have h2 : (2 : K) • u g = 0 := by rw [two_smul]; exact h0
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    show cont (g ∘ _) = m
    rw [content_comp_perm_eq]; exact hg
  · intro g _
    show (inv g) ∘ Equiv.swap (pr (xs (inv g))).1 (pr (xs (inv g))).2 = g
    rw [hxs g]
    funext s
    simp [inv]

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro a b hb; have : a = b := Fin.ext (by omega); rw [this]`. Consider the case `succ d ih`. Introduce `a b hb`.

Establish `hc : a.val + d < n` using `by have := b.isLt; omega`. Establish `hc' : (⟨a.val + d, hc⟩ : Fin n).val + 1 < n` using `by have := b.isLt; simp only; omega`. Establish `hb' : b = ⟨(⟨a.val + d, hc⟩ : Fin n).val + 1, hc'⟩` using `Fin.ext (by simp only; omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lcb_mono {n : ℕ} (col : Fin n → ℕ) (h : ∀ (j : Fin n) (hj : j.val + 1 < n), col j ≤ col ⟨j.val + 1, hj⟩) :
    ∀ (d : ℕ) (a b : Fin n), b.val = a.val + d → col a ≤ col b := by
  intro d
  induction d with
  | zero => intro a b hb; have : a = b := Fin.ext (by omega); rw [this]
  | succ d ih =>
    intro a b hb
    have hc : a.val + d < n := by have := b.isLt; omega
    have hc' : (⟨a.val + d, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d, hc⟩ : Fin n).val + 1, hc'⟩ := Fin.ext (by simp only; omega)
    calc col a ≤ col ⟨a.val + d, hc⟩ := ih a _ rfl
      _ ≤ col b := by rw [hb']; exact h _ hc'

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ h`. Rewrite `h` using `[hp.start]`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ m ih`. Introduce `hm h`. Distinguish the cases in `h' : j0 < κ m a`. Conclude with `ih (by omega) h'`. Establish `hs` using `hp.step ⟨m, by omega⟩`.

Establish `hs' : κ (m + 1) a = κ m a + (Pi.single (ρ ⟨m, by omega⟩) 1 : Fin q → ℕ) a`. Use `congrFun hs a` as an intermediate fact. Simplify using `using this`. Distinguish the cases in `hr : ρ ⟨m, by omega⟩ = a`. Use `⟨⟨m, by omega⟩, hr, ?_⟩` and prove the remaining obligations.

Rewrite `hs'` using `[hr, Pi.single_eq_same]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite `hs'` using `[Pi.single_eq_of_ne (Ne.symm hr)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lcb_ivt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (hp : IsPath n lam2 tau κ ρ) (a : Fin q) (j0 : ℕ) (h0 : lam2 a ≤ j0) :
    ∀ m ≤ n, j0 < κ m a → ∃ l : Fin n, ρ l = a ∧ κ l.val a = j0 := by
  intro m
  induction m with
  | zero => intro _ h; rw [hp.start] at h; omega
  | succ m ih =>
    intro hm h
    by_cases h' : j0 < κ m a
    · exact ih (by omega) h'
    · have hs := hp.step ⟨m, by omega⟩
      have hs' : κ (m + 1) a = κ m a + (Pi.single (ρ ⟨m, by omega⟩) 1 : Fin q → ℕ) a := by
        have := congrFun hs a; simpa using this
      by_cases hr : ρ ⟨m, by omega⟩ = a
      · refine ⟨⟨m, by omega⟩, hr, ?_⟩
        rw [hr, Pi.single_eq_same] at hs'
        simp only; omega
      · rw [Pi.single_eq_of_ne (Ne.symm hr)] at hs'
        omega

/- English proof (translation)
Introduce `q n lam2 tau κ ρ hp hmono p j0 hlen`. Unfold `LD.colLen at hlen`. Use `set S : Finset (Fin n) := Finset.univ.filter (fun l => colSeq κ ρ l = j0) with hS`. Establish `hmem : ∀ l, l ∈ S ↔ colSeq κ ρ l = j0`. Introduce `l`.

Simplify using `[hS]`. Establish `hsub : (Finset.univ.filter fun a : Fin q => lam2 a ≤ j0 ∧ j0 < tau a) ⊆ S.image ρ`. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Take `⟨l, hl1, hl2⟩` from `lcb_ivt hp a j0 ha.1 n le_rfl (by rw [hp.stop]; exact ha.2)`.

Use `Finset.mem_image.mpr ⟨l, ?_, hl1⟩` and prove the remaining obligations. Rewrite using `[hmem]`. Unfold `colSeq`. Rewrite using `[hl1]`. Conclude with `hl2`.

Establish `hcard : p < S.card`. Combine the equalities or inequalities in the displayed calculation. Establish `hne : S.Nonempty` using `Finset.card_pos.mp (by omega)`. Establish `hi : colSeq κ ρ (S.min' hne) = j0` using `(hmem _).mp (Finset.min'_mem S hne)`. Establish `hi' : colSeq κ ρ (S.max' hne) = j0` using `(hmem _).mp (Finset.max'_mem S hne)`.

Establish `hIcc : S ⊆ Finset.Icc (S.min' hne) (S.max' hne)` using `fun l hl => Finset.mem_Icc.mpr ⟨Finset.min'_le S l hl, Finset.le_max' S l hl⟩`. Establish `hc2 : S.card ≤ (S.max' hne).val + 1 - (S.min' hne).val`. Use `Finset.card_le_card hIcc` as an intermediate fact. Rewrite `this` using `[Fin.card_Icc]`. Then use the resulting hypothesis. Use `⟨(S.min' hne).val, by have := (S.max' hne).isLt; omega, fun l h1 h2 => ?_⟩` and prove the remaining obligations.

Establish `m1` using `lcb_mono _ hmono (l.val - (S.min' hne).val) (S.min' hne) l (by omega)`. Establish `m2` using `lcb_mono _ hmono ((S.max' hne).val - l.val) l (S.max' hne) (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem monotone_run : MonoRun := by
  intro q n lam2 tau κ ρ hp hmono p j0 hlen
  classical
  unfold LD.colLen at hlen
  set S : Finset (Fin n) := Finset.univ.filter (fun l => colSeq κ ρ l = j0) with hS
  have hmem : ∀ l, l ∈ S ↔ colSeq κ ρ l = j0 := by
    intro l; simp [hS]
  have hsub : (Finset.univ.filter fun a : Fin q => lam2 a ≤ j0 ∧ j0 < tau a) ⊆ S.image ρ := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨l, hl1, hl2⟩ := lcb_ivt hp a j0 ha.1 n le_rfl (by rw [hp.stop]; exact ha.2)
    refine Finset.mem_image.mpr ⟨l, ?_, hl1⟩
    rw [hmem]
    unfold colSeq
    rw [hl1]; exact hl2
  have hcard : p < S.card := by
    calc p < _ := hlen
      _ ≤ (S.image ρ).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hi : colSeq κ ρ (S.min' hne) = j0 := (hmem _).mp (Finset.min'_mem S hne)
  have hi' : colSeq κ ρ (S.max' hne) = j0 := (hmem _).mp (Finset.max'_mem S hne)
  have hIcc : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := fun l hl =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S l hl, Finset.le_max' S l hl⟩
  have hc2 : S.card ≤ (S.max' hne).val + 1 - (S.min' hne).val := by
    have := Finset.card_le_card hIcc
    rwa [Fin.card_Icc] at this
  refine ⟨(S.min' hne).val, by have := (S.max' hne).isLt; omega, fun l h1 h2 => ?_⟩
  have m1 := lcb_mono _ hmono (l.val - (S.min' hne).val) (S.min' hne) l (by omega)
  have m2 := lcb_mono _ hmono ((S.max' hne).val - l.val) l (S.max' hne) (by omega)
  omega

end Formalism.CohomologicalDescent.LC
