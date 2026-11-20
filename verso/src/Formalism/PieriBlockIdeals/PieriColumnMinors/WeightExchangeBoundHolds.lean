import Mathlib
import Formalism.PieriBlockIdeals.Statement

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

/- English proof (translation)
The claim follows from `|Bm.sum - Y.sum| ≤ (Multiset.card X : ℤ) * (hi - lo) := by subst hA have noMem : hi < lo → ∀ S : Multiset ℤ, (∀ a ∈ S, lo ≤ a ∧ a ≤ hi) → Multiset.card S = 0 := by intro hlt S hS by_contra hne obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne) have := h …`.
-/
theorem we_msum (Y A Bm X : Multiset ℤ) (lo hi : ℤ) (hYA : Y ≤ A) (hA : A = Bm + X)
    (hc : Multiset.card Y = Multiset.card Bm) (hin : ∀ a ∈ A, lo ≤ a ∧ a ≤ hi) :
    |Bm.sum - Y.sum| ≤ (Multiset.card X : ℤ) * (hi - lo) := by
  subst hA
  have noMem : hi < lo → ∀ S : Multiset ℤ, (∀ a ∈ S, lo ≤ a ∧ a ≤ hi) → Multiset.card S = 0 := by
    intro hlt S hS
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne)
    have := hS a ha
    omega
  have hP : Y - Bm ≤ X := Multiset.sub_le_iff_le_add.2 (by rw [add_comm]; exact hYA)
  have hYs : Y.sum = (Y - Bm).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.sum_add]
  have hBs : Bm.sum = (Bm - Y).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.sum_add, Multiset.inter_comm]
  have hYc : Multiset.card Y = Multiset.card (Y - Bm) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.card_add]
  have hBc : Multiset.card Bm = Multiset.card (Bm - Y) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.card_add, Multiset.inter_comm]
  have hPQ : Multiset.card (Y - Bm) = Multiset.card (Bm - Y) := by omega
  have memP : ∀ a ∈ Y - Bm, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_of_le hYA (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha))
  have memQ : ∀ a ∈ Bm - Y, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_add.2 (Or.inl (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)))
  have memX : ∀ a ∈ X, lo ≤ a ∧ a ≤ hi := fun a ha => hin a (Multiset.mem_add.2 (Or.inr ha))
  have P1 := Multiset.sum_le_card_nsmul (Y - Bm) hi (fun a ha => (memP a ha).2)
  have P2 : Multiset.card (Y - Bm) • lo ≤ (Y - Bm).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memP a ha).1)
  have Q1 := Multiset.sum_le_card_nsmul (Bm - Y) hi (fun a ha => (memQ a ha).2)
  have Q2 : Multiset.card (Bm - Y) • lo ≤ (Bm - Y).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memQ a ha).1)
  rw [hPQ] at P1 P2
  simp only [nsmul_eq_mul] at P1 P2 Q1 Q2
  have hm : (Multiset.card (Bm - Y) : ℤ) * (hi - lo) ≤ (Multiset.card X : ℤ) * (hi - lo) := by
    by_cases h : lo ≤ hi
    · apply mul_le_mul_of_nonneg_right _ (by linarith)
      have := Multiset.card_le_card hP
      rw [hPQ] at this
      exact_mod_cast this
    · push_neg at h
      rw [noMem h _ memQ, noMem h X memX]
  rw [hYs, hBs, abs_le]
  constructor <;> linarith

/- English proof (translation)
Introduce `l b t κ U kap hl htl hU hkap hle`. Establish `: NeZero l` using `⟨by omega⟩`. Establish `hlpos : (0 : ℤ) < (l : ℤ)` using `by exact_mod_cast hl`. Take `⟨lo, hlo⟩ : ∃ lo : ℤ, lo = b - (κ : ℤ)` from `⟨_, rfl⟩`. Take `⟨hi, hhi⟩ : ∃ hi : ℤ, hi = b + (t : ℤ) - 1 + (κ : ℤ)` from `⟨_, rfl⟩`.

Establish `hwin : hi < lo + l` using `by omega`. Take `⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ u, g u = lo + (u - lo) % (l : ℤ)` from `⟨_, fun _ => rfl⟩`. Establish `g_ge : ∀ u, lo ≤ g u` using `fun u => by`. Rewrite using `[hg]`. Use `Int.emod_nonneg (u - lo) hlpos.ne'` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `g_fix : ∀ v, lo ≤ v → v ≤ hi → g v = v` using `fun v h1 h2 => by`. Rewrite using `[hg, Int.emod_eq_of_lt (by linarith) (by linarith)]`. Expand and normalize the polynomial expressions, which then agree. Establish `g_mod : ∀ u, g u ≡ u [ZMOD (l : ℤ)]` using `fun u => by`.

Establish `h` using `(Int.mod_modEq (u - lo) (l : ℤ)).add_left lo`. Rewrite using `[hg]`. Rewrite `h` using `[show lo + (u - lo) = u by ring]`. Then use the resulting hypothesis. Establish `g_cong : ∀ u v, u ≡ v [ZMOD (l : ℤ)] → g u = g v` using `fun u v h => by`. Establish `e : (u - lo) % (l : ℤ) = (v - lo) % (l : ℤ)` using `Int.ModEq.sub_right lo h`.

Rewrite using `[hg, hg, e]`. Take `⟨ρ, hρ⟩ : ∃ ρ : ZMod l → ℤ, ∀ u : ℤ, ρ (u : ZMod l) = g u` from `⟨fun z => lo + ((z - (lo : ZMod l)).val : ℤ), fun u => by show lo + ((((u : ZMod l) - (lo : ZMod l))).val : ℤ) = g u`. Rewrite using `[← Int.cast_sub, ZMod.val_intCast, hg]⟩`. Establish `hvW : ∀ s : Fin t, lo ≤ b + ((s : ℕ) : ℤ) - kap s ∧ b + ((s : ℕ) : ℤ) - kap s ≤ hi` using `fun s => by`. Establish `h1` using `s.isLt`.

Establish `h2` using `abs_le.1 (hkap s)`. Use linear arithmetic over natural numbers and integers. Establish `hY : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤ Multiset.map g U.val`. Establish `h1` using `Multiset.map_le_map (f := ρ) hle`. Rewrite `h1` using `[Multiset.map_map, Multiset.map_map]`.

Use `Eq.trans_le (Multiset.map_congr rfl fun s _ => ?_) (h1.trans_eq (Multiset.map_congr rfl fun u _ => ?_))` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[hρ, g_fix _ (hvW s).1 (hvW s).2]`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hρ]`.

Establish `hYA : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤ Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val)`. Establish `hself : Multiset.filter (fun x => x ≤ hi) (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val) = Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val` using `Multiset.filter_eq_self.2 (fun a ha => by`. Rewrite `ha` using `[Multiset.mem_map]`. Take `⟨s, -, rfl⟩` from `ha`. Conclude with `(hvW s).2)`.

Rewrite using `[← hself]`. Conclude with `Multiset.filter_le_filter (p := fun x => x ≤ hi) hY`. Establish `hin : ∀ a ∈ Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val), lo ≤ a ∧ a ≤ hi`. Introduce `a ha`. Rewrite `ha` using `[Multiset.mem_filter, Multiset.mem_map]`.

Take `⟨⟨u, -, rfl⟩, h⟩` from `ha`. Conclude with `⟨g_ge u, h⟩`. Establish `hF : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) = Multiset.map g (Multiset.filter (fun u => g u ≤ hi) U.val)`. Rewrite using `[Multiset.filter_map]`. Conclude with `congrArg (Multiset.map g) (Multiset.filter_congr fun _ _ => Iff.rfl)`.

Establish `hfirst : Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1)) (Multiset.filter (fun u => g u ≤ hi) U.val) = Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val`. Establish `hinj : Function.Injective (fun s : Fin t => b + ((s : ℕ) : ℤ))`. Introduce `s1 s2 h`. Establish `h' : b + ((s1 : ℕ) : ℤ) = b + ((s2 : ℕ) : ℤ)` using `h`. Conclude with `Fin.ext (by omega)`.

Establish `hnd1 : (Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1)) (Multiset.filter (fun u => g u ≤ hi) U.val)).Nodup`. Apply `Multiset.Nodup.filter` to reduce the goal to its premises. Apply `Multiset.Nodup.filter` to reduce the goal to its premises. Conclude with `U.nodup`. Rewrite using `[Multiset.Nodup.ext hnd1 (Multiset.Nodup.map hinj (Finset.nodup _))]`.

Introduce `a`. Simplify using `only [Multiset.mem_filter, Finset.mem_val, Finset.mem_Icc, Multiset.mem_map, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, -⟩, h1, h2⟩`. Establish `hn` using `Int.toNat_of_nonneg (show 0 ≤ a - b by omega)`.

Use `⟨⟨(a - b).toNat, by omega⟩, ?_⟩` and prove the remaining obligations. Use `show b + (((a - b).toNat : ℕ) : ℤ) = a`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨s, rfl⟩`. Establish `hs` using `s.isLt`.

Use `⟨⟨hU s, ?_⟩, by omega, by omega⟩` and prove the remaining obligations. Rewrite using `[g_fix _ (by omega) (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `hA : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) = Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val + Multiset.map g (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1)) (Multiset.filter (fun u => g u ≤ hi) U.val))`. Rewrite using `[hF]`.

Use `conv_lhs => rw [← Multiset.filter_add_not (p := fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1)) (s := Multiset.filter (fun u => g u ≤ hi) U.val)]`. Rewrite using `[Multiset.map_add, hfirst, Multiset.map_map]`. Use `congr 1`. Conclude with `Multiset.map_congr rfl fun s _ => by`. Establish `hs` using `s.isLt`.

Simplify using `only [Function.comp_apply]`. Conclude with `g_fix _ (by omega) (by omega)`. Establish `hR : ∀ u, (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)), x ≡ u [ZMOD (l : ℤ)]) ↔ g u ≤ hi`. Introduce `u`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, hxu⟩`. Rewrite `hx` using `[Finset.mem_Icc]`. Rewrite using `[← g_cong x u hxu, g_fix x (by omega) (by omega)]`. Use linear arithmetic over natural numbers and integers. Introduce `hu`.

Conclude with `⟨g u, Finset.mem_Icc.2 ⟨by have := g_ge u; omega, by omega⟩, g_mod u⟩`. Establish `hcard : Multiset.card (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1)) (Multiset.filter (fun u => g u ≤ hi) U.val)) = mwCount l b t κ U`. Unfold `mwCount`. Rewrite using `[← Finset.card_val, Finset.filter_val, Finset.filter_val, Multiset.filter_filter, Multiset.filter_filter]`. Use `congr 1`.

Establish `e : Multiset.filter (fun a => a ∉ Finset.Icc b (b + (t : ℤ) - 1) ∧ g a ≤ hi) U.val = Multiset.filter (fun a => (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)), x ≡ a [ZMOD (l : ℤ)]) ∧ a ∉ Finset.Icc b (b + (t : ℤ) - 1)) U.val` using `Multiset.filter_congr (fun u _ => by rw [hR u]; exact and_comm)`. Use `e using 2` and compare the differences between its conclusion and the goal. Establish `key` using `we_msum _ _ _ _ lo hi hYA hA (by rw [Multiset.card_map, Multiset.card_map]) hin`. Rewrite `key` using `[Multiset.card_map, hcard]`. Establish `hBs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val).sum = ∑ s : Fin t, (b + ((s : ℕ) : ℤ))` using `(Finset.sum_eq_multiset_sum _ _).symm`.

Establish `hYs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val).sum = ∑ s : Fin t, (b + ((s : ℕ) : ℤ) - kap s)` using `(Finset.sum_eq_multiset_sum _ _).symm`. Rewrite `key` using `[hBs, hYs, Finset.sum_sub_distrib, sub_sub_cancel]`. Use `key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem shiftSumBound_holds : KapSum := by
  intro l b t κ U kap hl htl hU hkap hle
  have : NeZero l := ⟨by omega⟩
  have hlpos : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  obtain ⟨lo, hlo⟩ : ∃ lo : ℤ, lo = b - (κ : ℤ) := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : ℤ, hi = b + (t : ℤ) - 1 + (κ : ℤ) := ⟨_, rfl⟩
  have hwin : hi < lo + l := by omega
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ u, g u = lo + (u - lo) % (l : ℤ) := ⟨_, fun _ => rfl⟩
  have g_ge : ∀ u, lo ≤ g u := fun u => by
    rw [hg]
    have := Int.emod_nonneg (u - lo) hlpos.ne'
    linarith
  have g_fix : ∀ v, lo ≤ v → v ≤ hi → g v = v := fun v h1 h2 => by
    rw [hg, Int.emod_eq_of_lt (by linarith) (by linarith)]
    ring
  have g_mod : ∀ u, g u ≡ u [ZMOD (l : ℤ)] := fun u => by
    have h := (Int.mod_modEq (u - lo) (l : ℤ)).add_left lo
    rw [hg]
    rwa [show lo + (u - lo) = u by ring] at h
  have g_cong : ∀ u v, u ≡ v [ZMOD (l : ℤ)] → g u = g v := fun u v h => by
    have e : (u - lo) % (l : ℤ) = (v - lo) % (l : ℤ) := Int.ModEq.sub_right lo h
    rw [hg, hg, e]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ZMod l → ℤ, ∀ u : ℤ, ρ (u : ZMod l) = g u :=
    ⟨fun z => lo + ((z - (lo : ZMod l)).val : ℤ), fun u => by
      show lo + ((((u : ZMod l) - (lo : ZMod l))).val : ℤ) = g u
      rw [← Int.cast_sub, ZMod.val_intCast, hg]⟩
  have hvW : ∀ s : Fin t, lo ≤ b + ((s : ℕ) : ℤ) - kap s ∧ b + ((s : ℕ) : ℤ) - kap s ≤ hi :=
    fun s => by
      have h1 := s.isLt
      have h2 := abs_le.1 (hkap s)
      omega
  have hY : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.map g U.val := by
    have h1 := Multiset.map_le_map (f := ρ) hle
    rw [Multiset.map_map, Multiset.map_map] at h1
    refine Eq.trans_le (Multiset.map_congr rfl fun s _ => ?_)
      (h1.trans_eq (Multiset.map_congr rfl fun u _ => ?_))
    · simp only [Function.comp_apply]
      rw [hρ, g_fix _ (hvW s).1 (hvW s).2]
    · simp only [Function.comp_apply]
      rw [hρ]
  have hYA : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) := by
    have hself : Multiset.filter (fun x => x ≤ hi)
        (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val) =
        Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val :=
      Multiset.filter_eq_self.2 (fun a ha => by
        rw [Multiset.mem_map] at ha
        obtain ⟨s, -, rfl⟩ := ha
        exact (hvW s).2)
    rw [← hself]
    exact Multiset.filter_le_filter (p := fun x => x ≤ hi) hY
  have hin : ∀ a ∈ Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val), lo ≤ a ∧ a ≤ hi := by
    intro a ha
    rw [Multiset.mem_filter, Multiset.mem_map] at ha
    obtain ⟨⟨u, -, rfl⟩, h⟩ := ha
    exact ⟨g_ge u, h⟩
  have hF : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map g (Multiset.filter (fun u => g u ≤ hi) U.val) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map g) (Multiset.filter_congr fun _ _ => Iff.rfl)
  have hfirst : Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val := by
    have hinj : Function.Injective (fun s : Fin t => b + ((s : ℕ) : ℤ)) := by
      intro s1 s2 h
      have h' : b + ((s1 : ℕ) : ℤ) = b + ((s2 : ℕ) : ℤ) := h
      exact Fin.ext (by omega)
    have hnd1 : (Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)).Nodup := by
      apply Multiset.Nodup.filter
      apply Multiset.Nodup.filter
      exact U.nodup
    rw [Multiset.Nodup.ext hnd1 (Multiset.Nodup.map hinj (Finset.nodup _))]
    intro a
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_Icc, Multiset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, -⟩, h1, h2⟩
      have hn := Int.toNat_of_nonneg (show 0 ≤ a - b by omega)
      refine ⟨⟨(a - b).toNat, by omega⟩, ?_⟩
      show b + (((a - b).toNat : ℕ) : ℤ) = a
      omega
    · rintro ⟨s, rfl⟩
      have hs := s.isLt
      refine ⟨⟨hU s, ?_⟩, by omega, by omega⟩
      rw [g_fix _ (by omega) (by omega)]
      omega
  have hA : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val +
      Multiset.map g (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)) := by
    rw [hF]
    conv_lhs => rw [← Multiset.filter_add_not (p := fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (s := Multiset.filter (fun u => g u ≤ hi) U.val)]
    rw [Multiset.map_add, hfirst, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun s _ => by
      have hs := s.isLt
      simp only [Function.comp_apply]
      exact g_fix _ (by omega) (by omega)
  have hR : ∀ u, (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
      x ≡ u [ZMOD (l : ℤ)]) ↔ g u ≤ hi := by
    intro u
    constructor
    · rintro ⟨x, hx, hxu⟩
      rw [Finset.mem_Icc] at hx
      rw [← g_cong x u hxu, g_fix x (by omega) (by omega)]
      omega
    · intro hu
      exact ⟨g u, Finset.mem_Icc.2 ⟨by have := g_ge u; omega, by omega⟩, g_mod u⟩
  have hcard : Multiset.card (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val)) = mwCount l b t κ U := by
    unfold mwCount
    rw [← Finset.card_val, Finset.filter_val, Finset.filter_val,
      Multiset.filter_filter, Multiset.filter_filter]
    congr 1
    have e : Multiset.filter (fun a => a ∉ Finset.Icc b (b + (t : ℤ) - 1) ∧ g a ≤ hi) U.val =
        Multiset.filter (fun a => (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
          x ≡ a [ZMOD (l : ℤ)]) ∧ a ∉ Finset.Icc b (b + (t : ℤ) - 1)) U.val :=
      Multiset.filter_congr (fun u _ => by rw [hR u]; exact and_comm)
    convert e using 2
  have key := we_msum _ _ _ _ lo hi hYA hA
    (by rw [Multiset.card_map, Multiset.card_map]) hin
  rw [Multiset.card_map, hcard] at key
  have hBs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := (Finset.sum_eq_multiset_sum _ _).symm
  have hYs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) - kap s) := (Finset.sum_eq_multiset_sum _ _).symm
  rw [hBs, hYs, Finset.sum_sub_distrib, sub_sub_cancel] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  omega

/- English proof (translation)
Introduce `k j t q l h κ mw mwp U U' kc kp _ _ hU0 hU'h hsum htop hkc hkp`. Establish `hlkp : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ))` using `mul_le_mul_of_nonneg_left ((le_abs_self kp).trans hkp) (by positivity)`. Establish `hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ)` using `(neg_le_abs kc).trans hkc`. Establish `hq : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q), (h : ℤ) ≤ (q : ℤ) * h`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`.

Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `hc : (Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q)).card ≤ q`. Use `le_trans (Finset.card_le_card_of_injOn (fun a => (a : ℕ) - (k + j)) ?_ ?_) (Finset.card_range q).le` and prove the remaining obligations. Introduce `a ha`. Simplify using `at ha ⊢`.

Use linear arithmetic over natural numbers and integers. Introduce `a ha a' ha' hab`. Simplify using `at ha ha'`. Establish `hab' : (a : ℕ) - (k + j) = (a' : ℕ) - (k + j)` using `hab`. Conclude with `Fin.ext (by omega)`.

Conclude with `hc` after adjusting the coercions. Rewrite `hq` using `[Finset.sum_filter]`. Establish `hpt : ∀ a ∈ (Finset.univ : Finset (Fin (k + j + t + q))), (if (a : ℕ) < k + j then U a - U' a else 0) + (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t then U a else 0) ≤ (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q then (h : ℤ) else 0) + (if k + j + q ≤ (a : ℕ) then U' a else 0) + (U a - …`. Introduce `a _`. Establish `h1` using `hU0 a`.

Establish `h2` using `hU'h a`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hsumle` using `Finset.sum_le_sum hpt`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsumle`. Simplify using `only [Finset.sum_filter] at htop ⊢`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem weightExchangeBound_holds : WEArith := by
  intro k j t q l h κ mw mwp U U' kc kp _ _ hU0 hU'h hsum htop hkc hkp
  have hlkp : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self kp).trans hkp) (by positivity)
  have hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) := (neg_le_abs kc).trans hkc
  have hq : ∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q), (h : ℤ) ≤
      (q : ℤ) * h := by
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc : (Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q)).card ≤ q := by
      refine le_trans (Finset.card_le_card_of_injOn (fun a => (a : ℕ) - (k + j)) ?_ ?_)
        (Finset.card_range q).le
      · intro a ha
        simp at ha ⊢
        omega
      · intro a ha a' ha' hab
        simp at ha ha'
        have hab' : (a : ℕ) - (k + j) = (a' : ℕ) - (k + j) := hab
        exact Fin.ext (by omega)
    exact_mod_cast hc
  rw [Finset.sum_filter] at hq
  have hpt : ∀ a ∈ (Finset.univ : Finset (Fin (k + j + t + q))),
      (if (a : ℕ) < k + j then U a - U' a else 0) +
        (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t then U a else 0) ≤
      (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q then (h : ℤ) else 0) +
        (if k + j + q ≤ (a : ℕ) then U' a else 0) + (U a - U' a) := by
    intro a _
    have h1 := hU0 a
    have h2 := hU'h a
    split_ifs <;> omega
  have hsumle := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsumle
  simp only [Finset.sum_filter] at htop ⊢
  nlinarith

end Formalism.CohomologicalDescent
