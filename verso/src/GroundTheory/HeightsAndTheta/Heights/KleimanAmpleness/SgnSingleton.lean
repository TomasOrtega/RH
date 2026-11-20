import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

namespace CechContract

section Comb

variable {n : ℕ} {M : Type*} [AddCommGroup M]

/- English proof (translation)
Unfold `Kleiman.Cech.sgn`. Rewrite using `[Finset.filter_insert]`. Use `split_ifs with h`. Rewrite using `[Finset.card_insert_of_notMem (by simp [ha]), pow_succ]; ring`. Both sides reduce to the same expression.
-/
theorem sgn_insert {J : Finset (Fin n)} {a : Fin n} (ha : a ∉ J) (j : Fin n) :
    Kleiman.Cech.sgn (insert a J) j = if a < j then -Kleiman.Cech.sgn J j else Kleiman.Cech.sgn J j := by
  unfold Kleiman.Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ]; ring
  · rfl

/- English proof (translation)
Unfold `Kleiman.Cech.sgn`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
theorem sgn_mul_self (J : Finset (Fin n)) (j : Fin n) : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn J j = 1 := by
  unfold Kleiman.Cech.sgn
  rw [← mul_pow]; norm_num

/- English proof (translation)
Rewrite using `[Kleiman.Cech.sgn, Finset.filter_singleton, if_neg (lt_irrefl j)]`. Simplify using the standard rewrite rules.
-/
theorem sgn_singleton (j : Fin n) : Kleiman.Cech.sgn {j} j = 1 := by
  rw [Kleiman.Cech.sgn, Finset.filter_singleton, if_neg (lt_irrefl j)]; simp

def cD (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  ∑ j ∈ J, Kleiman.Cech.sgn J j • f (J.erase j)

def cH (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  if j₀ ∈ J then 0 else Kleiman.Cech.sgn (insert j₀ J) j₀ • f (insert j₀ J)

/- English proof (translation)
Distinguish the cases in `h₀ : j₀ ∈ J`. Establish `hH : cH j₀ (cD f) J = 0` using `if_pos h₀`. Establish `hrest : ∑ j ∈ J.erase j₀, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) = 0`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Take `⟨hj, -⟩` from `Finset.mem_erase.mp hj`.

Rewrite using `[cH, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hj, h₀⟩), smul_zero]`. Rewrite using `[hH, add_zero, cD, ← Finset.add_sum_erase J _ h₀, hrest, add_zero, cH, if_neg (Finset.notMem_erase j₀ J), Finset.insert_erase h₀, smul_smul, sgn_mul_self, one_smul]`. Establish `hsum : ∑ j ∈ J, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) + ∑ j ∈ J, Kleiman.Cech.sgn (insert j₀ J) j₀ • Kleiman.Cech.sgn (insert j₀ J) j • f ((insert j₀ J).erase j) = 0`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations.

Establish `hj₀ : j ≠ j₀` using `fun h => h₀ (h ▸ hj)`. Establish `hn : j₀ ∉ J.erase j` using `fun h => h₀ (Finset.mem_of_mem_erase h)`. Establish `e : insert j₀ (J.erase j) = (insert j₀ J).erase j` using `(Finset.erase_insert_of_ne (Ne.symm hj₀)).symm`. Establish `s1 : Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ = Kleiman.Cech.sgn (J.erase j) j₀`. Rewrite using `[← e, sgn_insert hn, if_neg (lt_irrefl _)]`.

Establish `s2 : Kleiman.Cech.sgn (insert j₀ J) j₀ = Kleiman.Cech.sgn J j₀`. Rewrite using `[sgn_insert h₀, if_neg (lt_irrefl _)]`. Establish `s3` using `sgn_insert h₀ j`. Establish `s4 : Kleiman.Cech.sgn J j₀ = if j < j₀ then -Kleiman.Cech.sgn (J.erase j) j₀ else Kleiman.Cech.sgn (J.erase j) j₀` using `by conv_lhs => rw [← Finset.insert_erase hj]`. Conclude with `sgn_insert (Finset.notMem_erase j J) j₀`.

Establish `hc : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ + Kleiman.Cech.sgn (insert j₀ J) j₀ * Kleiman.Cech.sgn (insert j₀ J) j = 0`. Rewrite using `[s1, s2, s3, s4]`. Break down `lt_or_gt_of_ne hj₀ with h | h` into its components or cases. Rewrite using `[if_neg (lt_asymm h), if_pos h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_pos h, if_neg (lt_asymm h)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[cH, if_neg hn, e, smul_smul, smul_smul, ← add_smul, hc, zero_smul]`. Establish `hH : cH j₀ (cD f) J = Kleiman.Cech.sgn (insert j₀ J) j₀ • cD f (insert j₀ J)` using `if_neg h₀`. Rewrite using `[hH]`.

Unfold `cD`. Rewrite using `[Finset.sum_insert h₀, Finset.erase_insert h₀, smul_add, smul_smul, sgn_mul_self, one_smul, Finset.smul_sum, add_left_comm, hsum, add_zero]`.
-/
theorem cD_cH_add (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) :
    cD (cH j₀ f) J + cH j₀ (cD f) J = f J := by
  by_cases h₀ : j₀ ∈ J
  · have hH : cH j₀ (cD f) J = 0 := if_pos h₀
    have hrest : ∑ j ∈ J.erase j₀, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hj, -⟩ := Finset.mem_erase.mp hj
      rw [cH, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hj, h₀⟩), smul_zero]
    rw [hH, add_zero, cD, ← Finset.add_sum_erase J _ h₀, hrest, add_zero, cH,
      if_neg (Finset.notMem_erase j₀ J), Finset.insert_erase h₀, smul_smul, sgn_mul_self, one_smul]
  · have hsum : ∑ j ∈ J, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) +
        ∑ j ∈ J, Kleiman.Cech.sgn (insert j₀ J) j₀ • Kleiman.Cech.sgn (insert j₀ J) j •
          f ((insert j₀ J).erase j) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj₀ : j ≠ j₀ := fun h => h₀ (h ▸ hj)
      have hn : j₀ ∉ J.erase j := fun h => h₀ (Finset.mem_of_mem_erase h)
      have e : insert j₀ (J.erase j) = (insert j₀ J).erase j := (Finset.erase_insert_of_ne (Ne.symm hj₀)).symm
      have s1 : Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ = Kleiman.Cech.sgn (J.erase j) j₀ := by
        rw [← e, sgn_insert hn, if_neg (lt_irrefl _)]
      have s2 : Kleiman.Cech.sgn (insert j₀ J) j₀ = Kleiman.Cech.sgn J j₀ := by
        rw [sgn_insert h₀, if_neg (lt_irrefl _)]
      have s3 := sgn_insert h₀ j
      have s4 : Kleiman.Cech.sgn J j₀ =
          if j < j₀ then -Kleiman.Cech.sgn (J.erase j) j₀ else Kleiman.Cech.sgn (J.erase j) j₀ := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact sgn_insert (Finset.notMem_erase j J) j₀
      have hc : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ +
          Kleiman.Cech.sgn (insert j₀ J) j₀ * Kleiman.Cech.sgn (insert j₀ J) j = 0 := by
        rw [s1, s2, s3, s4]
        rcases lt_or_gt_of_ne hj₀ with h | h
        · rw [if_neg (lt_asymm h), if_pos h]; ring
        · rw [if_pos h, if_neg (lt_asymm h)]; ring
      rw [cH, if_neg hn, e, smul_smul, smul_smul, ← add_smul, hc, zero_smul]
    have hH : cH j₀ (cD f) J = Kleiman.Cech.sgn (insert j₀ J) j₀ • cD f (insert j₀ J) := if_neg h₀
    rw [hH]
    unfold cD
    rw [Finset.sum_insert h₀, Finset.erase_insert h₀, smul_add, smul_smul, sgn_mul_self, one_smul,
      Finset.smul_sum, add_left_comm, hsum, add_zero]

end Comb

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

open Classical in

noncomputable def extZ {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (K : Finset (Fin (N + 1))) : Ω :=
  if h : K.Nonempty ∧ K ⊆ Kleiman.support x ∧ K.card = p + 1 then s ⟨⟨K, h.1, h.2.1⟩, h.2.2⟩ else 0

/- English proof (translation)
Rewrite using `[extZ, dif_pos ⟨I.1.2.1, I.1.2.2, I.2⟩]`.
-/
theorem extZ_idx {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : extZ s I.1.1 = s I := by
  rw [extZ, dif_pos ⟨I.1.2.1, I.1.2.2, I.2⟩]

/- English proof (translation)
Rewrite using `[Kleiman.Cech.d_apply, cD, ← Finset.sum_coe_sort J.1.1 (fun j => Kleiman.Cech.sgn J.1.1 j • g (J.1.1.erase j))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ • t (Kleiman.Cech.face J j) = _ • g (Kleiman.Cech.face J j).1.1`. Rewrite using `[hg]`.
-/
theorem d_eq {p : ℕ} (t : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p) (g : Finset (Fin (N + 1)) → Ω)
    (hg : ∀ I, t I = g I.1.1) (J : Kleiman.Cech.Idx (Kleiman.support x) (p + 1)) :
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t J = cD g J.1.1 := by
  rw [Kleiman.Cech.d_apply, cD,
    ← Finset.sum_coe_sort J.1.1 (fun j => Kleiman.Cech.sgn J.1.1 j • g (J.1.1.erase j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ • t (Kleiman.Cech.face J j) = _ • g (Kleiman.Cech.face J j).1.1
  rw [hg]

def insIdx {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ} (I : Kleiman.Cech.Idx (Kleiman.support x) p)
    (h : j₀ ∉ I.1.1) : Kleiman.Cech.Idx (Kleiman.support x) (p + 1) :=
  ⟨⟨insert j₀ I.1.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀ I.1.2.2⟩, by
    rw [Finset.card_insert_of_notMem h, I.2]⟩

/- English proof (translation)
Unfold `cH`. Use `split_ifs with h`. Both sides reduce to the same expression. Establish `h1` using `d_eq S s (extZ s) (fun I => (extZ_idx s I).symm) (insIdx hj₀ I h)`. Rewrite `h1` using `[hds]`.

Express the relevant statement in the definitionally equal form `_ • cD (extZ s) (insIdx hj₀ I h).1.1 = 0`. Rewrite using `[← h1, Pi.zero_apply, smul_zero]`.
-/
theorem cH_cD_extZ {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ}
    (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (hds : Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p s = 0)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : cH j₀ (cD (extZ s)) I.1.1 = 0 := by
  unfold cH
  split_ifs with h
  · rfl
  · have h1 := d_eq S s (extZ s) (fun I => (extZ_idx s I).symm) (insIdx hj₀ I h)
    rw [hds] at h1
    change _ • cD (extZ s) (insIdx hj₀ I h).1.1 = 0
    rw [← h1, Pi.zero_apply, smul_zero]

end CechSide

/- English proof (translation)
Introduce `S _ Ω _ _ N x G J₀ hcard hmono hadd`. Take `⟨j₀, hJ₀⟩` from `Finset.card_eq_one.mp hcard`. Establish `hj₀U : j₀ ∈ Kleiman.support x` using `J₀.2.2 (hJ₀ ▸ Finset.mem_singleton_self j₀)`. Establish `hG : ∀ J J' : Kleiman.Chart x, J'.1 = insert j₀ J.1 → G J' = G J` using `fun J J' h => hadd J J' (by rw [h, hJ₀, Finset.insert_eq])`. Use `⟨fun J => ?_, fun s hs hds => ?_, fun p s hs hds => ?_⟩` and prove the remaining obligations.

Set `J' : Kleiman.Chart x` to `⟨insert j₀ J.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀U J.2.2⟩`. Rewrite using `[← hG J J' rfl]`. Conclude with `hmono J₀ J' (by`. Rewrite using `[hJ₀]`. Conclude with `Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))`.

Use `⟨s ⟨J₀, hcard⟩, (hs ⟨J₀, hcard⟩ (Set.mem_univ _) :), fun J => ?_⟩` and prove the remaining obligations. Establish `eb : extZ s {j₀} = s ⟨J₀, hcard⟩` using `(congrArg (extZ s) hJ₀).symm.trans (extZ_idx s ⟨J₀, hcard⟩)`. Take `⟨j, hj⟩` from `Finset.card_eq_one.mp J.2`. Establish `e1 : cD (cH j₀ (extZ s)) J.1.1 = extZ s {j₀}`. Rewrite using `[hj, cD, Finset.sum_singleton, Finset.erase_singleton, sgn_singleton, one_smul, cH, if_neg (Finset.notMem_empty _), insert_empty_eq, sgn_singleton, one_smul]`.

Rewrite using `[← extZ_idx s J, ← cD_cH_add j₀ (extZ s) J.1.1, cH_cD_extZ S hj₀U s hds J, add_zero, e1, eb]`. Use `⟨fun I => cH j₀ (extZ s) I.1.1, fun I _ => ?_, ?_⟩` and prove the remaining obligations. Use `show cH j₀ (extZ s) I.1.1 ∈ G I.1`. Unfold `cH`. Use `split_ifs with h`.

Conclude with `zero_mem _`. Establish `hK : s (insIdx hj₀U I h) ∈ G (insIdx hj₀U I h).1` using `hs _ (Set.mem_univ _)`. Rewrite `hK` using `[← extZ_idx s (insIdx hj₀U I h), hG I.1 (insIdx hj₀U I h).1 rfl]`. Conclude with `zsmul_mem hK _`. Use function extensionality and compare the values at `J`.

Rewrite using `[d_eq S _ (cH j₀ (extZ s)) (fun _ => rfl)]`. Use `cD_cH_add j₀ (extZ s) J.1.1` as an intermediate fact. Rewrite `this` using `[cH_cD_extZ S hj₀U s hds J, add_zero, extZ_idx]`. Conclude with `this`.
-/
theorem proof : Statement := by
  intro S _ Ω _ _ N x G J₀ hcard hmono hadd
  obtain ⟨j₀, hJ₀⟩ := Finset.card_eq_one.mp hcard
  have hj₀U : j₀ ∈ Kleiman.support x := J₀.2.2 (hJ₀ ▸ Finset.mem_singleton_self j₀)
  have hG : ∀ J J' : Kleiman.Chart x, J'.1 = insert j₀ J.1 → G J' = G J := fun J J' h =>
    hadd J J' (by rw [h, hJ₀, Finset.insert_eq])
  refine ⟨fun J => ?_, fun s hs hds => ?_, fun p s hs hds => ?_⟩
  · let J' : Kleiman.Chart x := ⟨insert j₀ J.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀U J.2.2⟩
    rw [← hG J J' rfl]
    exact hmono J₀ J' (by
      rw [hJ₀]; exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  · refine ⟨s ⟨J₀, hcard⟩, (hs ⟨J₀, hcard⟩ (Set.mem_univ _) :), fun J => ?_⟩
    have eb : extZ s {j₀} = s ⟨J₀, hcard⟩ :=
      (congrArg (extZ s) hJ₀).symm.trans (extZ_idx s ⟨J₀, hcard⟩)
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp J.2
    have e1 : cD (cH j₀ (extZ s)) J.1.1 = extZ s {j₀} := by
      rw [hj, cD, Finset.sum_singleton, Finset.erase_singleton, sgn_singleton, one_smul, cH,
        if_neg (Finset.notMem_empty _), insert_empty_eq, sgn_singleton, one_smul]
    rw [← extZ_idx s J, ← cD_cH_add j₀ (extZ s) J.1.1, cH_cD_extZ S hj₀U s hds J, add_zero, e1, eb]
  · refine ⟨fun I => cH j₀ (extZ s) I.1.1, fun I _ => ?_, ?_⟩
    · show cH j₀ (extZ s) I.1.1 ∈ G I.1
      unfold cH
      split_ifs with h
      · exact zero_mem _
      · have hK : s (insIdx hj₀U I h) ∈ G (insIdx hj₀U I h).1 := hs _ (Set.mem_univ _)
        rw [← extZ_idx s (insIdx hj₀U I h), hG I.1 (insIdx hj₀U I h).1 rfl] at hK
        exact zsmul_mem hK _
    · funext J
      rw [d_eq S _ (cH j₀ (extZ s)) (fun _ => rfl)]
      have := cD_cH_add j₀ (extZ s) J.1.1
      rw [cH_cD_extZ S hj₀U s hds J, add_zero, extZ_idx] at this
      exact this

end CechContract

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
