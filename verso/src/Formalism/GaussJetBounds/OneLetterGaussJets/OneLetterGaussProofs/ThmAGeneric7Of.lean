import Formalism.GaussJetBounds.OneLetterGaussJets.StatementJ
import Formalism.GaussJetBounds.OneLetterGaussJets.StatementF
import Formalism.GaussJetBounds.GaussJetProofs.FrameA
import Formalism.GaussJetBounds.GaussJetProofs.Generic

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

/- English proof (translation)
Introduce `hGen K _ _ _ l d N0 N1 _ hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I xg hxg nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab lam hlam hlampos hlamneg e he hetop hdet`. Establish `hL` using `fun s : ZMod d => frameA_letter (J s) N0 (lam s) (fun k a => xg (s, k, a)) (hlam s) (fun k a => hxg _) (e s) (he s) (fun k => s ∈ TT ∧ k.val = 0) (hetop s) (hdet s)`. Use `choose xs T hxs hT hxtop hrec hdual using hL`. Set `x : ZMod d × Fin N0 × Fin N0 → K` to `fun y => xs y.1 y.2.1 y.2.2`. Set `spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)` to `fun r => if h : ∃ i, e r.1 i = r.2 then some (lab r.1 h.choose) else none`.

Establish `hspec_e : ∀ s i, spec (s, e s i) = some (lab s i)`. Introduce `s i`. Establish `hex : ∃ i', e s i' = e s i` using `⟨i, rfl⟩`. Establish `hch : hex.choose = i` using `he s hex.choose_spec`. Use `show (if h : ∃ i', e s i' = e s i then some (lab s h.choose) else none) = _`.

Rewrite using `[dif_pos hex, hch]`. Establish `hspec_some : ∀ s k, spec (s, k) ≠ none → ∃ i, k = e s i`. Introduce `s k h`. Assume the negation of the conclusion as `hcon`. Apply `h` to reduce the goal to its premises.

Use `show (if h : ∃ i', e s i' = k then some (lab s h.choose) else none) = _`. Rewrite using `[dif_neg (fun ⟨i, hi⟩ => hcon ⟨i, hi.symm⟩)]`. Use `hGen K l d N0 N1 hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe x (fun y => hxs _ _ _) g hg0 hg U hU ε hε TT colN p hp hp1 I T hT xg ?_ nu1 nu2 size hnu1 hnu2 hsize spec ?_ ?_ ?_` and prove the remaining obligations. Introduce `s i b`. Distinguish the cases in `hi : s ∈ TT ∧ i.val = 0`.

Simplify using `only [effMat, if_pos hi]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl, one_mul]`. Conclude with `(hxtop s i b hi).symm`. Introduce `k _ hk`.

Rewrite using `[if_neg hk, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [effMat, if_neg hi]`. Conclude with `hrec s i b hi`.

Introduce `s k s0 j hsp`. Take `⟨i, rfl⟩` from `hspec_some s k (by rw [hsp]; simp)`. Rewrite `hsp` using `[hspec_e]`. Establish `hlb : lab s i = (s0, j)` using `Option.some.inj hsp`. Take `⟨h1, h2, h3, h4, h5⟩` from `(hlab s s0 j).mp ⟨i, hlb⟩`.

Conclude with `⟨h1, h2, h3, hetop s i, h4, h5⟩`. Introduce and unpack `⟨s, k⟩ ⟨s', k'⟩ hne heq`. Take `⟨i, rfl⟩` from `hspec_some s k hne`. Take `⟨i', rfl⟩` from `hspec_some s' k' (by rw [← heq]; exact hne)`. Rewrite `heq` using `[hspec_e, hspec_e]`.

Establish `hlb : lab s i = lab s' i'` using `Option.some.inj heq`. Establish `e1` using `((hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩).2.2.1`. Establish `e2` using `((hlab s' (lab s' i').1 (lab s' i').2).mp ⟨i', rfl⟩).2.2.1`. Establish `hss : s = s'` using `by rw [e1, e2, hlb]`. Substitute `hss` using the available equality.

Establish `hii : i = i'` using `hlabinj s hlb`. Rewrite using `[hii]`. Introduce `s0 hs0 s k j hk hj hs hpos hneg hsp`. Take `⟨i, hi⟩` from `(hlab s s0 j).mpr ⟨hs0, hj, hs, hpos, hneg⟩`. Establish `hki : k ≠ e s i`.

Introduce `h`. Apply `hsp` to reduce the goal to its premises. Rewrite using `[h, hspec_e, hi]`. Establish `hzero : ∑ b, lam s i b * xs s k b = 0` using `hdual s i k hk hki`. Establish `hx0 : ∀ b, x (s0, ⟨0, h0⟩, b) = xg (s0, ⟨0, h0⟩, b)` using `fun b => hxtop s0 ⟨0, h0⟩ b ⟨hs0, rfl⟩`.

Establish `hi1 : (lab s i).1 = s0` using `by rw [hi]`. Establish `hi2 : (lab s i).2 = j` using `by rw [hi]`. Use `split_ifs with hj0`. Establish `hjpos : 0 < j`. Break down `hj with ⟨m, hm⟩` into its components or cases.

Use linear arithmetic over natural numbers and integers. Establish `hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) ^ (l ^ j.toNat) = lam s i b`. Introduce `b`. Use `hlampos s i b (by rw [hi2]; exact hjpos)` as an intermediate fact. Rewrite `this` using `[hi1, hi2]`.

Rewrite using `[this, hx0]`. Simplify using `only [hl1]`. Use `show ‖∑ b, lam s i b * xs s k b‖ ≤ _`. Rewrite using `[hzero, norm_zero]`. Conclude with `norm_nonneg _`.

Establish `hjneg : j < 0` using `not_le.mp hj0`. Establish `hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) = lam s i b ^ (l ^ (-j).toNat)`. Introduce `b`. Use `hlamneg s i b (by rw [hi2]; exact hjneg)` as an intermediate fact. Rewrite `this` using `[hi1, hi2]`.

Rewrite using `[this, hx0]`. Establish `hfr` using `frameA_frob_norm (K := K) hl (fun b => lam s i b * xs s k b) (fun b => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hlam s i b) (norm_nonneg _) (hxs s k b)) (-j).toNat`. Use the proof step `Finset.univ`.

Rewrite `hfr` using `[hzero, zero_pow (pow_ne_zero _ hl.ne_zero), zero_sub, norm_neg]`. Simplify using `only [hl1]`. Use `show ‖∑ b, lam s i b ^ (l ^ (-j).toNat) * xs s k b ^ (l ^ (-j).toNat)‖ ≤ _`. Simplify `hfr` using `only [mul_pow]`.
-/
theorem thmAFrame7_of : ThmAGen7.{u} → ThmAFrame7.{u} := by
  intro hGen K _ _ _ l d N0 N1 _ hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p
    hp hp1 I xg hxg nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab lam hlam hlampos hlamneg
    e he hetop hdet
  classical
  have hL := fun s : ZMod d => frameA_letter (J s) N0 (lam s) (fun k a => xg (s, k, a)) (hlam s)
    (fun k a => hxg _) (e s) (he s) (fun k => s ∈ TT ∧ k.val = 0) (hetop s) (hdet s)
  choose xs T hxs hT hxtop hrec hdual using hL
  let x : ZMod d × Fin N0 × Fin N0 → K := fun y => xs y.1 y.2.1 y.2.2
  let spec : ZMod d × Fin N0 → Option (ZMod d × ℤ) := fun r =>
    if h : ∃ i, e r.1 i = r.2 then some (lab r.1 h.choose) else none
  have hspec_e : ∀ s i, spec (s, e s i) = some (lab s i) := by
    intro s i
    have hex : ∃ i', e s i' = e s i := ⟨i, rfl⟩
    have hch : hex.choose = i := he s hex.choose_spec
    show (if h : ∃ i', e s i' = e s i then some (lab s h.choose) else none) = _
    rw [dif_pos hex, hch]
  have hspec_some : ∀ s k, spec (s, k) ≠ none → ∃ i, k = e s i := by
    intro s k h
    by_contra hcon
    apply h
    show (if h : ∃ i', e s i' = k then some (lab s h.choose) else none) = _
    rw [dif_neg (fun ⟨i, hi⟩ => hcon ⟨i, hi.symm⟩)]
  refine hGen K l d N0 N1 hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe x (fun y => hxs _ _ _) g hg0 hg U hU
    ε hε TT colN p hp hp1 I T hT xg ?_ nu1 nu2 size hnu1 hnu2 hsize spec ?_ ?_ ?_
  · intro s i b
    by_cases hi : s ∈ TT ∧ i.val = 0
    · simp only [effMat, if_pos hi]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
        exact (hxtop s i b hi).symm
      · intro k _ hk
        rw [if_neg hk, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [effMat, if_neg hi]
      exact hrec s i b hi
  · intro s k s0 j hsp
    obtain ⟨i, rfl⟩ := hspec_some s k (by rw [hsp]; simp)
    rw [hspec_e] at hsp
    have hlb : lab s i = (s0, j) := Option.some.inj hsp
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hlab s s0 j).mp ⟨i, hlb⟩
    exact ⟨h1, h2, h3, hetop s i, h4, h5⟩
  · rintro ⟨s, k⟩ ⟨s', k'⟩ hne heq
    obtain ⟨i, rfl⟩ := hspec_some s k hne
    obtain ⟨i', rfl⟩ := hspec_some s' k' (by rw [← heq]; exact hne)
    rw [hspec_e, hspec_e] at heq
    have hlb : lab s i = lab s' i' := Option.some.inj heq
    have e1 := ((hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩).2.2.1
    have e2 := ((hlab s' (lab s' i').1 (lab s' i').2).mp ⟨i', rfl⟩).2.2.1
    have hss : s = s' := by rw [e1, e2, hlb]
    subst hss
    have hii : i = i' := hlabinj s hlb
    rw [hii]
  · intro s0 hs0 s k j hk hj hs hpos hneg hsp
    obtain ⟨i, hi⟩ := (hlab s s0 j).mpr ⟨hs0, hj, hs, hpos, hneg⟩
    have hki : k ≠ e s i := by
      intro h
      apply hsp
      rw [h, hspec_e, hi]
    have hzero : ∑ b, lam s i b * xs s k b = 0 := hdual s i k hk hki
    have hx0 : ∀ b, x (s0, ⟨0, h0⟩, b) = xg (s0, ⟨0, h0⟩, b) := fun b =>
      hxtop s0 ⟨0, h0⟩ b ⟨hs0, rfl⟩
    have hi1 : (lab s i).1 = s0 := by rw [hi]
    have hi2 : (lab s i).2 = j := by rw [hi]
    split_ifs with hj0
    · have hjpos : 0 < j := by
        rcases hj with ⟨m, hm⟩
        omega
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) ^ (l ^ j.toNat) = lam s i b := by
        intro b
        have := hlampos s i b (by rw [hi2]; exact hjpos)
        rw [hi1, hi2] at this
        rw [this, hx0]
      simp only [hl1]
      show ‖∑ b, lam s i b * xs s k b‖ ≤ _
      rw [hzero, norm_zero]
      exact norm_nonneg _
    · have hjneg : j < 0 := not_le.mp hj0
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) = lam s i b ^ (l ^ (-j).toNat) := by
        intro b
        have := hlamneg s i b (by rw [hi2]; exact hjneg)
        rw [hi1, hi2] at this
        rw [this, hx0]
      have hfr := frameA_frob_norm (K := K) hl (fun b => lam s i b * xs s k b) (fun b => by
        rw [norm_mul]; exact mul_le_one₀ (hlam s i b) (norm_nonneg _) (hxs s k b)) (-j).toNat
        Finset.univ
      rw [hzero, zero_pow (pow_ne_zero _ hl.ne_zero), zero_sub, norm_neg] at hfr
      simp only [hl1]
      show ‖∑ b, lam s i b ^ (l ^ (-j).toNat) * xs s k b ^ (l ^ (-j).toNat)‖ ≤ _
      simpa only [mul_pow] using hfr

/- English proof (translation)
Introduce `hFrame K _ _ _ l d N0 N1 _ hl hl3 hd hev hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I Y hY nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab hJ m hm`. Establish `hY1 : ∀ y, ‖Y y‖ = 1` using `generic_norm_one hl Y hY`. Establish `hl2 : 2 ≤ l` using `hl.two_le`. Establish `hprop : ∀ s i, (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧ s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d)` using `fun s i => by`. Use `(hlab s (lab s i).1 (lab s i).2).1 ⟨i, rfl⟩` as an intermediate fact.

Conclude with `⟨this.1, this.2.1, this.2.2.1⟩`. Establish `hge : ∀ s i, 0 ≤ (m : ℤ) + (lab s i).2` using `fun s i => by`. Use `hm s i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hne : ∀ s i, (lab s i).1 ≠ s`.

Introduce `s i h`. Take `⟨-, hodd, hs⟩` from `hprop s i`. Rewrite `hs` using `[h]`. Establish `hz : (((lab s i).2 : ℤ) : ZMod d) = 0`. Use `hs.symm` as an intermediate fact.

Rewrite `this` using `[add_eq_left]`. Then use the resulting hypothesis. Rewrite `hz` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `h2 : (2 : ℤ) ∣ (lab s i).2` using `dvd_trans (by exact_mod_cast hev.two_dvd) hz`. Conclude with `(Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)`. Establish `htop : ∀ s i b, genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, b) = Y ((lab s i).1, ⟨0, h0⟩, b) ^ (l ^ m)` using `fun s i b => by`.

Unfold `genFrame`. Rewrite using `[if_pos ⟨(hprop s i).1, rfl⟩]`. Set `Lx : ∀ s, Fin (J s) → ℕ` to `fun s i => l ^ ((m : ℤ) + (lab s i).2).toNat`. Set `e : ∀ s, Fin (J s) → Fin N0` to `fun s i => ⟨i.val + (if s ∈ TT then 1 else 0), lt_of_lt_of_le (by have := i.isLt; omega) (hJ s)⟩`. Establish `hetop : ∀ s i, ¬ (s ∈ TT ∧ (e s i).val = 0)`.

Introduce and unpack `s i ⟨hs, h⟩`. Simplify using `only [e, if_pos hs] at h`. Use linear arithmetic over natural numbers and integers. Use `hFrame K l d N0 N1 hl hl3 hd hev hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I (genFrame TT l m Y) ?_ nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab (fun s i b => Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i)) ?_ ?_ ?_ e ?_ hetop ?_` and prove the remaining obligations. Introduce `y`.

Simplify using `only [genFrame]`. Use `split_ifs`. Rewrite using `[norm_pow, hY1, one_pow]`. Rewrite using `[hY1]`. Introduce `s i b`.

Simplify using `only [norm_pow, hY1, one_pow, le_refl]`. Introduce `s i b hpos`. Rewrite using `[htop, ← pow_mul, ← pow_add]`. Establish `hx : ((m : ℤ) + (lab s i).2).toNat = m + (lab s i).2.toNat` using `by omega`. Simplify using `only [Lx, hx]`.

Introduce `s i b hneg`. Establish `hx : ((m : ℤ) + (lab s i).2).toNat + (-(lab s i).2).toNat = m`. Use `hge s i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [Lx]`.

Rewrite using `[htop, ← pow_mul, ← pow_add, hx]`. Introduce `s i i' h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [e] at this`. Conclude with `Fin.ext (by omega)`.

Introduce `s`. Establish `hmat : (Matrix.of fun (i i' : Fin (J s)) => ∑ b, Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i) * genFrame TT l m Y (s, e s i', b)) = Matrix.of fun (i i' : Fin (J s)) => ∑ b, Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i) * Y (s, e s i', b)`. Use extensionality with `i i'`. Simplify using `only [Matrix.of_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Simplify using `only [genFrame]`. Rewrite using `[if_neg (hetop s i')]`. Rewrite using `[hmat]`. Use `generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (Lx s) (e s) ?_ ?_ (hne s) ?_ ?_` and prove the remaining obligations. Introduce `i i' h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [e] at this`. Conclude with `Fin.ext (by omega)`. Use `hJ s` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `i`. Conclude with `pow_ne_zero _ (by omega)`. Introduce `i i' h`. Simplify using `only [Prod.mk.injEq, Lx] at h`. Establish `h2` using `Nat.pow_right_injective hl2 h.2`.

Use `hge s i` as an intermediate fact. Use `hge s i'` as an intermediate fact. Conclude with `hlabinj s (Prod.ext h.1 (by omega))`.
-/
theorem thmAGeneric7_of : ThmAFrame7.{u} → ThmAGeneric7.{u} := by
  intro hFrame K _ _ _ l d N0 N1 _ hl hl3 hd hev hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    Y hY nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab hJ m hm
  classical
  have hY1 : ∀ y, ‖Y y‖ = 1 := generic_norm_one hl Y hY
  have hl2 : 2 ≤ l := hl.two_le

  have hprop : ∀ s i, (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧ s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d) :=
    fun s i => by
      have := (hlab s (lab s i).1 (lab s i).2).1 ⟨i, rfl⟩
      exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hge : ∀ s i, 0 ≤ (m : ℤ) + (lab s i).2 := fun s i => by
    have := hm s i
    omega
  have hne : ∀ s i, (lab s i).1 ≠ s := by
    intro s i h
    obtain ⟨-, hodd, hs⟩ := hprop s i
    rw [h] at hs
    have hz : (((lab s i).2 : ℤ) : ZMod d) = 0 := by
      have := hs.symm
      rwa [add_eq_left] at this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have h2 : (2 : ℤ) ∣ (lab s i).2 := dvd_trans (by exact_mod_cast hev.two_dvd) hz
    exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have htop : ∀ s i b, genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, b) =
      Y ((lab s i).1, ⟨0, h0⟩, b) ^ (l ^ m) := fun s i b => by
    unfold genFrame
    rw [if_pos ⟨(hprop s i).1, rfl⟩]
  let Lx : ∀ s, Fin (J s) → ℕ := fun s i => l ^ ((m : ℤ) + (lab s i).2).toNat
  let e : ∀ s, Fin (J s) → Fin N0 := fun s i =>
    ⟨i.val + (if s ∈ TT then 1 else 0), lt_of_lt_of_le (by have := i.isLt; omega) (hJ s)⟩
  have hetop : ∀ s i, ¬ (s ∈ TT ∧ (e s i).val = 0) := by
    rintro s i ⟨hs, h⟩
    simp only [e, if_pos hs] at h
    omega
  refine hFrame K l d N0 N1 hl hl3 hd hev hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p
    hp hp1 I (genFrame TT l m Y) ?_ nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab
    (fun s i b => Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i)) ?_ ?_ ?_ e ?_ hetop ?_
  · intro y
    simp only [genFrame]
    split_ifs
    · rw [norm_pow, hY1, one_pow]
    · rw [hY1]
  · intro s i b
    simp only [norm_pow, hY1, one_pow, le_refl]
  · intro s i b hpos
    rw [htop, ← pow_mul, ← pow_add]
    have hx : ((m : ℤ) + (lab s i).2).toNat = m + (lab s i).2.toNat := by omega
    simp only [Lx, hx]
  · intro s i b hneg
    have hx : ((m : ℤ) + (lab s i).2).toNat + (-(lab s i).2).toNat = m := by
      have := hge s i
      omega
    simp only [Lx]
    rw [htop, ← pow_mul, ← pow_add, hx]
  · intro s i i' h
    have := congrArg Fin.val h
    simp only [e] at this
    exact Fin.ext (by omega)
  · intro s
    have hmat : (Matrix.of fun (i i' : Fin (J s)) => ∑ b, Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i) *
          genFrame TT l m Y (s, e s i', b)) =
        Matrix.of fun (i i' : Fin (J s)) => ∑ b, Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i) *
          Y (s, e s i', b) := by
      ext i i'
      simp only [Matrix.of_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [genFrame]
      rw [if_neg (hetop s i')]
    rw [hmat]
    refine generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (Lx s) (e s) ?_ ?_ (hne s) ?_ ?_
    · intro i i' h
      have := congrArg Fin.val h
      simp only [e] at this
      exact Fin.ext (by omega)
    · have := hJ s
      omega
    · intro i
      exact pow_ne_zero _ (by omega)
    · intro i i' h
      simp only [Prod.mk.injEq, Lx] at h
      have h2 := Nat.pow_right_injective hl2 h.2
      have := hge s i
      have := hge s i'
      exact hlabinj s (Prod.ext h.1 (by omega))

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
