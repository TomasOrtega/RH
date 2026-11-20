import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbedding
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

section Param

variable {R : Ranks} (P : HCParam R)

/- English proof (translation)
The claim follows from `| 0, h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩) | n + 1, h => by have h1 := v_step a n (by omega) have h2 : P.v ⟨a + (n + 1) + 1, h⟩ < P.v ⟨a + n + 1, by omega⟩ := (P.u_gt_v ⟨a + (n + 1) + 1, h⟩).trans (P.v_gt_u ⟨a + n + 1, by omega⟩) exact h2.trans h1`.
-/
theorem v_step (a : ℕ) : ∀ (n : ℕ) (h : a + n + 1 < R.k - 1),
    P.v ⟨a + n + 1, h⟩ < P.v ⟨a, by omega⟩
  | 0, h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  | n + 1, h => by
    have h1 := v_step a n (by omega)
    have h2 : P.v ⟨a + (n + 1) + 1, h⟩ < P.v ⟨a + n + 1, by omega⟩ :=
      (P.u_gt_v ⟨a + (n + 1) + 1, h⟩).trans (P.v_gt_u ⟨a + n + 1, by omega⟩)
    exact h2.trans h1

/- English proof (translation)
The claim follows from `| 0, h => by have h1 := P.gap_be ⟨a, by omega⟩ have h2 := P.gap_eb ⟨a, by omega⟩ h have ht : (0 : ℚ) ≤ R.t := by positivity linarith | n + 1, h => by have h0 := b_step a n (by omega) have h1 := P.gap_be ⟨a + n + 1, by omega⟩ have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨a + (n + 1) + 1, h …`.
-/
theorem b_step (a : ℕ) : ∀ (n : ℕ) (h : a + n + 1 < R.m),
    P.b ⟨a, by omega⟩ < P.b ⟨a + n + 1, h⟩
  | 0, h => by
    have h1 := P.gap_be ⟨a, by omega⟩
    have h2 := P.gap_eb ⟨a, by omega⟩ h
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith
  | n + 1, h => by
    have h0 := b_step a n (by omega)
    have h1 := P.gap_be ⟨a + n + 1, by omega⟩
    have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨a + (n + 1) + 1, h⟩ - P.e ⟨a + n + 1, by omega⟩ :=
      P.gap_eb ⟨a + n + 1, by omega⟩ h
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith

/- English proof (translation)
Take `⟨n, hn⟩` from `Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)`. Use `v_step P a.1 n (hn ▸ c.2)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `Fin.ext hn`.
-/
theorem v_lt {a c : Fin (R.k - 1)} (h : a < c) : P.v c < P.v a := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := v_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

/- English proof (translation)
Take `⟨n, hn⟩` from `Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)`. Use `b_step P a.1 n (hn ▸ c.2)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `Fin.ext hn`.
-/
theorem b_lt {a c : Fin R.m} (h : a < c) : P.b a < P.b c := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := b_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

/- English proof (translation)
Introduce `a c hac`. Take `⟨x, hx⟩` from `P.v_int a`. Take `⟨y, hy⟩` from `P.v_int c`. Establish `hxy : P.v a = P.v c`. Simplify using `only [hx, hy, Int.floor_intCast] at hac`.

Rewrite using `[hx, hy, hac]`. Break down `lt_trichotomy a c with h | h | h` into its components or cases. Conclude with `absurd hxy (v_lt P h).ne'`. Conclude with `h`. Conclude with `absurd hxy (v_lt P h).ne`.
-/
theorem floor_v_inj : Function.Injective fun a : Fin (R.k - 1) => ⌊P.v a⌋ := by
  intro a c hac
  obtain ⟨x, hx⟩ := P.v_int a
  obtain ⟨y, hy⟩ := P.v_int c
  have hxy : P.v a = P.v c := by
    simp only [hx, hy, Int.floor_intCast] at hac
    rw [hx, hy, hac]
  rcases lt_trichotomy a c with h | h | h
  · exact absurd hxy (v_lt P h).ne'
  · exact h
  · exact absurd hxy (v_lt P h).ne

/- English proof (translation)
Introduce `a c hac`. Take `⟨x, hx⟩` from `P.b_int a`. Take `⟨y, hy⟩` from `P.b_int c`. Establish `hxy : P.b a = P.b c`. Simplify using `only [hx, hy, Int.floor_intCast] at hac`.

Rewrite using `[hx, hy, hac]`. Break down `lt_trichotomy a c with h | h | h` into its components or cases. Conclude with `absurd hxy (b_lt P h).ne`. Conclude with `h`. Conclude with `absurd hxy (b_lt P h).ne'`.
-/
theorem floor_b_inj : Function.Injective fun a : Fin R.m => ⌊P.b a⌋ := by
  intro a c hac
  obtain ⟨x, hx⟩ := P.b_int a
  obtain ⟨y, hy⟩ := P.b_int c
  have hxy : P.b a = P.b c := by
    simp only [hx, hy, Int.floor_intCast] at hac
    rw [hx, hy, hac]
  rcases lt_trichotomy a c with h | h | h
  · exact absurd hxy (b_lt P h).ne
  · exact h
  · exact absurd hxy (b_lt P h).ne'

/- English proof (translation)
Rewrite using `[Multiset.nodup_add]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `Multiset.Nodup.map (fun a c h => floor_v_inj P ?_) Finset.univ.nodup` and prove the remaining obligations. Simplify using `using h`. Use `Multiset.Nodup.map (fun a c h => floor_b_inj P ?_) Finset.univ.nodup` and prove the remaining obligations.

Simplify using `using h`. Rewrite using `[Multiset.disjoint_left]`. Introduce `u hu hu'`. Take `⟨a, -, rfl⟩` from `Multiset.mem_map.1 hu`. Take `⟨i, -, hi⟩` from `Multiset.mem_map.1 hu'`.

Take `⟨x, hx⟩` from `P.v_int a`. Take `⟨y, hy⟩` from `P.b_int i`. Establish `hx0 : 0 ≤ x`. Use `hv a` as an intermediate fact. Rewrite `this` using `[hx]`.

Conclude with `this` after adjusting the coercions. Establish `hy0 : 0 < y`. Use `hb i` as an intermediate fact. Rewrite `this` using `[hy]`. Conclude with `this` after adjusting the coercions.

Simplify using `only [hx, hy, Int.floor_intCast] at hi`. Use linear arithmetic over natural numbers and integers.
-/
theorem cloud_add_lows_nodup (j : Fin R.m) (hv : ∀ a, 0 ≤ P.v a) (hb : ∀ i, 0 < P.b i) :
    (cloud P j + lows P j).Nodup := by
  rw [Multiset.nodup_add]
  refine ⟨?_, ?_, ?_⟩
  · refine Multiset.Nodup.map (fun a c h => floor_v_inj P ?_) Finset.univ.nodup
    simpa using h
  · refine Multiset.Nodup.map (fun a c h => floor_b_inj P ?_) Finset.univ.nodup
    simpa using h
  · rw [Multiset.disjoint_left]
    intro u hu hu'
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hu
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hu'
    obtain ⟨x, hx⟩ := P.v_int a
    obtain ⟨y, hy⟩ := P.b_int i
    have hx0 : 0 ≤ x := by
      have := hv a
      rw [hx] at this
      exact_mod_cast this
    have hy0 : 0 < y := by
      have := hb i
      rw [hy] at this
      exact_mod_cast this
    simp only [hx, hy, Int.floor_intCast] at hi
    omega

/- English proof (translation)
Establish `h` using `cloud_add_lows_nodup P j hv hb`. Establish `h1 : Function.Injective fun u : ℤ => -u - 1` using `fun a c h => by`. Establish `: -a - 1 = -c - 1` using `h`. Use linear arithmetic over natural numbers and integers. Establish `h2 : Function.Injective fun u : ℤ => (R.t : ℤ) - 1 - u` using `fun a c h => by`.

Establish `: (R.t : ℤ) - 1 - a = (R.t : ℤ) - 1 - c` using `h`. Use linear arithmetic over natural numbers and integers. Unfold `jT2 jW`. Use `Multiset.Nodup.map h1 ?_` and prove the remaining obligations. Consider the cases of `s`.

Simplify using `using Multiset.Nodup.map h2 h`. Simplify using `using h`.
-/
theorem twistedDualJumpsWithoutBlock_nodup_of_signs (j : Fin R.m) (s : Bool) (hv : ∀ a, 0 ≤ P.v a) (hb : ∀ i, 0 < P.b i) :
    (jT2 P j s).Nodup := by
  have h := cloud_add_lows_nodup P j hv hb
  have h1 : Function.Injective fun u : ℤ => -u - 1 := fun a c h => by
    have : -a - 1 = -c - 1 := h
    omega
  have h2 : Function.Injective fun u : ℤ => (R.t : ℤ) - 1 - u := fun a c h => by
    have : (R.t : ℤ) - 1 - a = (R.t : ℤ) - 1 - c := h
    omega
  unfold jT2 jW
  refine Multiset.Nodup.map h1 ?_
  cases s
  · simpa using Multiset.Nodup.map h2 h
  · simpa using h

end Param

/- English proof (translation)
Introduce `D L C j g s hR`. Take `⟨hC, h100, hη, hwb, -, hCb⟩` from `id hR`. Establish `hS` using `L.Sc_pos`. Establish `hE` using `L.etaSz_pos`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `by positivity`.

Establish `hηw : L.etaSz < L.sc.w'' D.R.n` using `by linarith`. Establish `hbig : L.etaSz < (⌊(hcAt D g).e j⌋ : ℝ)`. Distinguish the cases in `hT : Thick D.host g`. Establish `h1` using `(SizeThick.size_thick L g j hT).1`. Establish `hL : (0 : ℝ) ≤ (D.host.Lw : ℝ)` using `by positivity`.

Establish `hb' : 0 < L.sc.b'` using `by linarith`. Establish `h2 : L.sc.b' ≤ C * ((D.host.Lw : ℝ) + 1) * L.sc.b'`. Establish `: (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `lt_of_lt_of_le hηw (size_not_thick L C g j hR hT).1`. Use `twistedDualJumpsWithoutBlock_nodup_of_signs _ j s ?_ ?_` and prove the remaining obligations. Introduce `a`. Establish `h` using `(L.cloud_v (D.eTau.symm ⟨plc g, plc_mem g⟩) a).1`. Conclude with `h` after adjusting the coercions.

Introduce `i`. Establish `h` using `L.be_close (D.eTau.symm ⟨plc g, plc_mem g⟩) i j`. Establish `h' : |((((hcAt D g).b i - (hcAt D g).e j : ℚ)) : ℝ)| ≤ L.etaSz` using `h`. Take `⟨z, hz⟩` from `(hcAt D g).e_int j`. Rewrite `hbig` using `[hz, Int.floor_intCast]`.

Rewrite `h'` using `[hz]`. Establish `h2` using `(abs_le.1 h').1`. Move the coercions through the operations in `at h2`. Establish `: (0 : ℝ) < (((hcAt D g).b i : ℚ) : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem twistedDualJumpsWithoutBlock_nodup_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (g : D.R.GG) (s : Bool),
    Roomy L C → (jT2 (hcAt D g) j s).Nodup := by
  intro D L C j g s hR
  obtain ⟨hC, h100, hη, hwb, -, hCb⟩ := id hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have hηw : L.etaSz < L.sc.w'' D.R.n := by linarith
  have hbig : L.etaSz < (⌊(hcAt D g).e j⌋ : ℝ) := by
    by_cases hT : Thick D.host g
    · have h1 := (SizeThick.size_thick L g j hT).1
      have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
      have hb' : 0 < L.sc.b' := by linarith
      have h2 : L.sc.b' ≤ C * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
        have : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
        nlinarith
      linarith
    · exact lt_of_lt_of_le hηw (size_not_thick L C g j hR hT).1
  refine twistedDualJumpsWithoutBlock_nodup_of_signs _ j s ?_ ?_
  · intro a
    have h := (L.cloud_v (D.eTau.symm ⟨plc g, plc_mem g⟩) a).1
    exact_mod_cast h
  · intro i
    have h := L.be_close (D.eTau.symm ⟨plc g, plc_mem g⟩) i j
    have h' : |((((hcAt D g).b i - (hcAt D g).e j : ℚ)) : ℝ)| ≤ L.etaSz := h
    obtain ⟨z, hz⟩ := (hcAt D g).e_int j
    rw [hz, Int.floor_intCast] at hbig
    rw [hz] at h'
    have h2 := (abs_le.1 h').1
    push_cast at h2
    have : (0 : ℝ) < (((hcAt D g).b i : ℚ) : ℝ) := by linarith
    exact_mod_cast this

end GlobalTheory.HTW.Rec
