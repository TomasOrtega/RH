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
A detailed English derivation is pending.
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
A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem v_lt {a c : Fin (R.k - 1)} (h : a < c) : P.v c < P.v a := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := v_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem b_lt {a c : Fin R.m} (h : a < c) : P.b a < P.b c := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := b_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Split into cases according to the possible forms of the given data.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Establish an intermediate fact. A detailed English derivation is pending.
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
