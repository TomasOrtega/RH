import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `hTp : 0 < T'` using `by omega`. Rewrite `hW` using `[Int.fdiv_eq_ediv, if_pos (Or.inl hTp.le), sub_zero]`. Establish `h1 : (a - c1 - c2) % T' + T' * ((a - c1 - c2) / T') = a - c1 - c2` using `by first`. Consider the case `exact Int.emod_add_ediv _ _`. Consider the case `exact Int.emod_add_mul_ediv _ _`.

Consider the case `(rw [Int.emod_def]; ring)`. Consider the case `(rw [Int.mul_comm]; exact Int.emod_add_ediv' _ _)`. Consider the case `exact (by simp [Int.emod_def])`. Establish `h2 : 0 ≤ (a - c1 - c2) % T'` using `Int.emod_nonneg _ hTp.ne'`. Establish `h3 : (a - c1 - c2) % T' < T'` using `Int.emod_lt_of_pos _ hTp`.

Rewrite `h1` using `[← hW]`. Establish `hN : T' * T' ≤ a - c1 - c2`. Substitute `hT'` using the available equality. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h40) (by omega : (0:ℤ) ≤ T), mul_nonneg (sub_nonneg.2 h40) (by omega : (0:ℤ) ≤ Dm + 2), mul_nonneg hD (by omega : (0:ℤ) ≤ T)]`. Establish `hq : T' ≤ aW`.

Assume the negation of the conclusion as `hc'`. Establish `h4 : aW ≤ T' - 1` using `by omega`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 hTp.le]`. Use `⟨hq, ?_⟩` and prove the remaining obligations. Substitute `hT'` using the available equality.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem weight_floor_inequalities (a aW Dm c1 c2 T T' : ℤ) (hT' : T' = T + Dm + 2) (hD : 0 ≤ Dm) (h40 : 40 * (Dm + 2) ≤ T)
    (hc : c1 + c2 ≤ T) (ha : 2 * T ^ 2 ≤ a) (hW : aW = Int.fdiv (a - c1 - c2) T') :
    T' ≤ aW ∧ a + 1 ≤ (T + Dm + 4) * aW := by
  have hTp : 0 < T' := by omega
  rw [Int.fdiv_eq_ediv, if_pos (Or.inl hTp.le), sub_zero] at hW
  have h1 : (a - c1 - c2) % T' + T' * ((a - c1 - c2) / T') = a - c1 - c2 := by
    first
      | exact Int.emod_add_ediv _ _
      | exact Int.emod_add_mul_ediv _ _
      | (rw [Int.emod_def]; ring)
      | (rw [Int.mul_comm]; exact Int.emod_add_ediv' _ _)
      | exact (by simp [Int.emod_def])
  have h2 : 0 ≤ (a - c1 - c2) % T' := Int.emod_nonneg _ hTp.ne'
  have h3 : (a - c1 - c2) % T' < T' := Int.emod_lt_of_pos _ hTp
  rw [← hW] at h1
  have hN : T' * T' ≤ a - c1 - c2 := by
    subst hT'
    nlinarith [mul_nonneg (sub_nonneg.2 h40) (by omega : (0:ℤ) ≤ T), mul_nonneg (sub_nonneg.2 h40) (by omega : (0:ℤ) ≤ Dm + 2), mul_nonneg hD (by omega : (0:ℤ) ≤ T)]
  have hq : T' ≤ aW := by
    by_contra hc'
    have h4 : aW ≤ T' - 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h4 hTp.le]
  refine ⟨hq, ?_⟩
  subst hT'
  nlinarith

/- English proof (translation)
Unfold `degP`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_add, Finset.mul_sum, Finset.mul_sum]`. Conclude with `add_le_add (Finset.sum_le_sum fun i _ => h1 τ i) (Finset.sum_le_sum fun i _ => h2 τ i)`.
-/
theorem degP_le_mul {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j) (c : ℕ) (h1 : ∀ τ i, x.aP τ i ≤ c * z.aP τ i)
    (h2 : ∀ τ i, x.aM τ i ≤ c * z.aM τ i) : degP x ≤ c * degP z := by
  unfold degP
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun i _ => h1 τ i) (Finset.sum_le_sum fun i _ => h2 τ i)

/- English proof (translation)
Take `⟨g, hg⟩` from `(factEmb D.R D.host).1.2 τ`. Distinguish the cases in `hgP : g ∈ D.R.Psi`. Take `⟨t, ht⟩` from `(Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP`. Conclude with `⟨t, hg.symm.trans ht⟩`. It suffices to derive a contradiction.

Establish `h2 : g * D.R.cc ∈ D.R.Psi`. Assume the negation of the conclusion as `h`. Conclude with `hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)`. Take `⟨t, ht⟩` from `(Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2`. Establish `h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0` using `hp.2.2.2 t`.

Rewrite `h3` using `[← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply]`. Establish `h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E))` using `Formalism.MainNotions.WeightFamilies.emb_conj D τ _`. Establish `hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0` using `hτ`. Establish `h5 : (starRingEnd ℂ) Q.H.rt0 = Q.H.rt0`. Establish `: star Q.H.rt0 = Q.H.rt0`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `this`. Take `⟨x, hx⟩` from `Complex.conj_eq_iff_real.1 h5`. Establish `h6` using `Q.H.sqrt_neg_disc_sq`. Rewrite `h6` using `[hx]`.

Establish `h7 : x ^ 2 = -(Q.H.d : ℝ)` using `by exact_mod_cast h6`. Establish `h8 : (0 : ℝ) < Q.H.d` using `by exact_mod_cast Q.H.d_prime.pos`. Use polynomial arithmetic with `[sq_nonneg x]`.
-/
theorem exists_tau_of_inPsi {D : D7} (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    have h5 : (starRingEnd ℂ) Q.H.rt0 = Q.H.rt0 := by
      have : star Q.H.rt0 = Q.H.rt0 :=
        calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
          _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
          _ = Q.H.rt0 := h3
      exact this
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
    have h6 := Q.H.sqrt_neg_disc_sq
    rw [hx] at h6
    have h7 : x ^ 2 = -(Q.H.d : ℝ) := by exact_mod_cast h6
    have h8 : (0 : ℝ) < Q.H.d := by exact_mod_cast Q.H.d_prime.pos
    nlinarith [sq_nonneg x]

/- English proof (translation)
Introduce `τ hτ hm`. Take `⟨t, rfl⟩` from `exists_tau_of_inPsi T.Q h.pins.1 τ hτ`. Establish `hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1`. Unfold `Datum.mult`. Establish `hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0` using `hτ`.

Rewrite using `[if_pos hτ']`. Conclude with `(h.pins.2.2.2 j hj).1`. Rewrite `hm`, the goal using `[hmult]`. Establish `h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩` using `hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)`. Establish `h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩`.

Unfold `ext0`. Rewrite using `[dif_pos (by omega)]`. Unfold `wtA`. Use `lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))` and prove the remaining obligations. Simplify using `only [if_true]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem lastPos_wtA {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : w.LastPos) :
    Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := by
  intro τ hτ hm
  obtain ⟨t, rfl⟩ := exists_tau_of_inPsi T.Q h.pins.1 τ hτ
  have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold Datum.mult
    have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.pins.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dif_pos (by omega)]
  unfold wtA
  classical
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

/- English proof (translation)
Introduce `D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP`. Take `⟨-, hS, hH3, -, -⟩` from `hP`. Take `⟨-, -, -, h4, -, h6, -, -, -, h10, h11, -, -, -, hL, hF, -, hT, -, h40, h21, h22, -⟩` from `hS`. Establish `hq : ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) ≤ (qq D : ℝ) - 2` using `hH3.2.2.2.2.2`. Establish `hq' : (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL + 2 ≤ qq D`.

Establish `: (((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL + 2 : ℕ) : ℝ) ≤ (qq D : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `hf : 1 ≤ D.R.f`. Unfold `Ranks.f Ranks.n`. Conclude with `Nat.succ_le_of_lt (by positivity)`.

Establish `hr : D.R.r ≤ nP`. Establish `: 1 * D.R.r ≤ 8 * D.R.f * D.R.r` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → ((Tp D j Tn : ℕ) : ℤ) ≤ wL.aP τ i ∧ (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i`. Introduce `τ i hi`.

Establish `hn : ¬ i.1 + 1 < (D.R.sigW j).1` using `by omega`. Establish `h3` using `hL.2.1 τ i`. Rewrite `h3` using `[if_neg hn]`. Unfold `gapZ at h3`. Rewrite `h3` using `[dif_neg hn]`.

Establish `hc : (2 * (Tn : ℝ) ^ 2) ≤ (ka.aP τ i : ℝ)` using `by have := h6 τ i hi; linarith`. Establish `hc' : 2 * Tn ^ 2 ≤ ka.aP τ i` using `by exact_mod_cast hc`. Conclude with `weight_floor_inequalities (ka.aP τ i) (wL.aP τ i) (WeightFamilies.dimY D j) (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * D.R.r) Tn (Tp D j Tn) (by unfold Tp; push_cast; ring) (Int.natCast_nonneg _) (by exact_mod_cast h40) (by exact_mod_cast h21) (by exact_mod_cast hc') h3`. Use `⟨fun w2 hG => ⟨?_, lastPos_wtA h hj w2 ?_, ?_⟩, fun _ w1 hG => ⟨?_, lastPos_wtA h hj w1 ?_, ?_⟩⟩` and prove the remaining obligations. Establish `e` using `hG.1`.

Rewrite `e` using `[hL.1, hF.1]`. Establish `: 1 * nW ≤ (WeightFamilies.dimY D j + 3) * nW` using `Nat.mul_le_mul_right _ (by omega)`. Establish `e2 : (WeightFamilies.dimY D j + 4) * nW = (WeightFamilies.dimY D j + 3) * nW + nW` using `by ring`. Use linear arithmetic over natural numbers and integers. Introduce `τ i hi`.

Take `⟨-, k2⟩` from `key τ i hi`. Establish `e1 : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i` using `by exact_mod_cast hG.2.1 τ i`. Establish `e2` using `hF.2.1 τ i`. Establish `: (1 : ℤ) ≤ w2.aP τ i` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Establish `: WeightAlgebra.DF w2 ≤ (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL` using `degP_le_mul w2 wL _ (fun τ i => by have := hG.2.1 τ i; omega) (fun τ i => by have := hG.2.2 τ i; omega)`. Use linear arithmetic over natural numbers and integers. Establish `e` using `hG.1`. Use linear arithmetic over natural numbers and integers. Introduce `τ i hi`.

Take `⟨k1, -⟩` from `key τ i hi`. Establish `e1` using `hG.2.1 τ i`. Establish `k3 : (1 : ℤ) ≤ wL.aP τ i`. Establish `: (1 : ℤ) ≤ ((Tp D j Tn : ℕ) : ℤ)` using `by unfold Tp; push_cast; omega`. Use linear arithmetic over natural numbers and integers.

Establish `k4 : 1 ≤ wL.aP τ i` using `by exact_mod_cast k3`. Use linear arithmetic over natural numbers and integers. Establish `h1 : WeightAlgebra.DF w1 ≤ 2 * WeightAlgebra.DF wL` using `degP_le_mul w1 wL 2 (fun τ i => (hG.2.1 τ i).le) (fun τ i => (hG.2.2 τ i).le)`. Establish `h2 : 2 * WeightAlgebra.DF wL ≤ (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem theta_weight_bounds : ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaWeightBounds := by
  intro D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP
  obtain ⟨-, hS, hH3, -, -⟩ := hP
  obtain ⟨-, -, -, h4, -, h6, -, -, -, h10, h11, -, -, -, hL, hF, -, hT, -, h40, h21, h22, -⟩ := hS
  have hq : ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) ≤ (qq D : ℝ) - 2 := hH3.2.2.2.2.2
  have hq' : (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL + 2 ≤ qq D := by
    have : (((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL + 2 : ℕ) : ℝ) ≤ (qq D : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.succ_le_of_lt (by positivity)
  have hr : D.R.r ≤ nP := by
    have : 1 * D.R.r ≤ 8 * D.R.f * D.R.r := Nat.mul_le_mul_right _ (by omega)
    omega

  have key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      ((Tp D j Tn : ℕ) : ℤ) ≤ wL.aP τ i ∧ (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ i hi
    have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
    have h3 := hL.2.1 τ i
    rw [if_neg hn] at h3
    unfold gapZ at h3
    rw [dif_neg hn] at h3
    have hc : (2 * (Tn : ℝ) ^ 2) ≤ (ka.aP τ i : ℝ) := by have := h6 τ i hi; linarith
    have hc' : 2 * Tn ^ 2 ≤ ka.aP τ i := by exact_mod_cast hc
    exact weight_floor_inequalities (ka.aP τ i) (wL.aP τ i) (WeightFamilies.dimY D j) (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * D.R.r) Tn (Tp D j Tn)
      (by unfold Tp; push_cast; ring) (Int.natCast_nonneg _) (by exact_mod_cast h40) (by exact_mod_cast h21)
      (by exact_mod_cast hc') h3
  refine ⟨fun w2 hG => ⟨?_, lastPos_wtA h hj w2 ?_, ?_⟩, fun _ w1 hG => ⟨?_, lastPos_wtA h hj w1 ?_, ?_⟩⟩
  · have e := hG.1
    rw [hL.1, hF.1] at e
    have : 1 * nW ≤ (WeightFamilies.dimY D j + 3) * nW := Nat.mul_le_mul_right _ (by omega)
    have e2 : (WeightFamilies.dimY D j + 4) * nW = (WeightFamilies.dimY D j + 3) * nW + nW := by ring
    omega
  · intro τ i hi
    obtain ⟨-, k2⟩ := key τ i hi
    have e1 : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i := by exact_mod_cast hG.2.1 τ i
    have e2 := hF.2.1 τ i
    have : (1 : ℤ) ≤ w2.aP τ i := by nlinarith
    exact_mod_cast this
  · have : WeightAlgebra.DF w2 ≤ (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL :=
      degP_le_mul w2 wL _ (fun τ i => by have := hG.2.1 τ i; omega) (fun τ i => by have := hG.2.2 τ i; omega)
    omega
  · have e := hG.1
    omega
  · intro τ i hi
    obtain ⟨k1, -⟩ := key τ i hi
    have e1 := hG.2.1 τ i
    have k3 : (1 : ℤ) ≤ wL.aP τ i := by
      have : (1 : ℤ) ≤ ((Tp D j Tn : ℕ) : ℤ) := by unfold Tp; push_cast; omega
      omega
    have k4 : 1 ≤ wL.aP τ i := by exact_mod_cast k3
    omega
  · have h1 : WeightAlgebra.DF w1 ≤ 2 * WeightAlgebra.DF wL :=
      degP_le_mul w1 wL 2 (fun τ i => (hG.2.1 τ i).le) (fun τ i => (hG.2.2 τ i).le)
    have h2 : 2 * WeightAlgebra.DF wL ≤ (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL := Nat.mul_le_mul_right _ (by omega)
    omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
