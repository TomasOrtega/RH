import Formalism.LocalToGlobal.GlobalTheory.SuppSat
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaa
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSk
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.GenericFramesLetters
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

section AtRecord

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ)

open NumberField in

/- English proof (translation)
Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 h`. Distinguish the cases in `hN : N = 0`. Substitute `hN` using the available equality. Simplify using `only [Int.cast_zero, mul_zero] at hz`. Establish `: a = 0` using `by exact_mod_cast hz.symm`.

Simplify using `[this]`. Establish `hNE : (N : E) ≠ 0` using `by exact_mod_cast hN`. Establish `hzE' : (z : E) * (N : E) = (a : E)`. Use `congrArg (fun t : 𝓞 E => (t : E)) hz` as an intermediate fact. Simplify using `using this`.

Establish `hzE : (z : E) = algebraMap ℚ E ((a : ℚ) / N)`. Rewrite using `[map_div₀, eq_div_iff (by simpa using hNE)]`. Simplify using `using hzE'`. Establish `hint : IsIntegral ℤ ((a : ℚ) / N)`. Establish `: IsIntegral ℤ (z : E)` using `RingOfIntegers.isIntegral_coe z`.

Rewrite `this` using `[hzE]`. Conclude with `(isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 this`. Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hNQ : (N : ℚ) ≠ 0` using `by exact_mod_cast hN`.

Establish `: (a : ℚ) = N * m`. Establish `h2 : (m : ℚ) = (a : ℚ) / N` using `by simpa using hm`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions.
-/
theorem pa_int_dvd_of_mem_span {E : Type*} [Field E] [NumberField E] (N a : ℤ)
    (h : (a : 𝓞 E) ∈ Ideal.span {(N : 𝓞 E)}) : N ∣ a := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  by_cases hN : N = 0
  · subst hN
    simp only [Int.cast_zero, mul_zero] at hz
    have : a = 0 := by exact_mod_cast hz.symm
    simp [this]
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
  have hzE' : (z : E) * (N : E) = (a : E) := by
    have := congrArg (fun t : 𝓞 E => (t : E)) hz
    simpa using this
  have hzE : (z : E) = algebraMap ℚ E ((a : ℚ) / N) := by
    rw [map_div₀, eq_div_iff (by simpa using hNE)]
    simpa using hzE'
  have hint : IsIntegral ℤ ((a : ℚ) / N) := by
    have : IsIntegral ℤ (z : E) := RingOfIntegers.isIntegral_coe z
    rw [hzE] at this
    exact (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨m, ?_⟩
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have : (a : ℚ) = N * m := by
    have h2 : (m : ℚ) = (a : ℚ) / N := by simpa using hm
    rw [h2]; field_simp
  exact_mod_cast this

open NumberField in

/- English proof (translation)
Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hcong`. Use `set c' : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (c : E ≃+* E) with hc'`. Establish `hT : (T : 𝓞 E) = pz * c' pz`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `: ((c' pz : 𝓞 E) : E) = c (pz : E)` using `rfl`.

Use `show ((T : 𝓞 E) : E) = (pz : E) * ((c' pz : 𝓞 E) : E)`. Rewrite using `[this, hpz]`. Simplify using the standard rewrite rules. Establish `hp : pz = 1 + y * M` using `by rw [hy]; ring`. Establish `hcp : c' pz = 1 + c' y * M` using `by rw [hp]; simp`.

Apply `pa_int_dvd_of_mem_span (E := E)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨y + c' y + y * c' y * M, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hT, hcp]`.

Take the linear combination `(-(1 + c' y * M)) * hp`.
-/
theorem pa_norm_congr_one {E : Type*} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (T M : ℕ) (pz : 𝓞 E)
    (hpz : (pz : E) * c (pz : E) = (T : E)) (hcong : (pz - 1) ∈ Ideal.span {(M : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hcong
  set c' : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (c : E ≃+* E) with hc'
  have hT : (T : 𝓞 E) = pz * c' pz := by
    apply RingOfIntegers.ext
    have : ((c' pz : 𝓞 E) : E) = c (pz : E) := rfl
    show ((T : 𝓞 E) : E) = (pz : E) * ((c' pz : 𝓞 E) : E)
    rw [this, hpz]; simp
  have hp : pz = 1 + y * M := by rw [hy]; ring
  have hcp : c' pz = 1 + c' y * M := by rw [hp]; simp
  apply pa_int_dvd_of_mem_span (E := E)
  rw [Ideal.mem_span_singleton']
  refine ⟨y + c' y + y * c' y * M, ?_⟩
  push_cast
  rw [hT, hcp]
  linear_combination (-(1 + c' y * M)) * hp

/- English proof (translation)
Take `⟨m, hm⟩` from `hT`. Establish `h4' : (T : ℤ) = 1 + 4 * (q * m)` using `by linarith`. Establish `h4 : T % 4 = 1`. Generalize the expression as in `(q : ℤ) * m = k at h4'`. Use linear arithmetic over natural numbers and integers.

Establish `hTq : (T : ℤ) % q = 1 % q`. Establish `: (T : ℤ) = 1 + q * (4 * m)` using `by linarith`. Rewrite using `[this, Int.add_mul_emod_self_left]`. Establish `hodd : Odd T` using `Nat.odd_iff.2 (by omega)`. Rewrite using `[show (-(q : ℤ)) = (-1) * q by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hq h4, jacobiSym.mod_left, hTq, ← jacobiSym.mod_left, jacobiSym.one_left]`.
-/
theorem pa_jacobi_neg_eq_one (q T : ℕ) (hq : Odd q) (hT : (4 * q : ℤ) ∣ (T : ℤ) - 1) :
    jacobiSym (-(q : ℤ)) T = 1 := by
  obtain ⟨m, hm⟩ := hT
  have h4' : (T : ℤ) = 1 + 4 * (q * m) := by linarith
  have h4 : T % 4 = 1 := by
    generalize (q : ℤ) * m = k at h4'
    omega
  have hTq : (T : ℤ) % q = 1 % q := by
    have : (T : ℤ) = 1 + q * (4 * m) := by linarith
    rw [this, Int.add_mul_emod_self_left]
  have hodd : Odd T := Nat.odd_iff.2 (by omega)
  rw [show (-(q : ℤ)) = (-1) * q by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hodd,
    ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hq h4,
    jacobiSym.mod_left, hTq, ← jacobiSym.mod_left, jacobiSym.one_left]

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h1 : (T : ℤ) ∣ (T : ℤ) - 1` using `(Int.natCast_dvd_natCast.2 hm).trans h`. Establish `h2 : (T : ℤ) ∣ 1`. Use `dvd_sub (dvd_refl (T : ℤ)) h1` as an intermediate fact. Simplify using `using this`.

Conclude with `hm1 (by exact_mod_cast Int.natAbs_dvd_natAbs.2 h2 |> Nat.dvd_one.1)`.
-/
theorem pa_ne_of_dvd_of_congr {M T m : ℕ} (h : (M : ℤ) ∣ (T : ℤ) - 1) (hm : m ∣ M) (hm1 : m ≠ 1) : T ≠ m := by
  rintro rfl
  have h1 : (T : ℤ) ∣ (T : ℤ) - 1 := (Int.natCast_dvd_natCast.2 hm).trans h
  have h2 : (T : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_refl (T : ℤ)) h1
    simpa using this
  exact hm1 (by exact_mod_cast Int.natAbs_dvd_natAbs.2 h2 |> Nat.dvd_one.1)

/- English proof (translation)
Take `⟨π, -, hn, hc⟩` from `D.T_norm u`. Establish `hcg` using `pa_norm_congr_one D.host.conj (D.mem u).A.T _ π hn hc`. Establish `hT` using `(D.mem u).A.T_prime`. Establish `hN : ¬ (D.mem u).A.T ∣ D.host.condN` using `fun hdv => pa_ne_of_dvd_of_congr hcg (hdv.trans ⟨(D.host.g 0 * D.host.g 1) ^ 2, rfl⟩) hT.one_lt.ne' rfl`. Establish `hj : jacobiSym (-(D.host.d : ℤ)) (D.mem u).A.T = 1`.

Use `pa_jacobi_neg_eq_one D.host.d _ (D.host.hypOdd.2.1.odd_of_ne_two D.host.hypOdd.2.2.2.2) (Dvd.dvd.trans ?_ hcg)` and prove the remaining obligations. Take `⟨c, hc16⟩` from `D.host.toHostRaw.sixteen_dvd_QS`. Establish `hc16' : D.host.QS = 16 * c` using `hc16`. Conclude with `⟨((4 * c * D.host.q * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : ℤ), by rw [hc16']; push_cast; ring⟩`. Establish `hcl : D.host.cls (D.mem u).A.T = PrimeClass.splitK` using `(primeClass_eq_splitK_iff' hT).2 ⟨hN, hj⟩`.

Apply the tactic sequence `rintro (h | h) <;> rw [hcl] at h <;> cases h`.
-/
theorem T_not_inert (D : D7) (u : D.what₂.Word) : ¬ InertK D (D.mem u).A.T := by
  obtain ⟨π, -, hn, hc⟩ := D.T_norm u
  have hcg := pa_norm_congr_one D.host.conj (D.mem u).A.T _ π hn hc
  have hT := (D.mem u).A.T_prime
  have hN : ¬ (D.mem u).A.T ∣ D.host.condN := fun hdv =>
    pa_ne_of_dvd_of_congr hcg (hdv.trans ⟨(D.host.g 0 * D.host.g 1) ^ 2, rfl⟩) hT.one_lt.ne' rfl
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.mem u).A.T = 1 := by
    refine pa_jacobi_neg_eq_one D.host.d _ (D.host.hypOdd.2.1.odd_of_ne_two D.host.hypOdd.2.2.2.2) (Dvd.dvd.trans ?_ hcg)
    obtain ⟨c, hc16⟩ := D.host.toHostRaw.sixteen_dvd_QS
    have hc16' : D.host.QS = 16 * c := hc16
    exact ⟨((4 * c * D.host.q * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : ℤ), by rw [hc16']; push_cast; ring⟩
  have hcl : D.host.cls (D.mem u).A.T = PrimeClass.splitK :=
    (primeClass_eq_splitK_iff' hT).2 ⟨hN, hj⟩
  rintro (h | h) <;> rw [hcl] at h <;> cases h

/- English proof (translation)
Establish `h1 : ∑ w ∈ S, Lnk.lE w * h (D.what₂.places.resChar w) = ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w ∈ Q), Lnk.lE w * h (D.what₂.places.resChar w)`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Distinguish the cases in `hq : D.what₂.places.resChar w ∈ Q`. Rewrite using `[if_pos hq]`.

Rewrite using `[if_neg hq, hout w hw hq, mul_zero]`. Rewrite using `[h1, ← Finset.sum_fiberwise_of_maps_to (g := D.what₂.places.resChar) (t := Q) (fun w hw => (Finset.mem_filter.1 hw).2)]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `e1 : ∑ w ∈ (S.filter (fun w => D.what₂.places.resChar w ∈ Q)).filter (fun w => D.what₂.places.resChar w = p), Lnk.lE w * h (D.what₂.places.resChar w) = (∑ w ∈ (S.filter (fun w => D.what₂.places.resChar w ∈ Q)).filter (fun w => D.what₂.places.resChar w = p), Lnk.lE w) * h p`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hw).2]`. Rewrite using `[e1]`. Use `congr 1`. Conclude with `factEtaMean D p (hQ p hp) _ (fun w => ⟨fun hw => (Finset.mem_filter.1 hw).2, fun hw => Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hin p hp w hw, hw ▸ hp⟩, hw⟩⟩)`.
-/
theorem sum_places (S : Finset D.what₂.places.Pl) (Q : Finset ℕ) (h : ℕ → ℝ) (hQ : ∀ p ∈ Q, p.Prime)
    (hin : ∀ p ∈ Q, ∀ w, D.what₂.places.resChar w = p → w ∈ S)
    (hout : ∀ w ∈ S, D.what₂.places.resChar w ∉ Q → h (D.what₂.places.resChar w) = 0) :
    ∑ w ∈ S, Lnk.lE w * h (D.what₂.places.resChar w) = ∑ p ∈ Q, Real.log p * h p := by
  classical
  have h1 : ∑ w ∈ S, Lnk.lE w * h (D.what₂.places.resChar w) =
      ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w ∈ Q), Lnk.lE w * h (D.what₂.places.resChar w) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases hq : D.what₂.places.resChar w ∈ Q
    · rw [if_pos hq]
    · rw [if_neg hq, hout w hw hq, mul_zero]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := D.what₂.places.resChar) (t := Q)
    (fun w hw => (Finset.mem_filter.1 hw).2)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e1 : ∑ w ∈ (S.filter (fun w => D.what₂.places.resChar w ∈ Q)).filter (fun w => D.what₂.places.resChar w = p),
      Lnk.lE w * h (D.what₂.places.resChar w) =
      (∑ w ∈ (S.filter (fun w => D.what₂.places.resChar w ∈ Q)).filter (fun w => D.what₂.places.resChar w = p),
        Lnk.lE w) * h p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [(Finset.mem_filter.1 hw).2]
  rw [e1]
  congr 1
  exact factEtaMean D p (hQ p hp) _ (fun w => ⟨fun hw => (Finset.mem_filter.1 hw).2, fun hw =>
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hin p hp w hw, hw ▸ hp⟩, hw⟩⟩)

/- English proof (translation)
Take `⟨hx, -, ha, hX, -⟩` from `Lnk.sc_pos s`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Unfold `Scale.X'' Scale.w'' Scale.b'`. Clear the denominators using the available nonvanishing facts.
-/
theorem pa_Xpp_eq (s : Scale) (n : ℕ) (hn : (1 : ℝ) ≤ n) : s.X'' n = s.X' * (s.x * n) := by
  obtain ⟨hx, -, ha, hX, -⟩ := Lnk.sc_pos s
  have hn0 : (0 : ℝ) < n := by linarith
  unfold Scale.X'' Scale.w'' Scale.b'
  field_simp

/- English proof (translation)
Take `⟨hx, -, ha, hX, -⟩` from `Lnk.sc_pos s`. Rewrite using `[pa_Xpp_eq s n hn]`. Establish `h1 : 1 ≤ s.x * n` using `by nlinarith [s.one_lt_alt]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pa_Xp_le_Xpp (s : Scale) (n : ℕ) (hn : (1 : ℝ) ≤ n) : s.X' ≤ s.X'' n := by
  obtain ⟨hx, -, ha, hX, -⟩ := Lnk.sc_pos s
  rw [pa_Xpp_eq s n hn]
  have h1 : 1 ≤ s.x * n := by nlinarith [s.one_lt_alt]
  nlinarith

/- English proof (translation)
Unfold `G.VV`. Rewrite using `[if_neg (fun hh => h hh.1)]`.
-/
theorem pa_VV_empty (a b : G.HH D → ℤ) (p : ℕ) (h : ¬ G.Cand D L K p) : G.VV X K a b p = ∅ := by
  unfold G.VV
  rw [if_neg (fun hh => h hh.1)]

/- English proof (translation)
Unfold `G.tauP`. Rewrite using `[if_pos (pa_VV_empty X K a b p h)]`.
-/
theorem tauP_eq_zero_of_not_cand (a b : G.HH D → ℤ) (p : ℕ) (h : ¬ G.Cand D L K p) : G.tauP X K a b p = 0 := by
  unfold G.tauP
  rw [if_pos (pa_VV_empty X K a b p h)]

/- English proof (translation)
Unfold `G.ioP`. Rewrite using `[dif_neg]`. Rewrite using `[pa_VV_empty X K a b p h]`. Conclude with `Finset.not_nonempty_empty`.
-/
theorem ioP_eq_zero_of_not_cand₂ (a b : G.HH D → ℤ) (p : ℕ) (h : ¬ G.Cand D L K p) : G.ioP X K a b p = 0 := by
  unfold G.ioP
  rw [dif_neg]
  rw [pa_VV_empty X K a b p h]
  exact Finset.not_nonempty_empty

/- English proof (translation)
Introduce `hc`. Use `pa_Xp_le_Xpp L.sc D.R.n (Lnk.one_le_n D.R)` as an intermediate fact. Establish `h2` using `hc.2.1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pa_not_cand_above (p : ℕ) (h : L.sc.X'' D.R.n < (p : ℝ)) : ¬ G.Cand D L K p := by
  intro hc
  have := pa_Xp_le_Xpp L.sc D.R.n (Lnk.one_le_n D.R)
  have h2 := hc.2.1
  linarith

/- English proof (translation)
Unfold `gainQ G.gainP`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `absurd (Or.inr h) h2`.
-/
theorem pa_gainQ_above (j p : ℕ) (h : L.sc.X'' D.R.n < (p : ℝ)) : gainQ X K j p = 0 := by
  unfold gainQ G.gainP
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (Or.inr h) h2

/- English proof (translation)
Unfold `PsAt`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`.
-/
theorem pa_mem_PsAt {p : ℕ} : p ∈ PsAt L ↔ p < bndP L ∧ p.Prime ∧ InertK D p := by
  classical
  unfold PsAt
  rw [Finset.mem_filter, Finset.mem_range]

/- English proof (translation)
Unfold `bndP`. Establish `: p ≤ ⌊L.sc.X'' D.R.n⌋₊` using `Nat.le_floor h`. Establish `h2` using `le_max_right ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊ ⌊L.sc.X'' D.R.n⌋₊`. Use linear arithmetic over natural numbers and integers.
-/
theorem pa_lt_bndP {p : ℕ} (h : (p : ℝ) ≤ L.sc.X'' D.R.n) : p < bndP L := by
  unfold bndP
  have : p ≤ ⌊L.sc.X'' D.R.n⌋₊ := Nat.le_floor h
  have h2 := le_max_right ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊ ⌊L.sc.X'' D.R.n⌋₊
  omega

open Classical in

/- English proof (translation)
Take `⟨-, -, -, f4, f5, -, -⟩` from `H.fills w`. Distinguish the cases in `hI : InertK D (D.what₂.places.resChar w)`. Rewrite using `[if_pos hI, f5]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Unfold `SizeData₂.gainD gainQ`. Distinguish the cases in `hd : D.what₂.places.resChar w ∈ L.drop`. Rewrite using `[if_pos hd, if_pos hd]`. Rewrite using `[if_neg hd, if_neg hd]`. Conclude with `f4 hw (Or.symm hI) j hj`.

Rewrite using `[if_neg hI]`. Establish `hn` using `L.not_inert w (fun h => hI (Or.inl h)) (fun h => hI (Or.inr h))`. Rewrite using `[hn.2.1, sub_zero]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Unfold `SizeData₂.gainD`.

Use `split_ifs`. Both sides reduce to the same expression. Conclude with `hn.1 j`.
-/
theorem pa_entry (H : PtH X K Cr) (w : D.what₂.places.Pl) (hw : w ∈ L.supp) :
    (∑ j ∈ SizeData₂.lifts D, L.gainD j w) - L.tau w =
      (if InertK D (D.what₂.places.resChar w) then
        (∑ j ∈ SizeData₂.lifts D, gainQ X K j (D.what₂.places.resChar w)) -
          G.tauP X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) else 0) := by
  obtain ⟨-, -, -, f4, f5, -, -⟩ := H.fills w
  by_cases hI : InertK D (D.what₂.places.resChar w)
  · rw [if_pos hI, f5]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    unfold SizeData₂.gainD gainQ
    by_cases hd : D.what₂.places.resChar w ∈ L.drop
    · rw [if_pos hd, if_pos hd]
    · rw [if_neg hd, if_neg hd]
      exact f4 hw (Or.symm hI) j hj
  · rw [if_neg hI]
    have hn := L.not_inert w (fun h => hI (Or.inl h)) (fun h => hI (Or.inr h))
    rw [hn.2.1, sub_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold SizeData₂.gainD
    split_ifs
    · rfl
    · exact hn.1 j

/- English proof (translation)
Use `set h : ℕ → ℝ := fun p => if InertK D p then (∑ j ∈ SizeData₂.lifts D, gainQ X K j p) - G.tauP X K (G.aL L) (G.bL L) p else 0 with hh`. Establish `e1 : L.Ga = 2 * ∑ w ∈ L.supp, Lnk.lE w * h (D.what₂.places.resChar w)`. Unfold `SizeData₂.Ga`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations.

Apply the tactic sequence `rw [Lnk.sz_eq, pa_entry X K Cr H w hw]`. Establish `habove : ∀ p : ℕ, L.sc.X'' D.R.n < (p : ℝ) → (∑ j ∈ SizeData₂.lifts D, gainQ X K j p) - G.tauP X K (G.aL L) (G.bL L) p = 0`. Introduce `p hp`. Rewrite using `[tauP_eq_zero_of_not_cand X K _ _ p (pa_not_cand_above K p hp), sub_zero]`. Conclude with `Finset.sum_eq_zero fun j _ => pa_gainQ_above X K j p hp`.

Establish `e2` using `sum_places L.supp ((PsAt L).filter (fun p => (p : ℝ) ≤ L.sc.X'' D.R.n)) h (fun p hp => (pa_mem_PsAt.1 (Finset.mem_filter.1 hp).1).2.1) (fun p hp w hw => H.supp_sat w (by rw [hw]; exact (Finset.mem_filter.1 hp).2)) (fun w _ hq => by`. Distinguish the cases in `hI : InertK D (D.what₂.places.resChar w)`. Simplify using `only [hh, if_pos hI]`. Apply `habove` to reduce the goal to its premises. Assume the negation of the conclusion as `hle`.

Rewrite `hle` using `[not_lt]`. Conclude with `hq (Finset.mem_filter.2 ⟨pa_mem_PsAt.2 ⟨pa_lt_bndP hle, D.what₂.places.resChar_prime w, hI⟩, hle⟩)`. Simplify using `only [hh, if_neg hI])`. Rewrite using `[e1, e2]`. Use `show GaW (PsAt L) (SizeData₂.lifts D) (fun p => Real.log p) (gainQ X K) (G.tauP X K (G.aL L) (G.bL L)) = _`.

Unfold `GaW`. Use `congr 1`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hI` using `(pa_mem_PsAt.1 hp).2.2`.

Distinguish the cases in `hle : (p : ℝ) ≤ L.sc.X'' D.R.n`. Rewrite using `[if_pos hle]`. Simplify using `only [hh, if_pos hI]`. Rewrite using `[if_neg hle, habove p (not_le.1 hle), mul_zero]`.
-/
theorem Ga_at (H : PtH X K Cr) : (ldAt X K C bo).Ga (SizeData₂.lifts D) = L.Ga := by
  classical
  set h : ℕ → ℝ := fun p => if InertK D p then
        (∑ j ∈ SizeData₂.lifts D, gainQ X K j p) - G.tauP X K (G.aL L) (G.bL L) p else 0 with hh
  have e1 : L.Ga = 2 * ∑ w ∈ L.supp, Lnk.lE w * h (D.what₂.places.resChar w) := by
    unfold SizeData₂.Ga
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Lnk.sz_eq, pa_entry X K Cr H w hw]
  have habove : ∀ p : ℕ, L.sc.X'' D.R.n < (p : ℝ) →
      (∑ j ∈ SizeData₂.lifts D, gainQ X K j p) - G.tauP X K (G.aL L) (G.bL L) p = 0 := by
    intro p hp
    rw [tauP_eq_zero_of_not_cand X K _ _ p (pa_not_cand_above K p hp), sub_zero]
    exact Finset.sum_eq_zero fun j _ => pa_gainQ_above X K j p hp
  have e2 := sum_places L.supp ((PsAt L).filter (fun p => (p : ℝ) ≤ L.sc.X'' D.R.n)) h
    (fun p hp => (pa_mem_PsAt.1 (Finset.mem_filter.1 hp).1).2.1)
    (fun p hp w hw => H.supp_sat w (by rw [hw]; exact (Finset.mem_filter.1 hp).2))
    (fun w _ hq => by
      by_cases hI : InertK D (D.what₂.places.resChar w)
      · simp only [hh, if_pos hI]
        apply habove
        by_contra hle
        rw [not_lt] at hle
        exact hq (Finset.mem_filter.2 ⟨pa_mem_PsAt.2 ⟨pa_lt_bndP hle, D.what₂.places.resChar_prime w, hI⟩, hle⟩)
      · simp only [hh, if_neg hI])
  rw [e1, e2]
  show GaW (PsAt L) (SizeData₂.lifts D) (fun p => Real.log p) (gainQ X K) (G.tauP X K (G.aL L) (G.bL L)) = _
  unfold GaW
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hI := (pa_mem_PsAt.1 hp).2.2
  by_cases hle : (p : ℝ) ≤ L.sc.X'' D.R.n
  · rw [if_pos hle]
    simp only [hh, if_pos hI]
  · rw [if_neg hle, habove p (not_le.1 hle), mul_zero]

/- English proof (translation)
Unfold `sAt`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨fun h => h.2, fun h => ⟨Nat.lt_ceil.2 h.2.1, h⟩⟩`.
-/
theorem pa_mem_sAt {p : ℕ} : p ∈ sAt L K ↔ G.Cand D L K p := by
  classical
  unfold sAt
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_ceil.2 h.2.1, h⟩⟩

/- English proof (translation)
Establish `e1 : Lnk.IOsum L = ∑ w ∈ L.supp, Lnk.lE w * G.ioP X K (G.aL L) (G.bL L) (D.what₂.places.resChar w)`. Unfold `Lnk.IOsum`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[(H.fills w).2.2.2.2.2.1]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Use `(sum_places L.supp (sAt L K) _ (fun p hp => (pa_mem_sAt K |>.1 hp).1) (fun p hp w hw => ?_) (fun w _ hq => ?_)).symm` and prove the remaining obligations. Apply `H.supp_sat w` to reduce the goal to its premises. Rewrite using `[hw]`. Establish `h1` using `(pa_mem_sAt K |>.1 hp).2.1`.

Establish `h2` using `pa_Xp_le_Xpp L.sc D.R.n (Lnk.one_le_n D.R)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `ioP_eq_zero_of_not_cand₂ X K _ _ _ (fun hc => hq ((pa_mem_sAt K).2 hc))`.
-/
theorem IO_at (H : PtH X K Cr) :
    ∑ p ∈ sAt L K, Real.log p * G.ioP X K (G.aL L) (G.bL L) p = Lnk.IOsum L := by
  have e1 : Lnk.IOsum L = ∑ w ∈ L.supp, Lnk.lE w * G.ioP X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) := by
    unfold Lnk.IOsum
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [(H.fills w).2.2.2.2.2.1]
    rfl
  rw [e1]
  refine (sum_places L.supp (sAt L K) _ (fun p hp => (pa_mem_sAt K |>.1 hp).1) (fun p hp w hw => ?_)
    (fun w _ hq => ?_)).symm
  · apply H.supp_sat w
    rw [hw]
    have h1 := (pa_mem_sAt K |>.1 hp).2.1
    have h2 := pa_Xp_le_Xpp L.sc D.R.n (Lnk.one_le_n D.R)
    linarith
  · exact ioP_eq_zero_of_not_cand₂ X K _ _ _ (fun hc => hq ((pa_mem_sAt K).2 hc))

end AtRecord

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

section AtRecord

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ)

/- English proof (translation)
The claim follows from `D.R.toFrame.ofNat_val _`.
-/
theorem pb_cast (t : D.host.TT) : D.R.ofNat (t : D.R.A).val = (t : D.R.A) :=
  D.R.toFrame.ofNat_val _

/- English proof (translation)
Unfold `G.aL`. Rewrite using `[dif_pos t.2]`.
-/
theorem pb_aL (t : D.host.TT) : G.aL L (t : D.R.A) = L.aT t := by
  unfold G.aL
  rw [dif_pos t.2]

/- English proof (translation)
Unfold `TTv`. Rewrite using `[Finset.sum_image (fun a _ b _ h => Formalism.HC.Frame.A.val_injective _ h)]`. Conclude with `(Finset.sum_coe_sort D.host.TT (fun t => F t.val)).symm`.
-/
theorem pb_sum_TTv (F : ℕ → ℝ) : ∑ n ∈ TTv D, F n = ∑ t : D.host.TT, F (t : D.R.A).val := by
  unfold TTv
  rw [Finset.sum_image (fun a _ b _ h => Formalism.HC.Frame.A.val_injective _ h)]
  exact (Finset.sum_coe_sort D.host.TT (fun t => F t.val)).symm

/- English proof (translation)
Take `⟨w0, hw0⟩` from `Lnk.place_over D p hp`. Establish `f2` using `(H.fills w0).2.1`. Rewrite `f2` using `[hw0]`. Unfold `askAt SizeData₂.vonMangoldtClassSum`. Simplify using `only [ldAt, pb_cast, pb_aL]`.

Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : Odd i`. Rewrite using `[if_pos hi, if_pos hi, f2 j t i, max_comm]`. Rewrite using `[if_neg hi, if_neg hi]`.
-/
theorem ask_at (H : PtH X K Cr) (j : ℕ) (_hj : j ∈ SizeData₂.lifts D) (t : D.host.TT) (p : ℕ) (hp : p.Prime) (_hI : InertK D p) :
    askAt ((ldAt X K C bo).Iex j (t : D.R.A).val p) ((ldAt X K C bo).at_ (t : D.R.A).val) p
      ((ldAt X K C bo).wz j (t : D.R.A).val p) = L.vonMangoldtClassSum j t p := by
  obtain ⟨w0, hw0⟩ := Lnk.place_over D p hp
  have f2 := (H.fills w0).2.1
  rw [hw0] at f2
  unfold askAt SizeData₂.vonMangoldtClassSum
  simp only [ldAt, pb_cast, pb_aL]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : Odd i
  · rw [if_pos hi, if_pos hi, f2 j t i, max_comm]
  · rw [if_neg hi, if_neg hi]

/- English proof (translation)
Unfold `SizeData₂.vonMangoldtClassSum`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : Odd i`. Rewrite using `[if_pos hi]`. Establish `hlt : (L.aT t).toNat < p ^ i` using `lt_of_lt_of_le hp (Nat.le_self_pow (by have := hi.pos; omega) p)`.

Use `Lnk.term0 L t (L.wPart_ge j t p i) hlt` as an intermediate fact. Rewrite `this` using `[Nat.cast_pow]`. Rewrite using `[max_comm]`. Conclude with `this`. Rewrite using `[if_neg hi]`.
-/
theorem pb_ask_zero (j : ℕ) (t : D.host.TT) (p : ℕ) (hp : (L.aT t).toNat < p) : L.vonMangoldtClassSum j t p = 0 := by
  unfold SizeData₂.vonMangoldtClassSum
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hi : Odd i
  · rw [if_pos hi]
    have hlt : (L.aT t).toNat < p ^ i := lt_of_lt_of_le hp (Nat.le_self_pow (by have := hi.pos; omega) p)
    have := Lnk.term0 L t (L.wPart_ge j t p i) hlt
    rw [Nat.cast_pow] at this
    rw [max_comm]
    exact this
  · rw [if_neg hi]

/- English proof (translation)
Unfold `bndP`. Establish `h1 : (L.aT t).toNat ≤ ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊`. Apply `Nat.le_floor` to reduce the goal to its premises. Rewrite using `[← Lnk.aT_toNat L t]`. Conclude with `(L.aT_win t).2`.

Establish `h2` using `le_max_left ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊ ⌊L.sc.X'' D.R.n⌋₊`. Use linear arithmetic over natural numbers and integers.
-/
theorem pb_toNat_lt (t : D.host.TT) : (L.aT t).toNat < bndP L := by
  unfold bndP
  have h1 : (L.aT t).toNat ≤ ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊ := by
    apply Nat.le_floor
    rw [← Lnk.aT_toNat L t]
    exact (L.aT_win t).2
  have h2 := le_max_left ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊ ⌊L.sc.X'' D.R.n⌋₊
  omega

open Classical in
/- English proof (translation)
Establish `e1 : ∑ p ∈ PsAt L, 2 * Real.log p * askAt ((ldAt X K C bo).Iex j (t : D.R.A).val p) ((ldAt X K C bo).at_ (t : D.R.A).val) p ((ldAt X K C bo).wz j (t : D.R.A).val p) = ∑ p ∈ PsAt L, 2 * Real.log p * L.vonMangoldtClassSum j t p`. Use `Finset.sum_congr rfl (fun p hp => ?_)` and prove the remaining obligations. Establish `hp'` using `(Finset.mem_filter.mp hp).2`. Rewrite using `[ask_at X K Cr C bo H j hj t p hp'.1 hp'.2]`. Rewrite using `[e1]`.

Use `symm`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `p hp`. Take `⟨hp1, hp2⟩` from `Finset.mem_filter.mp hp`. Take `⟨hp3, hp4⟩` from `Finset.mem_filter.mp hp1`.

Use `pb_toNat_lt (L := L) t` as an intermediate fact. Establish `h5` using `Finset.mem_range.mp hp3`. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp4, hp2⟩`. Introduce `p hp hn`. Establish `hp'` using `(Finset.mem_filter.mp hp).2`.

Establish `hlt : (L.aT t).toNat < p`. Assume the negation of the conclusion as `hcon`. Conclude with `hn (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp'.1⟩, hp'.2⟩)`. Rewrite using `[pb_ask_zero j t p hlt, mul_zero]`.
-/
theorem pb_primes (H : PtH X K Cr) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : D.host.TT) :
    ∑ p ∈ PsAt L, 2 * Real.log p *
      askAt ((ldAt X K C bo).Iex j (t : D.R.A).val p) ((ldAt X K C bo).at_ (t : D.R.A).val) p
        ((ldAt X K C bo).wz j (t : D.R.A).val p) =
    ∑ p ∈ (LocalQuadraticParts.askPrimes (L.aT t)).filter (fun p => DV.InertK D p), 2 * Real.log p * L.vonMangoldtClassSum j t p := by
  have e1 : ∑ p ∈ PsAt L, 2 * Real.log p *
      askAt ((ldAt X K C bo).Iex j (t : D.R.A).val p) ((ldAt X K C bo).at_ (t : D.R.A).val) p
        ((ldAt X K C bo).wz j (t : D.R.A).val p) = ∑ p ∈ PsAt L, 2 * Real.log p * L.vonMangoldtClassSum j t p := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' := (Finset.mem_filter.mp hp).2
    rw [ask_at X K Cr C bo H j hj t p hp'.1 hp'.2]
  rw [e1]
  symm
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp3, hp4⟩ := Finset.mem_filter.mp hp1
    have := pb_toNat_lt (L := L) t
    have h5 := Finset.mem_range.mp hp3
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp4, hp2⟩
  · intro p hp hn
    have hp' := (Finset.mem_filter.mp hp).2
    have hlt : (L.aT t).toNat < p := by
      by_contra hcon
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp'.1⟩, hp'.2⟩)
    rw [pb_ask_zero j t p hlt, mul_zero]

open Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ZetaZeroFreeRegion Formalism.MainNotions.ZetaZeroFreeRegion.Br in
/- English proof (translation)
Establish `hj'` using `Finset.mem_Icc.mp hj`. Unfold `askAt ZetaZeroFreeRegion.askD`. Simplify using `only [ldAt, pb_cast, pb_aL]`. Rewrite using `[tsum_eq_sum (s := Finset.Icc 1 (Nat.log D.host.d (L.aT t).toNat + 1))]`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations.

Rewrite using `[if_pos (Finset.mem_Icc.mp hi).1]`. Introduce `i hi`. Distinguish the cases in `hc : 1 ≤ i`. Rewrite using `[if_pos hc]`. Establish `hi' : Nat.log D.host.d (L.aT t).toNat + 2 ≤ i`.

Assume the negation of the conclusion as `hcon`. Conclude with `hi (Finset.mem_Icc.mpr ⟨hc, by omega⟩)`. Establish `hlt : (L.aT t).toNat < D.host.d ^ i` using `lt_of_lt_of_le (Nat.lt_pow_succ_log_self D.host.hyp.2.1.one_lt _) (Nat.pow_le_pow_right D.host.hyp.2.1.pos (by omega))`. Establish `hg : gD D i ∉ D.R.Psi` using `fun h => (gD_spec D i).2 ((inPhi_iff D _).2 h)`. Use `Lnk.term0 L t (Lnk.one_le_wAt L H.numN j hj'.1 hj'.2 _ (rho_mem D (t : D.R.A) hg)) hlt` as an intermediate fact.

Rewrite `this` using `[Nat.cast_pow]`. Then use the resulting hypothesis. Rewrite using `[if_neg hc]`.
-/
theorem pb_atD (H : PtH X K Cr) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : D.host.TT) :
    askAt ((ldAt X K C bo).Id j (t : D.R.A).val) ((ldAt X K C bo).at_ (t : D.R.A).val) D.host.d
        ((ldAt X K C bo).wd j (t : D.R.A).val) =
      ZetaZeroFreeRegion.askD D (L.aT t : ℝ) (LocalQuadraticParts.wAt D j) (D.R.tau1 (t : D.R.A)) := by
  have hj' := Finset.mem_Icc.mp hj
  unfold askAt ZetaZeroFreeRegion.askD
  simp only [ldAt, pb_cast, pb_aL]
  rw [tsum_eq_sum (s := Finset.Icc 1 (Nat.log D.host.d (L.aT t).toNat + 1))]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_pos (Finset.mem_Icc.mp hi).1]
  · intro i hi
    by_cases hc : 1 ≤ i
    · rw [if_pos hc]
      have hi' : Nat.log D.host.d (L.aT t).toNat + 2 ≤ i := by
        by_contra hcon
        exact hi (Finset.mem_Icc.mpr ⟨hc, by omega⟩)
      have hlt : (L.aT t).toNat < D.host.d ^ i :=
        lt_of_lt_of_le (Nat.lt_pow_succ_log_self D.host.hyp.2.1.one_lt _)
          (Nat.pow_le_pow_right D.host.hyp.2.1.pos (by omega))
      have hg : gD D i ∉ D.R.Psi := fun h => (gD_spec D i).2 ((inPhi_iff D _).2 h)
      have := Lnk.term0 L t (Lnk.one_le_wAt L H.numN j hj'.1 hj'.2 _ (rho_mem D (t : D.R.A) hg)) hlt
      rwa [Nat.cast_pow] at this
    · rw [if_neg hc]

/- English proof (translation)
Unfold `LD.ASK Formalism.LFunctionChainParameters.DeficitSplitLemmas.ASK LocalQuadraticParts.ASK`. Use `Finset.sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Rewrite using `[pb_sum_TTv]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[pb_primes X K Cr C bo H j hj t]`.

Use `show _ + Real.log (D.host.d : ℝ) * askAt ((ldAt X K C bo).Id j (t : D.R.A).val) ((ldAt X K C bo).at_ (t : D.R.A).val) D.host.d ((ldAt X K C bo).wd j (t : D.R.A).val) = _`. Rewrite using `[pb_atD X K Cr C bo H j hj t]`.
-/
theorem ASK_at (H : PtH X K Cr) :
    (ldAt X K C bo).ASK D.host.d (PsAt L) (SizeData₂.lifts D) (TTv D) = LocalQuadraticParts.ASK L := by
  unfold LD.ASK Formalism.LFunctionChainParameters.DeficitSplitLemmas.ASK LocalQuadraticParts.ASK
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [pb_sum_TTv]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [pb_primes X K Cr C bo H j hj t]
  show _ + Real.log (D.host.d : ℝ) * askAt ((ldAt X K C bo).Id j (t : D.R.A).val)
    ((ldAt X K C bo).at_ (t : D.R.A).val) D.host.d ((ldAt X K C bo).wd j (t : D.R.A).val) = _
  rw [pb_atD X K Cr C bo H j hj t]

end AtRecord

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

/- English proof (translation)
Take `⟨⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩, ⟨sc, Sc, η⟩, ⟨bs, h1, h2, off, h3, h4, h5, kapI, ep⟩, a, b⟩` from `A`. Take `⟨⟨R', ⟨TT', T2', u0', cls'⟩, hPf'⟩, ⟨sc', Sc', η'⟩, ⟨bs', h1', h2', off', h3', h4', h5', kapI', ep'⟩, a', b'⟩` from `A'`. Simplify using `only at hR`. Substitute `hR` using the available equality. Simplify using `only at hTT hcls hhP hsc hbs`.

Establish `eTT : TT = TT'` using `Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT`. Establish `ehP : hPf = hPf'` using `funext fun p => Formalism.HC.Frame.A.val_injective _ (hhP p)`. Establish `ebs : bs = bs'` using `funext fun h => funext fun t => Formalism.HC.Frame.A.val_injective _ (hbs h t h t rfl rfl)`. Substitute `eTT hcls ehP hsc ebs` using the available equality. Conclude with `⟨Iff.rfl, Iff.rfl, rfl, rfl⟩`.
-/
theorem pg_sameMore (K : G.Consts) (A A' : GAll) (hR : A.D.R = A'.D.R)
    (hTT : A.D.host.TT.image Formalism.HC.Frame.A.val = A'.D.host.TT.image Formalism.HC.Frame.A.val)
    (hcls : A.D.host.cls = A'.D.host.cls) (hhP : ∀ p, (A.D.hPf p).val = (A'.D.hPf p).val)
    (hsc : A.L.sc = A'.L.sc)
    (hbs : ∀ (h t : GC.HH A.D) (h' t' : GC.HH A'.D), h.val = h'.val → t.val = t'.val →
      (A.X.bs h t).val = (A'.X.bs h' t').val) (p n : ℕ) :
    (GC.Cand A.D A.L K p ↔ GC.Cand A'.D A'.L K p) ∧
    (GC.Good A.X p (A.X.bs (GC.stepP A.D p) (A.D.R.ofNat n)) ↔
      GC.Good A'.X p (A'.X.bs (GC.stepP A'.D p) (A'.D.R.ofNat n))) ∧
    addOrderOf (GC.hP A.D p) = addOrderOf (GC.hP A'.D p) ∧
    GC.rhoB A.D K A.L.sc = GC.rhoB A'.D K A'.L.sc := by
  obtain ⟨⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩, ⟨sc, Sc, η⟩, ⟨bs, h1, h2, off, h3, h4, h5, kapI, ep⟩, a, b⟩ := A
  obtain ⟨⟨R', ⟨TT', T2', u0', cls'⟩, hPf'⟩, ⟨sc', Sc', η'⟩, ⟨bs', h1', h2', off', h3', h4', h5', kapI', ep'⟩, a', b'⟩ := A'
  simp only at hR
  subst hR
  simp only at hTT hcls hhP hsc hbs
  have eTT : TT = TT' := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have ehP : hPf = hPf' := funext fun p => Formalism.HC.Frame.A.val_injective _ (hhP p)
  have ebs : bs = bs' := funext fun h => funext fun t => Formalism.HC.Frame.A.val_injective _ (hbs h t h t rfl rfl)
  subst eTT hcls ehP hsc ebs
  exact ⟨Iff.rfl, Iff.rfl, rfl, rfl⟩

section Family

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ} {i0 : Fm.Ix x}

/- English proof (translation)
Conclude with `host_cls_eq (Fm.q_eq x i i') (Fm.d_eq x i i') (Fm.QS_eq x i i')`.
-/
theorem pg_cls (i i' : Fm.Ix x) : (Fm.D x i).host.cls = (Fm.D x i').host.cls := by
  exact host_cls_eq (Fm.q_eq x i i') (Fm.d_eq x i i') (Fm.QS_eq x i i')

/- English proof (translation)
The claim follows from `(Fm.TT_eq x i).trans (Fm.TT_eq x i').symm`.
-/
theorem pg_TT (i i' : Fm.Ix x) : (Fm.D x i).host.TT.image Formalism.HC.Frame.A.val = (Fm.D x i').host.TT.image Formalism.HC.Frame.A.val :=
  (Fm.TT_eq x i).trans (Fm.TT_eq x i').symm

/- English proof (translation)
The claim follows from `pg_sameMore Fm.GK (allOf (Fm.Gx x i)) (allOf (Fm.Gx x i')) (Fm.R_eq x i i') (pg_TT i i') (pg_cls i i') (Fm.hP_eq x i i') (Lnk.sc_eq Fm hx i i') (Fm.bs_eq x i i') p n`.
-/
theorem pg_more (hx : Fm.x1 < x) (i i' : Fm.Ix x) (p n : ℕ) :
    (G.Cand (Fm.D x i) (Fm.L x i) Fm.GK p ↔ G.Cand (Fm.D x i') (Fm.L x i') Fm.GK p) ∧
    (G.Good (Fm.Gx x i) p ((Fm.Gx x i).bs (G.stepP (Fm.D x i) p) ((Fm.D x i).R.ofNat n)) ↔
      G.Good (Fm.Gx x i') p ((Fm.Gx x i').bs (G.stepP (Fm.D x i') p) ((Fm.D x i').R.ofNat n))) ∧
    addOrderOf (G.hP (Fm.D x i) p) = addOrderOf (G.hP (Fm.D x i') p) ∧
    G.rhoB (Fm.D x i) Fm.GK (Fm.L x i).sc = G.rhoB (Fm.D x i') Fm.GK (Fm.L x i').sc :=
  pg_sameMore Fm.GK (allOf (Fm.Gx x i)) (allOf (Fm.Gx x i')) (Fm.R_eq x i i') (pg_TT i i') (pg_cls i i')
    (Fm.hP_eq x i i') (Lnk.sc_eq Fm hx i i') (Fm.bs_eq x i i') p n

/- English proof (translation)
Unfold `InertK`. Rewrite using `[pg_cls i i']`.
-/
theorem pg_inert (i i' : Fm.Ix x) (p : ℕ) : InertK (Fm.D x i) p ↔ InertK (Fm.D x i') p := by
  unfold InertK
  rw [pg_cls i i']

/- English proof (translation)
Unfold `bndP`. Rewrite using `[Lnk.sc_eq Fm hx i i', Fm.R_eq x i i']`.
-/
theorem pg_bndP (hx : Fm.x1 < x) (i i' : Fm.Ix x) : bndP (Fm.L x i) = bndP (Fm.L x i') := by
  unfold bndP
  rw [Lnk.sc_eq Fm hx i i', Fm.R_eq x i i']

open Classical in
/- English proof (translation)
Use extensionality with `p`. Unfold `PsAt`. Rewrite using `[Finset.mem_filter, Finset.mem_filter, pg_bndP hx i i0, pg_inert i i0 p]`.
-/
theorem PsAt_eq (hx : Fm.x1 < x) (i : Fm.Ix x) : PsAt (Fm.L x i) = PsAt (Fm.L x i0) := by
  ext p
  unfold PsAt
  rw [Finset.mem_filter, Finset.mem_filter, pg_bndP hx i i0, pg_inert i i0 p]

open Classical in
/- English proof (translation)
Use extensionality with `p`. Unfold `sAt`. Rewrite using `[Finset.mem_filter, Finset.mem_filter, Lnk.sc_eq Fm hx i i0, (pg_more hx i i0 p 0).1]`.
-/
theorem sAt_eq (hx : Fm.x1 < x) (i : Fm.Ix x) : sAt (Fm.L x i) Fm.GK = sAt (Fm.L x i0) Fm.GK := by
  ext p
  unfold sAt
  rw [Finset.mem_filter, Finset.mem_filter, Lnk.sc_eq Fm hx i i0, (pg_more hx i i0 p 0).1]

open Classical in
/- English proof (translation)
Use extensionality with `p`. Unfold `largeOrderResiduePrimes`. Rewrite using `[Finset.mem_filter, Finset.mem_filter, Lnk.sc_eq Fm hx i i0, (pg_more hx i i0 p 0).2.2.1]`. Unfold `G.IsResidueClassZero`. Rewrite using `[pg_cls i i0]`.
-/
theorem large_order_primes_eq_filter (hx : Fm.x1 < x) (i : Fm.Ix x) : largeOrderResiduePrimes (Fm.L x i) = largeOrderResiduePrimes (Fm.L x i0) := by
  ext p
  unfold largeOrderResiduePrimes
  rw [Finset.mem_filter, Finset.mem_filter, Lnk.sc_eq Fm hx i i0, (pg_more hx i i0 p 0).2.2.1]
  unfold G.IsResidueClassZero
  rw [pg_cls i i0]

/- English proof (translation)
Unfold `SizeData₂.lifts`. Rewrite using `[Fm.R_eq x i i0]`.
-/
theorem lifts_eq (i : Fm.Ix x) : SizeData₂.lifts (Fm.D x i) = SizeData₂.lifts (Fm.D x i0) := by
  unfold SizeData₂.lifts
  rw [Fm.R_eq x i i0]

/- English proof (translation)
Rewrite using `[← Fm.TT_eq x i, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hst⟩`. Conclude with `Formalism.HC.Frame.A.val_injective _ hst ▸ hs`. Introduce `h`.

Conclude with `⟨t, h, rfl⟩`.
-/
theorem pg_mem_TTn (i : Fm.Ix x) (t : G.HH (Fm.D x i)) : t.val ∈ Fm.TTn x ↔ t ∈ (Fm.D x i).host.TT := by
  rw [← Fm.TT_eq x i, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hst⟩
    exact Formalism.HC.Frame.A.val_injective _ hst ▸ hs
  · intro h
    exact ⟨t, h, rfl⟩

/- English proof (translation)
Unfold `G.aL G.bL aO bO`. Rewrite using `[← ht]`. Distinguish the cases in `h : t ∈ (Fm.D x i).host.TT`. Rewrite using `[dif_pos h, dif_pos h]`. Conclude with `hc ⟨t, h⟩`.

Establish `h' : t.val ∉ Fm.TTn x` using `fun hh => h ((pg_mem_TTn i t).1 hh)`. Rewrite using `[dif_neg h, dif_neg h]`. Unfold `Lnk.avOf Lnk.bvOf`. Rewrite using `[dif_neg h', dif_neg h']`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem pg_aL (i : Fm.Ix x) (o : Lnk.Wt Fm x i0) (hc : Lnk.Carries Fm i (Lnk.avOf o) (Lnk.bvOf o))
    (t : G.HH (Fm.D x i)) (t' : G.HH (Fm.D x i0)) (ht : t.val = t'.val) :
    G.aL (Fm.L x i) t = aO o t' ∧ G.bL (Fm.L x i) t = bO o t' := by
  unfold G.aL G.bL aO bO
  rw [← ht]
  by_cases h : t ∈ (Fm.D x i).host.TT
  · rw [dif_pos h, dif_pos h]
    exact hc ⟨t, h⟩
  · have h' : t.val ∉ Fm.TTn x := fun hh => h ((pg_mem_TTn i t).1 hh)
    rw [dif_neg h, dif_neg h]
    unfold Lnk.avOf Lnk.bvOf
    rw [dif_neg h', dif_neg h']
    exact ⟨rfl, rfl⟩

/- English proof (translation)
The claim follows from `(J.sameServed Fm.GK (allOf (Fm.Gx x i)) ⟨viewD (Fm.D x i0), viewL (Fm.L x i0), viewX (Fm.Gx x i0), aO o, bO o⟩ (Fm.R_eq x i i0) (pg_TT i i0) (pg_cls i i0) (Fm.hP_eq x i i0) (Lnk.sc_eq Fm hx i i0) (Fm.Sc_shared x i i0) (Fm.eta_eq x i i0) (Fm.bs_eq x i i0) (Fm.off_eq x i i0) (Fm.ka …`.
-/
theorem Sig_eq (hx : Fm.x1 < x) (i : Fm.Ix x) (o : Lnk.Wt Fm x i0) (hc : Lnk.Carries Fm i (Lnk.avOf o) (Lnk.bvOf o)) (p : ℕ) :
    G.Sig (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p = SigO p o :=
  (J.sameServed Fm.GK (allOf (Fm.Gx x i))
    ⟨viewD (Fm.D x i0), viewL (Fm.L x i0), viewX (Fm.Gx x i0), aO o, bO o⟩ (Fm.R_eq x i i0) (pg_TT i i0) (pg_cls i i0)
    (Fm.hP_eq x i i0) (Lnk.sc_eq Fm hx i i0) (Fm.Sc_shared x i i0) (Fm.eta_eq x i i0) (Fm.bs_eq x i i0) (Fm.off_eq x i i0)
    (Fm.kapI_eq x i i0) (Fm.ep_eq x i i0) (fun t t' ht => (pg_aL i o hc t t' ht).1)
    (fun t t' ht => (pg_aL i o hc t t' ht).2) p).2.1

/- English proof (translation)
Unfold `badAt`. Rewrite using `[(pg_more hx i i0 p n).2.1]`.
-/
theorem badAt_iff (hx : Fm.x1 < x) (i : Fm.Ix x) (p n : ℕ) : badAt (Fm.Gx x i) p n ↔ badAt (Fm.Gx x i0) p n := by
  unfold badAt
  rw [(pg_more hx i i0 p n).2.1]

/- English proof (translation)
Take `⟨w, -⟩` from `Lnk.place_over (Fm.D x i) 2 Nat.prime_two`. Conclude with `(Fm.fills x hx i w).2.2.2.2.2.2.symm`.
-/
theorem pg_LaG (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.L x i).LaG = G.La Fm.GK (Fm.L x i).sc := by
  obtain ⟨w, -⟩ := Lnk.place_over (Fm.D x i) 2 Nat.prime_two
  exact (Fm.fills x hx i w).2.2.2.2.2.2.symm

/- English proof (translation)
Establish `hsc` using `Lnk.sc_eq Fm hx i0 i`. Establish `hR` using `Fm.R_eq x i0 i`. Establish `hrho` using `(pg_more hx i0 i 0 0).2.2.2`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (Fm.L x i0).sc.x = _`.

Rewrite using `[hsc]`. Use `show (Fm.L x i0).sc.eps = _`. Rewrite using `[hsc]`. Use `show (Fm.D x i0).R.e = _`. Rewrite using `[hR]`.

Use `show ((Fm.D x i0).R.n : ℝ) = _`. Rewrite using `[hR]`. Use `show ((Fm.D x i0).R.k : ℝ) = _`. Rewrite using `[hR]`. Use `show ((Fm.D x i0).R.N (Fm.D x i0).R.m : ℝ) = _`.

Rewrite using `[hR]`. Use `show ((Fm.D x i0).R.t : ℝ) = _`. Rewrite using `[hR]`. Use `show ⌈(Fm.L x i0).sc.p0 (Fm.D x i0).R.k⌉₊ = _`. Rewrite using `[hsc, hR]`.

Use `show (Fm.L x i0).LaG = _`. Rewrite using `[pg_LaG hx i0, pg_LaG hx i, hsc]`. Use `show (Formalism.MainNotions.rG (Fm.L x i0).sc.eps : ℝ) = _`. Rewrite using `[hsc]`. Conclude with `Fm.Sc_shared x i0 i`.

Conclude with `Fm.eta_eq x i0 i`. Conclude with `hrho`. Use `show 1 / (((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.x ^ (Scale.A / 2)) = _`. Rewrite using `[hsc, hR]`. Use `show ((Fm.D x i0).R.k : ℝ) ^ 2 * (Fm.L x i0).sc.x ^ (3 * Scale.A) = _`.

Rewrite using `[hsc, hR]`. Conclude with `Fm.d_eq x i0 i`. Both sides reduce to the same expression. Use `show (Fm.L x i0).sc.X' * (1 + Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc) = _`. Rewrite using `[hrho, hsc]`.

Both sides reduce to the same expression.
-/
theorem parTie (hx : Fm.x1 < x) (i : Fm.Ix x) (C bo Cb Cord : ℝ) :
    ParTie (par Fm x i0 C bo Cb Cord) (Fm.L x i) Fm.GK C bo Fm.Cr := by
  have hsc := Lnk.sc_eq Fm hx i0 i
  have hR := Fm.R_eq x i0 i
  have hrho := (pg_more hx i0 i 0 0).2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (Fm.L x i0).sc.x = _; rw [hsc]
  · show (Fm.L x i0).sc.eps = _; rw [hsc]
  · show (Fm.D x i0).R.e = _; rw [hR]
  · show ((Fm.D x i0).R.n : ℝ) = _; rw [hR]
  · show ((Fm.D x i0).R.k : ℝ) = _; rw [hR]
  · show ((Fm.D x i0).R.N (Fm.D x i0).R.m : ℝ) = _; rw [hR]
  · show ((Fm.D x i0).R.t : ℝ) = _; rw [hR]
  · show ⌈(Fm.L x i0).sc.p0 (Fm.D x i0).R.k⌉₊ = _; rw [hsc, hR]
  · show (Fm.L x i0).LaG = _; rw [pg_LaG hx i0, pg_LaG hx i, hsc]
  · show (Formalism.MainNotions.rG (Fm.L x i0).sc.eps : ℝ) = _; rw [hsc]
  · exact Fm.Sc_shared x i0 i
  · exact Fm.eta_eq x i0 i
  · exact hrho
  · show 1 / (((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.x ^ (Scale.A / 2)) = _; rw [hsc, hR]
  · show ((Fm.D x i0).R.k : ℝ) ^ 2 * (Fm.L x i0).sc.x ^ (3 * Scale.A) = _; rw [hsc, hR]
  · exact Fm.d_eq x i0 i
  · rfl
  · show (Fm.L x i0).sc.X' * (1 + Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc) = _; rw [hrho, hsc]
  · rfl

open Classical in
/- English proof (translation)
Establish `hcast : ∀ t : G.HH (Fm.D x i0), (Fm.D x i0).R.ofNat t.val = t` using `fun t => (Fm.D x i0).R.toFrame.ofNat_val t`. Establish `himg : (Fm.TTn x).filter (fun n => badAt (Fm.Gx x i0) p n) = (badTops (Fm.Gx x i0) p).image Formalism.HC.Frame.A.val`. Use extensionality with `n`. Rewrite using `[Finset.mem_filter, Finset.mem_image, ← Fm.TT_eq x i0, Finset.mem_image]`. Unfold `badTops badAt`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨t, ht, rfl⟩, hb⟩`. Rewrite `hb` using `[hcast]`. Conclude with `⟨t, Finset.mem_filter.2 ⟨ht, hb⟩, rfl⟩`. Introduce and unpack `⟨t, ht, rfl⟩`.

Take `⟨h1, h2⟩` from `Finset.mem_filter.1 ht`. Rewrite using `[hcast]`. Conclude with `⟨⟨t, h1, rfl⟩, h2⟩`. Rewrite using `[himg, Finset.card_image_of_injective _ (Formalism.HC.Frame.A.val_injective _)]`.
-/
theorem bad_card (p : ℕ) : ((Fm.TTn x).filter (fun n => badAt (Fm.Gx x i0) p n)).card = (badTops (Fm.Gx x i0) p).card := by
  have hcast : ∀ t : G.HH (Fm.D x i0), (Fm.D x i0).R.ofNat t.val = t := fun t => (Fm.D x i0).R.toFrame.ofNat_val t
  have himg : (Fm.TTn x).filter (fun n => badAt (Fm.Gx x i0) p n) = (badTops (Fm.Gx x i0) p).image Formalism.HC.Frame.A.val := by
    ext n
    rw [Finset.mem_filter, Finset.mem_image, ← Fm.TT_eq x i0, Finset.mem_image]
    unfold badTops badAt
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hb⟩
      rw [hcast] at hb
      exact ⟨t, Finset.mem_filter.2 ⟨ht, hb⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ht
      rw [hcast]
      exact ⟨⟨t, h1, rfl⟩, h2⟩
  rw [himg, Finset.card_image_of_injective _ (Formalism.HC.Frame.A.val_injective _)]

end Family

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

section AtRecordC

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ)

/- English proof (translation)
Unfold `PsAt`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`.
-/
theorem pc_mem_Ps {p : ℕ} : p ∈ PsAt L ↔ p < bndP L ∧ p.Prime ∧ InertK D p := by
  classical
  unfold PsAt
  rw [Finset.mem_filter, Finset.mem_range]

/- English proof (translation)
Take `⟨hx, hb, ha, hX, hb'⟩` from `Lnk.sc_pos L.sc`. Establish `hn` using `Lnk.one_le_n D.R`. Establish `h1` using `L.sc.one_lt_alt`. Establish `e : L.sc.X'' D.R.n = L.sc.X' * (L.sc.x * D.R.n)`. Unfold `Scale.X'' Scale.w'' Scale.b'`.

Establish `hn0 : (D.R.n : ℝ) ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `: 1 ≤ L.sc.x * D.R.n` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pc_X'_le (L : SizeData₂ D) : L.sc.X' ≤ L.sc.X'' D.R.n := by
  obtain ⟨hx, hb, ha, hX, hb'⟩ := Lnk.sc_pos L.sc
  have hn := Lnk.one_le_n D.R
  have h1 := L.sc.one_lt_alt
  have e : L.sc.X'' D.R.n = L.sc.X' * (L.sc.x * D.R.n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    have hn0 : (D.R.n : ℝ) ≠ 0 := by linarith
    field_simp
  rw [e]
  have : 1 ≤ L.sc.x * D.R.n := by nlinarith
  nlinarith

/- English proof (translation)
Take `⟨hx, hb, ha, hX, hb'⟩` from `Lnk.sc_pos L.sc`. Establish `h1 : 0 ≤ K.La` using `hK.1`. Establish `h2 : 0 ≤ K.rho` using `hK.2.1`. Establish `h2' : 0 ≤ K.CN` using `hK.2.2.2.2.2.2.2.2.2.2.2.2.2.2`. Establish `hlx : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg L.sc.one_lt_alt.le`.

Establish `hb1` using `Lnk.one_le_b L.sc`. Establish `ha1 : 1 ≤ L.sc.a`. Unfold `Scale.a`. Use `L.sc.one_lt_alt` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hlog : 0 ≤ Real.log L.sc.a` using `Real.log_nonneg ha1`. Establish `hLa : 0 ≤ G.La K L.sc`. Unfold `G.La`. Check the signs of the components of the expression. Establish `hd : 0 ≤ L.sc.delta1`.

Unfold `Scale.delta1`. Check the signs of the components of the expression. Establish `hN : 0 ≤ G.Nstar D L.sc`. Unfold `G.Nstar`. Check the signs of the components of the expression.

Establish `hxe : 0 ≤ L.sc.x ^ L.sc.eps` using `Real.rpow_nonneg hx.le _`. Unfold `G.rhoB`. Check the signs of the components of the expression.
-/
theorem pc_rho_nonneg (hK : K.Nonneg) (L : SizeData₂ D) : 0 ≤ G.rhoB D K L.sc := by
  obtain ⟨hx, hb, ha, hX, hb'⟩ := Lnk.sc_pos L.sc
  have h1 : 0 ≤ K.La := hK.1
  have h2 : 0 ≤ K.rho := hK.2.1
  have h2' : 0 ≤ K.CN := hK.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have hb1 := Lnk.one_le_b L.sc
  have ha1 : 1 ≤ L.sc.a := by
    unfold Scale.a
    have := L.sc.one_lt_alt
    nlinarith
  have hlog : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have hLa : 0 ≤ G.La K L.sc := by
    unfold G.La
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have hN : 0 ≤ G.Nstar D L.sc := by
    unfold G.Nstar
    positivity
  have hxe : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx.le _
  unfold G.rhoB
  positivity

/- English proof (translation)
Unfold `clAt`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Rewrite `h` using `[if_neg (not_not.2 hc)]`.

Use `split_ifs at h`. Introduce `h`. Rewrite using `[if_pos h]`.
-/
theorem pc_served_iff (p : ℕ) : clAt X K p = PClass.served ↔ p ∉ L.drop := by
  classical
  unfold clAt
  constructor
  · intro h
    by_contra hc
    rw [if_neg (not_not.2 hc)] at h
    split_ifs at h
  · intro h
    rw [if_pos h]

variable {X K Cr}

/- English proof (translation)
Take `⟨-, hpp, hI⟩` from `pc_mem_Ps.1 hp`. Rewrite using `[H.drop_iff p hpp]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `h`.

Use `⟨h, fun u hu => hT u ?_⟩` and prove the remaining obligations. Rewrite using `[← hu]`. Conclude with `hI`.
-/
theorem pc_drop_iff (H : PtH X K Cr) (hT : ∀ u, ¬ InertK D (D.mem u).A.T) {p : ℕ} (hp : p ∈ PsAt L) :
    p ∈ L.drop ↔ NoGain X K Cr p := by
  obtain ⟨-, hpp, hI⟩ := pc_mem_Ps.1 hp
  rw [H.drop_iff p hpp]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun u hu => hT u ?_⟩
    rw [← hu]; exact hI

variable (X K Cr)

/- English proof (translation)
Establish `h1` using `(pc_served_iff X K p).1 h`. Rewrite `h1` using `[pc_drop_iff H hT hp]`. Assume the negation of the conclusion as `hc`. Conclude with `h1 (Or.inr (Or.inl (not_le.1 hc)))`.
-/
theorem served_le (H : PtH X K Cr) (hT : ∀ u, ¬ InertK D (D.mem u).A.T) (p : ℕ) (hp : p ∈ PsAt L)
    (h : clAt X K p = PClass.served) : (p : ℝ) ≤ L.sc.X'' D.R.n := by
  have h1 := (pc_served_iff X K p).1 h
  rw [pc_drop_iff H hT hp] at h1
  by_contra hc
  exact h1 (Or.inr (Or.inl (not_le.1 hc)))

/- English proof (translation)
Unfold `clAt at h`. Use `split_ifs at h with h1 h2 h3`. Conclude with `h2`.
-/
theorem high_gt (p : ℕ) (h : clAt X K p = PClass.high) : L.sc.X'' D.R.n < (p : ℝ) := by
  classical
  unfold clAt at h
  split_ifs at h with h1 h2 h3
  exact h2

/- English proof (translation)
Unfold `clAt at h`. Use `split_ifs at h with h1 h2 h3`. Conclude with `h3`.
-/
theorem second_spec (p : ℕ) (h : clAt X K p = PClass.second) :
    G.Cand D L K p ∧ L.sc.x ^ (-L.sc.eps) < G.Sig X K (G.aL L) (G.bL L) p := by
  classical
  unfold clAt at h
  split_ifs at h with h1 h2 h3
  exact h3

/- English proof (translation)
Unfold `G.VV`. Rewrite using `[if_neg]`. Introduce and unpack `⟨hc, hs⟩`. Take `⟨hpp, hpX, hc0, hord, hband⟩` from `hc`. Break down `h with ⟨-, -, h | h | h⟩ | h | h | h` into its components or cases.

Conclude with `absurd hord (not_le.2 h)`. Take `⟨hp0, i, hi, hab⟩` from `h`. Use `hband hp0 ⟨hp0, hpX, i, hi, ?_, ?_⟩` and prove the remaining obligations. Use `(abs_le.1 hab).1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `(abs_le.1 hab).2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `absurd hs (not_le.2 h.2)`. Use `pc_X'_le L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h (Or.inl hc0)`. Conclude with `(Nat.not_odd_iff_even.2 (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hord)) h.2.1`.
-/
theorem pc_VV_empty (p : ℕ) (h : NoGain X K Cr p) :
    G.VV X K (G.aL L) (G.bL L) p = ∅ := by
  classical
  unfold G.VV
  rw [if_neg]
  rintro ⟨hc, hs⟩
  obtain ⟨hpp, hpX, hc0, hord, hband⟩ := hc
  rcases h with ⟨-, -, h | h | h⟩ | h | h | h
  · exact absurd hord (not_le.2 h)
  · obtain ⟨hp0, i, hi, hab⟩ := h
    refine hband hp0 ⟨hp0, hpX, i, hi, ?_, ?_⟩
    · have := (abs_le.1 hab).1
      nlinarith
    · have := (abs_le.1 hab).2
      nlinarith
  · exact absurd hs (not_le.2 h.2)
  · have := pc_X'_le L
    linarith
  · exact h (Or.inl hc0)
  · exact (Nat.not_odd_iff_even.2 (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hord)) h.2.1

/- English proof (translation)
Establish `hd : p ∈ L.drop`. Assume the negation of the conclusion as `hc`. Conclude with `h ((pc_served_iff X K p).2 hc)`. Use `⟨fun j => ?_, ?_⟩` and prove the remaining obligations. Unfold `gainQ`.

Rewrite using `[if_pos hd]`. Unfold `G.tauP`. Rewrite using `[if_pos (pc_VV_empty X K Cr p ((pc_drop_iff H hT hp).1 hd))]`.
-/
theorem nonserved_zero (H : PtH X K Cr) (hT : ∀ u, ¬ InertK D (D.mem u).A.T) (p : ℕ) (hp : p ∈ PsAt L)
    (h : clAt X K p ≠ PClass.served) :
    (∀ j, gainQ X K j p = 0) ∧ G.tauP X K (G.aL L) (G.bL L) p = 0 := by
  classical
  have hd : p ∈ L.drop := by
    by_contra hc
    exact h ((pc_served_iff X K p).2 hc)
  refine ⟨fun j => ?_, ?_⟩
  · unfold gainQ
    rw [if_pos hd]
  · unfold G.tauP
    rw [if_pos (pc_VV_empty X K Cr p ((pc_drop_iff H hT hp).1 hd))]

/- English proof (translation)
Establish `hρ` using `pc_rho_nonneg K hK L`. Establish `hX : 0 < L.sc.X'` using `(Lnk.sc_pos L.sc).2.2.2.1`. Establish `hlt : (p : ℝ) < L.sc.X' * (1 + Cr * G.rhoB D K L.sc)`. Establish `: 0 ≤ Cr * G.rhoB D K L.sc` using `mul_nonneg (by linarith) hρ`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : ¬ ((addOrderOf (G.hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4))` using `fun hh => h (Or.inl ⟨hlt, hc0, Or.inl hh⟩)`. Establish `h2 : ¬ (L.sc.p0 D.R.k ≤ (p : ℝ) ∧ ∃ i : ℕ, 1 ≤ i ∧ |(p : ℝ) ^ i - L.sc.X'| ≤ G.rhoB D K L.sc * L.sc.X')` using `fun hh => h (Or.inl ⟨hlt, hc0, Or.inr (Or.inl hh)⟩)`. Establish `hc : G.Cand D L K p`. Use `⟨hpp, hpX, hc0, not_lt.1 h1, fun hp0 hb => h2 ⟨hp0, ?_⟩⟩` and prove the remaining obligations. Take `⟨-, -, d, hd, hb1, hb2⟩` from `hb`.

Use `⟨d, hd, abs_le.2 ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Use `⟨hc, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hs`.

Conclude with `h (Or.inl ⟨hlt, hc0, Or.inr (Or.inr ⟨hc, not_le.1 hs⟩)⟩)`.
-/
theorem pc_cand (hK : K.Nonneg) (hCr : 1 ≤ Cr) (p : ℕ) (hpp : p.Prime) (hc0 : G.IsResidueClassZero D p) (hpX : (p : ℝ) < L.sc.X')
    (h : ¬ NoGain X K Cr p) :
    G.Cand D L K p ∧ G.Sig X K (G.aL L) (G.bL L) p ≤ L.sc.x ^ (-L.sc.eps) := by
  have hρ := pc_rho_nonneg K hK L
  have hX : 0 < L.sc.X' := (Lnk.sc_pos L.sc).2.2.2.1
  have hlt : (p : ℝ) < L.sc.X' * (1 + Cr * G.rhoB D K L.sc) := by
    have : 0 ≤ Cr * G.rhoB D K L.sc := mul_nonneg (by linarith) hρ
    nlinarith
  have h1 : ¬ ((addOrderOf (G.hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)) :=
    fun hh => h (Or.inl ⟨hlt, hc0, Or.inl hh⟩)
  have h2 : ¬ (L.sc.p0 D.R.k ≤ (p : ℝ) ∧ ∃ i : ℕ, 1 ≤ i ∧ |(p : ℝ) ^ i - L.sc.X'| ≤ G.rhoB D K L.sc * L.sc.X') :=
    fun hh => h (Or.inl ⟨hlt, hc0, Or.inr (Or.inl hh)⟩)
  have hc : G.Cand D L K p := by
    refine ⟨hpp, hpX, hc0, not_lt.1 h1, fun hp0 hb => h2 ⟨hp0, ?_⟩⟩
    obtain ⟨-, -, d, hd, hb1, hb2⟩ := hb
    refine ⟨d, hd, abs_le.2 ⟨?_, ?_⟩⟩
    · nlinarith
    · nlinarith
  refine ⟨hc, ?_⟩
  by_contra hs
  exact h (Or.inl ⟨hlt, hc0, Or.inr (Or.inr ⟨hc, not_le.1 hs⟩)⟩)

/- English proof (translation)
Take `⟨-, hpp, hI⟩` from `pc_mem_Ps.1 hp`. Establish `hnd : ¬ NoGain X K Cr p`. Rewrite using `[← pc_drop_iff H hT hp]`. Conclude with `(pc_served_iff X K p).1 h`. Take `⟨hn1, hn2⟩` from `Finset.mem_sdiff.1 hn`.

Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hn1`. Establish `ht2 : t ∉ G.TTP X K (G.aL L) (G.bL L) p` using `fun hh => hn2 (Finset.mem_image_of_mem _ hh)`. Establish `hcase : ¬ (G.IsSg D p ∨ L.sc.X' ≤ (p : ℝ))`. Introduce `hh`. Apply `ht2` to reduce the goal to its premises.

Unfold `G.TTP`. Rewrite using `[if_pos hh]`. Conclude with `ht`. Establish `hc0 : G.IsResidueClassZero D p`. Break down `hI with hs | hc` into its components or cases.

Conclude with `absurd (Or.inl hs) hcase`. Conclude with `hc`. Establish `hpX : (p : ℝ) < L.sc.X'` using `not_le.1 (fun hh => hcase (Or.inr hh))`. Take `⟨hc, hs⟩` from `pc_cand X K Cr H.Knn H.Cr1 p hpp hc0 hpX hnd`. Establish `hVV : G.VV X K (G.aL L) (G.bL L) p = G.goodReps X p`.

Unfold `G.VV`. Rewrite using `[if_pos ⟨hc, hs⟩]`. Establish `ht3 : X.bs (G.stepP D p) t ∉ G.goodReps X p`. Introduce `hh`. Apply `ht2` to reduce the goal to its premises.

Unfold `G.TTP`. Rewrite using `[if_neg hcase, Finset.mem_filter, hVV]`. Conclude with `⟨ht, hh⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `largeOrderResiduePrimes`.

Rewrite using `[Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨Nat.lt_ceil.2 hpX, hpp, hc0, hc.2.2.2.1⟩`. Unfold `badAt`. Rewrite using `[D.R.toFrame.ofNat_val]`. Introduce `hg`.

Apply `ht3` to reduce the goal to its premises. Unfold `G.goodReps G.reps`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩`.
-/
theorem unserved_bad (H : PtH X K Cr) (hT : ∀ u, ¬ InertK D (D.mem u).A.T) (p : ℕ) (hp : p ∈ PsAt L)
    (h : clAt X K p = PClass.served) (n : ℕ)
    (hn : n ∈ TTv D \ (ldAt X K C bo).TTp p) : p ∈ largeOrderResiduePrimes L ∧ badAt X p n := by
  classical
  obtain ⟨-, hpp, hI⟩ := pc_mem_Ps.1 hp
  have hnd : ¬ NoGain X K Cr p := by
    rw [← pc_drop_iff H hT hp]
    exact (pc_served_iff X K p).1 h
  obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.1 hn
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hn1
  have ht2 : t ∉ G.TTP X K (G.aL L) (G.bL L) p := fun hh => hn2 (Finset.mem_image_of_mem _ hh)
  have hcase : ¬ (G.IsSg D p ∨ L.sc.X' ≤ (p : ℝ)) := by
    intro hh
    apply ht2
    unfold G.TTP
    rw [if_pos hh]
    exact ht
  have hc0 : G.IsResidueClassZero D p := by
    rcases hI with hs | hc
    · exact absurd (Or.inl hs) hcase
    · exact hc
  have hpX : (p : ℝ) < L.sc.X' := not_le.1 (fun hh => hcase (Or.inr hh))
  obtain ⟨hc, hs⟩ := pc_cand X K Cr H.Knn H.Cr1 p hpp hc0 hpX hnd
  have hVV : G.VV X K (G.aL L) (G.bL L) p = G.goodReps X p := by
    unfold G.VV
    rw [if_pos ⟨hc, hs⟩]
  have ht3 : X.bs (G.stepP D p) t ∉ G.goodReps X p := by
    intro hh
    apply ht2
    unfold G.TTP
    rw [if_neg hcase, Finset.mem_filter, hVV]
    exact ⟨ht, hh⟩
  refine ⟨?_, ?_⟩
  · unfold largeOrderResiduePrimes
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.2 hpX, hpp, hc0, hc.2.2.2.1⟩
  · unfold badAt
    rw [D.R.toFrame.ofNat_val]
    intro hg
    apply ht3
    unfold G.goodReps G.reps
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩

/- English proof (translation)
Take `⟨-, hpp, hI⟩` from `pc_mem_Ps.1 hp`. Establish `hle` using `served_le X K Cr H hT p hp h`. Establish `hnd : p ∉ L.drop` using `(pc_served_iff X K p).1 h`. Take `⟨w, hw⟩` from `Lnk.place_over D p hpp`. Take `⟨-, -, hG2, -, -⟩` from `hG`.

Take `⟨-, hled⟩` from `hG2 w (by rw [hw]; exact hI) (by rw [hw]; exact hle)`. Rewrite `hled` using `[hw]`. Take `⟨-, -, fT, fg, ft, -, -⟩` from `H.fills w`. Simplify using `only [hw] at fT fg ft`. Establish `hws : w ∈ L.supp` using `H.supp_sat w (by rw [hw]; exact hle)`.

Establish `hI' : G.IsResidueClassZero D p ∨ G.IsSg D p` using `hI.symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `n hn`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hn`. Use `Finset.mem_image_of_mem _ ?_` and prove the remaining obligations.

Rewrite `ht` using `[← fT, Finset.mem_map]`. Take `⟨s, -, rfl⟩` from `ht`. Conclude with `s.2`. Establish `e1 : ∀ j ∈ SizeData₂.lifts D, ∑ t ∈ (ldAt X K C bo).TTp p, (askAt ((ldAt X K C bo).Iex j t p) ((ldAt X K C bo).at_ t) p ((ldAt X K C bo).wz j t p) - (ldAt X K C bo).lo p) = ∑ t ∈ L.TTw w, (L.vonMangoldtClassSum j t p - loG L C bo p)`. Introduce `j hj`.

Use `show ∑ t ∈ (G.TTP X K (G.aL L) (G.bL L) p).image Formalism.HC.Frame.A.val, _ = _`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => Formalism.HC.Frame.A.val_injective _ hab), ← fT, Finset.sum_map]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Use `hask j hj t p hpp hI` as an intermediate fact. Use `show askAt ((ldAt X K C bo).Iex j t.1.val p) ((ldAt X K C bo).at_ t.1.val) p ((ldAt X K C bo).wz j t.1.val p) - loG L C bo p = _`.

Rewrite using `[this]`. Establish `e2 : ∑ j ∈ SizeData₂.lifts D, (ldAt X K C bo).gain j p = ∑ j ∈ SizeData₂.lifts D, L.gain j w`. Use `Finset.sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Use `show gainQ X K j p = _`. Unfold `gainQ`.

Rewrite using `[if_neg hnd, fg hws hI' j hj]`. Establish `e3 : ((SizeData₂.lifts D).card : ℝ) = (D.R.m : ℝ)`. Unfold `SizeData₂.lifts`. Rewrite using `[Nat.card_Icc]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl e1, e2, e3]`. Use `show _ - (D.R.m : ℝ) * flG L C p ≤ _ - G.tauP X K (G.aL L) (G.bL L) p`. Rewrite using `[← ft]`. Conclude with `hled`.
-/
theorem loss_bound_at (H : PtH X K Cr) (hT : ∀ u, ¬ InertK D (D.mem u).A.T)
    (hask : ∀ j ∈ SizeData₂.lifts D, ∀ (t : D.host.TT) (p : ℕ), p.Prime → InertK D p →
      askAt ((ldAt X K C bo).Iex j t.1.val p) ((ldAt X K C bo).at_ t.1.val) p ((ldAt X K C bo).wz j t.1.val p) = L.vonMangoldtClassSum j t p)
    (hG : LinkG_at X K C bo) (p : ℕ) (hp : p ∈ PsAt L) (h : clAt X K p = PClass.served) :
    Formalism.LFunctionChainParameters.DeficitSplitLemmas.SizeData₂ (SizeData₂.lifts D) (TTv D) (ldAt X K C bo).TTp
      (fun j t p => askAt ((ldAt X K C bo).Iex j t p) ((ldAt X K C bo).at_ t) p ((ldAt X K C bo).wz j t p))
      (ldAt X K C bo).gain (ldAt X K C bo).tau (ldAt X K C bo).lo (ldAt X K C bo).fl p := by
  classical
  obtain ⟨-, hpp, hI⟩ := pc_mem_Ps.1 hp
  have hle := served_le X K Cr H hT p hp h
  have hnd : p ∉ L.drop := (pc_served_iff X K p).1 h
  obtain ⟨w, hw⟩ := Lnk.place_over D p hpp
  obtain ⟨-, -, hG2, -, -⟩ := hG
  obtain ⟨-, hled⟩ := hG2 w (by rw [hw]; exact hI) (by rw [hw]; exact hle)
  rw [hw] at hled
  obtain ⟨-, -, fT, fg, ft, -, -⟩ := H.fills w
  simp only [hw] at fT fg ft
  have hws : w ∈ L.supp := H.supp_sat w (by rw [hw]; exact hle)
  have hI' : G.IsResidueClassZero D p ∨ G.IsSg D p := hI.symm
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hn
    refine Finset.mem_image_of_mem _ ?_
    rw [← fT, Finset.mem_map] at ht
    obtain ⟨s, -, rfl⟩ := ht
    exact s.2
  · have e1 : ∀ j ∈ SizeData₂.lifts D,
        ∑ t ∈ (ldAt X K C bo).TTp p,
          (askAt ((ldAt X K C bo).Iex j t p) ((ldAt X K C bo).at_ t) p ((ldAt X K C bo).wz j t p) - (ldAt X K C bo).lo p) =
        ∑ t ∈ L.TTw w, (L.vonMangoldtClassSum j t p - loG L C bo p) := by
      intro j hj
      show ∑ t ∈ (G.TTP X K (G.aL L) (G.bL L) p).image Formalism.HC.Frame.A.val, _ = _
      rw [Finset.sum_image (fun a _ b _ hab => Formalism.HC.Frame.A.val_injective _ hab), ← fT, Finset.sum_map]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have := hask j hj t p hpp hI
      show askAt ((ldAt X K C bo).Iex j t.1.val p) ((ldAt X K C bo).at_ t.1.val) p ((ldAt X K C bo).wz j t.1.val p) -
        loG L C bo p = _
      rw [this]
    have e2 : ∑ j ∈ SizeData₂.lifts D, (ldAt X K C bo).gain j p = ∑ j ∈ SizeData₂.lifts D, L.gain j w := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      show gainQ X K j p = _
      unfold gainQ
      rw [if_neg hnd, fg hws hI' j hj]
    have e3 : ((SizeData₂.lifts D).card : ℝ) = (D.R.m : ℝ) := by
      unfold SizeData₂.lifts
      rw [Nat.card_Icc]
      simp
    rw [Finset.sum_congr rfl e1, e2, e3]
    show _ - (D.R.m : ℝ) * flG L C p ≤ _ - G.tauP X K (G.aL L) (G.bL L) p
    rw [← ft]
    exact hled

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem pc_ord_cast {N N' : ℕ} (h : N = N') (l : ℕ) (h1 : Nat.Coprime l N) (h2 : Nat.Coprime l N') :
    orderOf (QuotientGroup.mk (ZMod.unitOfCoprime l h1) : (ZMod N)ˣ ⧸ Subgroup.zpowers (-1 : (ZMod N)ˣ)) =
      orderOf (QuotientGroup.mk (ZMod.unitOfCoprime l h2) : (ZMod N')ˣ ⧸ Subgroup.zpowers (-1 : (ZMod N')ˣ)) := by
  subst h
  rfl

/- English proof (translation)
Take `⟨h2, hh⟩` from `J.two_readings_of_Frobenius D p hpp hc0`. Establish `hl2 : Nat.Coprime p 2` using `(Nat.coprime_primes hpp Nat.prime_two).2 h2`. Establish `hN : 2 ^ (D.R.e + 2) = 4 * 2 ^ D.R.e` using `by ring`. Establish `hl : Nat.Coprime p (4 * 2 ^ D.R.e)`. Rewrite using `[← hN]`.

Conclude with `Nat.Coprime.pow_right _ hl2`. Use `⟨hl, ?_⟩` and prove the remaining obligations. Rewrite using `[hh, addOrderOf_ofMul_eq_orderOf, UnusedSlot33.SlopeTestRemainingChoices.orderOf_iotaH]`. Use `UnusedSlot33.PrimeReciprocalSums.hOf_ord D.R.e p hl2` as an intermediate fact. Unfold `GlobalTheoryTheory.ordH at this`.

Rewrite using `[this]`. Conclude with `(pc_ord_cast hN p _ hl).symm`.
-/
theorem pc_ord (D : D7) (p : ℕ) (hpp : p.Prime) (hc0 : G.IsResidueClassZero D p) :
    ∃ hl : Nat.Coprime p (4 * 2 ^ D.R.e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf D.R.e p hl) = addOrderOf (D.R.h (G.hP D p)) := by
  obtain ⟨h2, hh⟩ := J.two_readings_of_Frobenius D p hpp hc0
  have hl2 : Nat.Coprime p 2 := (Nat.coprime_primes hpp Nat.prime_two).2 h2
  have hN : 2 ^ (D.R.e + 2) = 4 * 2 ^ D.R.e := by ring
  have hl : Nat.Coprime p (4 * 2 ^ D.R.e) := by
    rw [← hN]; exact Nat.Coprime.pow_right _ hl2
  refine ⟨hl, ?_⟩
  rw [hh, addOrderOf_ofMul_eq_orderOf, UnusedSlot33.SlopeTestRemainingChoices.orderOf_iotaH]
  have := UnusedSlot33.PrimeReciprocalSums.hOf_ord D.R.e p hl2
  unfold GlobalTheoryTheory.ordH at this
  rw [this]
  exact (pc_ord_cast hN p _ hl).symm

/- English proof (translation)
Substitute `he` using the available equality. Conclude with `pc_ord D p hpp hc0`.
-/
theorem pc_ord' (D : D7) (e : ℕ) (he : e = D.R.e) (p : ℕ) (hpp : p.Prime) (hc0 : G.IsResidueClassZero D p) :
    ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) = addOrderOf (D.R.h (G.hP D p)) := by
  subst he
  exact pc_ord D p hpp hc0

/- English proof (translation)
Introduce `p hp hcl`. Take `⟨-, hpp, hI⟩` from `pc_mem_Ps.1 hp`. Establish `hXp : P.Xp = L.sc.X'`. Unfold `Par.Xp Formalism.LFunctionChainParameters.LErr.XpTx Scale.X'`. Rewrite using `[tie.x, tie.ε]`.

Unfold `clAt at hcl`. Use `split_ifs at hcl with h1 h2 h3`. Establish `hd : p ∈ L.drop` using `h1`. Establish `hN` using `(pc_drop_iff H hT hp).1 hd`. Break down `hN with ⟨hlt, hc0, h | h | h⟩ | h | h | h` into its components or cases.

Use `left`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations. Rewrite using `[tie.Y]`. Conclude with `hlt.le`.

Take `⟨hl, ho⟩` from `pc_ord' D P.e₂ tie.e₂ p hpp hc0`. Rewrite using `[tie.x, tie.ε]`. Use `⟨hl, lt_of_le_of_lt ?_ h⟩` and prove the remaining obligations. Rewrite using `[ho]`. Conclude with `Nat.le_of_dvd (addOrderOf_pos _) (D.R.toFrame.addOrderOf_h_dvd (G.hP D p))` after adjusting the coercions.

Use `right`. Take `⟨hp0, i, hi, hab⟩` from `h`. Use `⟨?_, i, hi, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[tie.p₀]`. Conclude with `Nat.ceil_le.2 hp0`.

Rewrite using `[hXp, tie.ρ]`. Use `(abs_le.1 hab).1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hXp, tie.ρ]`. Use `(abs_le.1 hab).2` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `absurd h h3`. Conclude with `absurd h h2`. Conclude with `absurd hI.symm h`. Use `left`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `hXpp : P.Xpp = L.sc.X'' D.R.n`. Unfold `Par.Xpp Par.n Formalism.LFunctionChainParameters.LErr.XppTx Formalism.LFunctionChainParameters.LErr.wppTx Formalism.LFunctionChainParameters.LErr.bpTx Formalism.LFunctionChainParameters.LErr.aTx Formalism.LFunctionChainParameters.LErr.bTx Formalism.LFunctionChainParameters.LErr.X …`. Rewrite using `[tie.x, tie.ε, tie.nA]`.

Rewrite using `[hXpp]`. Conclude with `not_lt.1 h2`. Take `⟨hl, ho⟩` from `pc_ord' D P.e₂ tie.e₂ p hpp h.1`. Use `⟨hl, ?_⟩` and prove the remaining obligations. Establish `h0 : D.R.h (G.hP D p) = 0` using `(UpperTheory.even_addOrderOf_hP_of_pow_le.1 D.R (G.hP D p) h.2.1).1`.

Rewrite using `[ho, h0, addOrderOf_zero, tie.x, tie.ε, Nat.cast_one]`. Conclude with `Real.one_lt_rpow L.sc.one_lt_alt (by linarith [L.sc.eps_pos])`.
-/
theorem firstHyp_at (H : PtH X K Cr) (hT : ∀ u, ¬ InertK D (D.mem u).A.T) (P : Par) (tie : ParTie P L K C bo Cr) :
    FirstHyp P (PsAt L) (clAt X K) := by
  classical
  intro p hp hcl
  obtain ⟨-, hpp, hI⟩ := pc_mem_Ps.1 hp
  have hXp : P.Xp = L.sc.X' := by
    unfold Par.Xp Formalism.LFunctionChainParameters.LErr.XpTx Scale.X'
    rw [tie.x, tie.ε]
  unfold clAt at hcl
  split_ifs at hcl with h1 h2 h3
  have hd : p ∈ L.drop := h1
  have hN := (pc_drop_iff H hT hp).1 hd
  rcases hN with ⟨hlt, hc0, h | h | h⟩ | h | h | h
  · left
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (le_max_left _ _)
      rw [tie.Y]; exact hlt.le
    · obtain ⟨hl, ho⟩ := pc_ord' D P.e₂ tie.e₂ p hpp hc0
      rw [tie.x, tie.ε]
      refine ⟨hl, lt_of_le_of_lt ?_ h⟩
      rw [ho]
      exact_mod_cast Nat.le_of_dvd (addOrderOf_pos _) (D.R.toFrame.addOrderOf_h_dvd (G.hP D p))
  · right
    obtain ⟨hp0, i, hi, hab⟩ := h
    refine ⟨?_, i, hi, ?_, ?_⟩
    · rw [tie.p₀]; exact Nat.ceil_le.2 hp0
    · rw [hXp, tie.ρ]
      have := (abs_le.1 hab).1
      nlinarith
    · rw [hXp, tie.ρ]
      have := (abs_le.1 hab).2
      nlinarith
  · exact absurd h h3
  · exact absurd h h2
  · exact absurd hI.symm h
  · left
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (le_max_right _ _)
      have hXpp : P.Xpp = L.sc.X'' D.R.n := by
        unfold Par.Xpp Par.n Formalism.LFunctionChainParameters.LErr.XppTx Formalism.LFunctionChainParameters.LErr.wppTx Formalism.LFunctionChainParameters.LErr.bpTx Formalism.LFunctionChainParameters.LErr.aTx
          Formalism.LFunctionChainParameters.LErr.bTx Formalism.LFunctionChainParameters.LErr.XpTx Scale.X'' Scale.w'' Scale.b' Scale.a Scale.b Scale.L Scale.X'
        rw [tie.x, tie.ε, tie.nA]
      rw [hXpp]; exact not_lt.1 h2
    · obtain ⟨hl, ho⟩ := pc_ord' D P.e₂ tie.e₂ p hpp h.1
      refine ⟨hl, ?_⟩
      have h0 : D.R.h (G.hP D p) = 0 := (UpperTheory.even_addOrderOf_hP_of_pow_le.1 D.R (G.hP D p) h.2.1).1
      rw [ho, h0, addOrderOf_zero, tie.x, tie.ε, Nat.cast_one]
      exact Real.one_lt_rpow L.sc.one_lt_alt (by linarith [L.sc.eps_pos])

end AtRecordC

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.LErr

section AtRecord

variable {D : D7} {L : SizeData₂ D} {X : G.Inst D L} {K : G.Consts} {Cr C bo : ℝ} {P : Par}

/- English proof (translation)
Unfold `Par.b bTx Scale.b Scale.L`. Rewrite using `[tie.x, tie.ε]`.
-/
theorem pd_b (tie : ParTie P L K C bo Cr) : P.b = L.sc.b := by
  unfold Par.b bTx Scale.b Scale.L; rw [tie.x, tie.ε]

/- English proof (translation)
Unfold `Par.a aTx bTx Scale.a Scale.b Scale.L`. Rewrite using `[tie.x, tie.ε]`.
-/
theorem pd_a (tie : ParTie P L K C bo Cr) : P.a = L.sc.a := by
  unfold Par.a aTx bTx Scale.a Scale.b Scale.L; rw [tie.x, tie.ε]

/- English proof (translation)
Unfold `Par.Xp XpTx Scale.X'`. Rewrite using `[tie.x, tie.ε]`.
-/
theorem pd_Xp (tie : ParTie P L K C bo Cr) : P.Xp = L.sc.X' := by
  unfold Par.Xp XpTx Scale.X'; rw [tie.x, tie.ε]

/- English proof (translation)
Establish `h1` using `pd_a tie`. Establish `h2` using `pd_Xp tie`. Unfold `Par.a at h1`. Unfold `Par.Xp at h2`. Unfold `Par.bp bpTx Scale.b'`.

Rewrite using `[h1, h2]`.
-/
theorem pd_bp (tie : ParTie P L K C bo Cr) : P.bp = L.sc.b' := by
  have h1 := pd_a tie
  have h2 := pd_Xp tie
  unfold Par.a at h1
  unfold Par.Xp at h2
  unfold Par.bp bpTx Scale.b'; rw [h1, h2]

/- English proof (translation)
Conclude with `tie.nA`.
-/
theorem pd_n (tie : ParTie P L K C bo Cr) : P.n = (D.R.n : ℝ) := by
  exact tie.nA

/- English proof (translation)
Unfold `Par.f Ranks.f`. Rewrite using `[pd_n tie]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem pd_f (tie : ParTie P L K C bo Cr) : P.f = (D.R.f : ℝ) := by
  unfold Par.f Ranks.f; rw [pd_n tie]; push_cast; rfl

/- English proof (translation)
Establish `h1` using `pd_bp tie`. Unfold `Par.bp at h1`. Unfold `Par.wpp wppTx Scale.w''`. Rewrite using `[h1, tie.x, pd_n tie]`.
-/
theorem pd_wpp (tie : ParTie P L K C bo Cr) : P.wpp = L.sc.w'' D.R.n := by
  have h1 := pd_bp tie
  unfold Par.bp at h1
  unfold Par.wpp wppTx Scale.w''; rw [h1, tie.x, pd_n tie]

/- English proof (translation)
Establish `h1` using `pd_a tie`. Establish `h2` using `pd_wpp tie`. Unfold `Par.a at h1`. Unfold `Par.wpp at h2`. Unfold `Par.Xpp XppTx Scale.X''`.

Rewrite using `[h1, h2]`.
-/
theorem pd_Xpp (tie : ParTie P L K C bo Cr) : P.Xpp = L.sc.X'' D.R.n := by
  have h1 := pd_a tie
  have h2 := pd_wpp tie
  unfold Par.a at h1
  unfold Par.wpp at h2
  unfold Par.Xpp XppTx Scale.X''; rw [h1, h2]

/- English proof (translation)
Unfold `Par.lx`. Rewrite using `[tie.x]`.
-/
theorem pd_lx (tie : ParTie P L K C bo Cr) : P.lx = Real.log L.sc.x := by
  unfold Par.lx; rw [tie.x]

/- English proof (translation)
Unfold `Par.δ₁ Scale.delta1`. Rewrite using `[tie.x, tie.ε]`.
-/
theorem loss_delta_param_eq (tie : ParTie P L K C bo Cr) : P.δ₁ = L.sc.delta1 := by
  unfold Par.δ₁ Scale.delta1; rw [tie.x, tie.ε]

/- English proof (translation)
Unfold `Par.θ`. Rewrite using `[tie.x, tie.ε]`.
-/
theorem pd_th (tie : ParTie P L K C bo Cr) : P.θ = L.sc.x ^ (-L.sc.eps) := by
  unfold Par.θ; rw [tie.x, tie.ε]

/- English proof (translation)
Unfold `Par.Sk`. Rewrite using `[tie.Sc, tie.k, tie.η]`.
-/
theorem pd_Sk (tie : ParTie P L K C bo Cr) : P.Sk = L.Sc + D.R.k + L.etaSz := by
  unfold Par.Sk; rw [tie.Sc, tie.k, tie.η]

/- English proof (translation)
Unfold `Par.Q₁`. Rewrite using `[tie.C, tie.rG, pd_bp tie, pd_lx tie]`.
-/
theorem first_loss_param_eq (tie : ParTie P L K C bo Cr) :
    P.Q₁ = max C 0 * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x := by
  unfold Par.Q₁; rw [tie.C, tie.rG, pd_bp tie, pd_lx tie]

/- English proof (translation)
Unfold `Par.Q₂`. Rewrite using `[tie.C, pd_bp tie, tie.x, tie.η, tie.Sc, pd_wpp tie, tie.t, pd_lx tie, loss_delta_param_eq tie, tie.bo]`.
-/
theorem second_loss_param_eq (tie : ParTie P L K C bo Cr) :
    P.Q₂ = max C 0 * (L.sc.b' / L.sc.x + L.etaSz + L.Sc +
      (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.delta1) + bo := by
  unfold Par.Q₂; rw [tie.C, pd_bp tie, tie.x, tie.η, tie.Sc, pd_wpp tie, tie.t, pd_lx tie, loss_delta_param_eq tie, tie.bo]

/- English proof (translation)
Establish `h1` using `Lnk.one_le_b s`. Establish `h2` using `s.one_lt_alt`. Unfold `Scale.a`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pd_one_le_a (s : Scale) : 1 ≤ s.a := by
  have h1 := Lnk.one_le_b s
  have h2 := s.one_lt_alt
  unfold Scale.a
  nlinarith

/- English proof (translation)
Take `⟨hx, -, -, -, hb'⟩` from `Lnk.sc_pos L.sc`. Establish `hn` using `Lnk.one_le_n D.R`. Unfold `Scale.w''`. Conclude with `div_pos hb' (mul_pos hx (by linarith))`.
-/
theorem pd_wpp_pos (L : SizeData₂ D) : 0 < L.sc.w'' D.R.n := by
  obtain ⟨hx, -, -, -, hb'⟩ := Lnk.sc_pos L.sc
  have hn := Lnk.one_le_n D.R
  unfold Scale.w''
  exact div_pos hb' (mul_pos hx (by linarith))

/- English proof (translation)
Unfold `Scale.X'`. Conclude with `Real.one_le_exp (Real.rpow_nonneg (lt_trans one_pos s.one_lt_alt).le _)`.
-/
theorem pd_one_le_X' (s : Scale) : 1 ≤ s.X' := by
  unfold Scale.X'
  exact Real.one_le_exp (Real.rpow_nonneg (lt_trans one_pos s.one_lt_alt).le _)

/- English proof (translation)
Take `⟨hx, -, -, -, hb'⟩` from `Lnk.sc_pos L.sc`. Establish `hn` using `Lnk.one_le_n D.R`. Unfold `Scale.w''`. Apply `div_le_div_of_nonneg_left hb'.le hx` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pd_wpp_le_bx (L : SizeData₂ D) : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
  obtain ⟨hx, -, -, -, hb'⟩ := Lnk.sc_pos L.sc
  have hn := Lnk.one_le_n D.R
  unfold Scale.w''
  apply div_le_div_of_nonneg_left hb'.le hx
  nlinarith

/- English proof (translation)
Take `⟨hx, hb, ha, hX, hb'⟩` from `Lnk.sc_pos L.sc`. Use `le_trans (pd_wpp_le_bx L) ?_` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hx]`. Establish `h1 : L.sc.b' ≤ L.sc.a`. Unfold `Scale.b'`.

Conclude with `div_le_self ha.le (pd_one_le_X' L.sc)`. Establish `h2 : L.sc.a = L.sc.b * L.sc.x` using `by unfold Scale.a; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pd_wpp_le_b (L : SizeData₂ D) : L.sc.w'' D.R.n ≤ L.sc.b := by
  obtain ⟨hx, hb, ha, hX, hb'⟩ := Lnk.sc_pos L.sc
  refine le_trans (pd_wpp_le_bx L) ?_
  rw [div_le_iff₀ hx]
  have h1 : L.sc.b' ≤ L.sc.a := by
    unfold Scale.b'
    exact div_le_self ha.le (pd_one_le_X' L.sc)
  have h2 : L.sc.a = L.sc.b * L.sc.x := by unfold Scale.a; ring
  linarith

/- English proof (translation)
Unfold `PsAt at hp`. Conclude with `(Finset.mem_filter.mp hp).2.1`.
-/
theorem pd_prime {p : ℕ} (hp : p ∈ PsAt L) : p.Prime := by
  classical
  unfold PsAt at hp
  exact (Finset.mem_filter.mp hp).2.1

/- English proof (translation)
Establish `: D.R.ofNat t.val = t` using `D.R.toFrame.ofNat_val t`. Rewrite using `[this]`. Unfold `G.aL`. Rewrite using `[dif_pos ht]`.
-/
theorem pd_aL (t : G.HH D) (ht : t ∈ D.host.TT) : G.aL L (D.R.ofNat t.val) = L.aT ⟨t, ht⟩ := by
  have : D.R.ofNat t.val = t := D.R.toFrame.ofNat_val t
  rw [this]
  unfold G.aL
  rw [dif_pos ht]

/- English proof (translation)
Introduce `t ht`. Unfold `TTv at ht`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.mp ht`. Use `show 0 ≤ ((G.aL L (D.R.ofNat s.val) : ℤ) : ℝ) ∧ ((G.aL L (D.R.ofNat s.val) : ℤ) : ℝ) ≤ _`. Rewrite using `[pd_aL s hs, pd_a tie, tie.th]`.

Take `⟨h1, h2⟩` from `L.aT_win ⟨s, hs⟩`. Establish `ha` using `(Lnk.sc_a_pos L.sc).le`. Use `⟨le_trans ha h1, le_trans h2 (le_of_eq ?_)⟩` and prove the remaining obligations. Rewrite using `[mul_add, mul_one, mul_one_div]`.
-/
theorem pd_at (tie : ParTie P L K C bo Cr) :
    ∀ t ∈ TTv D, 0 ≤ (ldAt X K C bo).at_ t ∧ (ldAt X K C bo).at_ t ≤ P.a * (1 + P.th) := by
  intro t ht
  unfold TTv at ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  show 0 ≤ ((G.aL L (D.R.ofNat s.val) : ℤ) : ℝ) ∧ ((G.aL L (D.R.ofNat s.val) : ℤ) : ℝ) ≤ _
  rw [pd_aL s hs, pd_a tie, tie.th]
  obtain ⟨h1, h2⟩ := L.aT_win ⟨s, hs⟩
  have ha := (Lnk.sc_a_pos L.sc).le
  refine ⟨le_trans ha h1, le_trans h2 (le_of_eq ?_)⟩
  rw [mul_add, mul_one, mul_one_div]

/- English proof (translation)
Unfold `G.bL`. Use `split_ifs with h`. Conclude with `le_trans (Lnk.sc_b'_pos L.sc).le (L.bT_ge ⟨t, h⟩)`. Simplify using the standard rewrite rules.
-/
theorem pd_bL_nonneg (t : G.HH D) : (0 : ℝ) ≤ (G.bL L t : ℝ) := by
  unfold G.bL
  split_ifs with h
  · exact le_trans (Lnk.sc_b'_pos L.sc).le (L.bT_ge ⟨t, h⟩)
  · simp

/- English proof (translation)
Unfold `G.fill`. Distinguish the cases in `htop : G.IsTopPl D z`. Establish `h1` using `(X.off_top j z htop).1`. Establish `h2` using `pd_wpp_le_bx L`. Rewrite using `[if_pos (show z.1 = false ∧ z.2 ∈ D.host.TT from htop)]`.

Establish `h3` using `pd_bL_nonneg (L := L) z.2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg (show ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) from htop), zero_add]`. Distinguish the cases in `hth : G.IsThickPl D z`. Conclude with `le_trans (pd_wpp_le_b L) (X.off_thick j z hth).1`.

Conclude with `(X.off_thin j z ⟨htop, hth⟩).1`.
-/
theorem pd_fill (X : G.Inst D L) (j : ℕ) (z : Bool × G.HH D) : L.sc.w'' D.R.n ≤ G.fill X (G.bL L) j z := by
  unfold G.fill
  by_cases htop : G.IsTopPl D z
  · have h1 := (X.off_top j z htop).1
    have h2 := pd_wpp_le_bx L
    rw [if_pos (show z.1 = false ∧ z.2 ∈ D.host.TT from htop)]
    have h3 := pd_bL_nonneg (L := L) z.2
    linarith
  · rw [if_neg (show ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) from htop), zero_add]
    by_cases hth : G.IsThickPl D z
    · exact le_trans (pd_wpp_le_b L) (X.off_thick j z hth).1
    · exact (X.off_thin j z ⟨htop, hth⟩).1

/- English proof (translation)
Introduce `j _ t _ p _ i hi`. Use `⟨(Finset.mem_filter.mp hi).2, ?_⟩` and prove the remaining obligations. Rewrite using `[pd_wpp tie]`. Conclude with `pd_fill X j _`.
-/
theorem pd_wz (tie : ParTie P L K C bo Cr) :
    ∀ j ∈ SizeData₂.lifts D, ∀ t ∈ TTv D, ∀ p ∈ PsAt L, ∀ i ∈ (ldAt X K C bo).Iex j t p,
      Odd i ∧ P.wpp ≤ (ldAt X K C bo).wz j t p i := by
  intro j _ t _ p _ i hi
  refine ⟨(Finset.mem_filter.mp hi).2, ?_⟩
  rw [pd_wpp tie]
  exact pd_fill X j _

/- English proof (translation)
Introduce `j hj t _ i hi`. Use `⟨(Finset.mem_Icc.mp hi).1, ?_⟩` and prove the remaining obligations. Establish `hj'` using `Finset.mem_Icc.mp hj`. Use `show 0 ≤ LocalQuadraticParts.wAt D j _`. Distinguish the cases in `hρ : GlobalTheoryTheory.rho D (D.R.tau1 (D.R.ofNat t)) (ZetaZeroFreeRegion.gD D i) ∈ D.R.Psi`.

Use `Lnk.one_le_wAt L H.numN j hj'.1 hj'.2 _ hρ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `LocalQuadraticParts.wAt`. Rewrite using `[dif_neg hρ]`.
-/
theorem pd_wd (H : PtH X K Cr) :
    ∀ j ∈ SizeData₂.lifts D, ∀ t ∈ TTv D, ∀ i ∈ (ldAt X K C bo).Id j t, 1 ≤ i ∧ 0 ≤ (ldAt X K C bo).wd j t i := by
  intro j hj t _ i hi
  refine ⟨(Finset.mem_Icc.mp hi).1, ?_⟩
  have hj' := Finset.mem_Icc.mp hj
  show 0 ≤ LocalQuadraticParts.wAt D j _
  by_cases hρ : GlobalTheoryTheory.rho D (D.R.tau1 (D.R.ofNat t)) (ZetaZeroFreeRegion.gD D i) ∈ D.R.Psi
  · have := Lnk.one_le_wAt L H.numN j hj'.1 hj'.2 _ hρ
    linarith
  · unfold LocalQuadraticParts.wAt
    rw [dif_neg hρ]

/- English proof (translation)
Introduce `p hp`. Establish `hpp` using `pd_prime hp`. Establish `h1p : (1 : ℝ) < (p : ℝ)` using `by exact_mod_cast hpp.one_lt`. Establish `hlog : 0 ≤ Real.logb p L.sc.a` using `Real.logb_nonneg h1p (pd_one_le_a L.sc)`. Use `show flG L C p ≤ _`.

Unfold `flG flF`. Rewrite using `[tie.C, pd_f tie, tie.N, pd_a tie]`. Establish `hC : C ≤ max C 0` using `le_max_left _ _`. Establish `e1 : C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a ≤ max C 0 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a`. Use `mul_le_mul_of_nonneg_right hC (show 0 ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a by positivity)` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Establish `e2 : C * (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 ≤ max C 0 * (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2`. Use `mul_le_mul_of_nonneg_right hC (show 0 ≤ (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 by positivity)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pd_fl (tie : ParTie P L K C bo Cr) :
    ∀ p ∈ PsAt L, (ldAt X K C bo).fl p ≤ flF P.C P.f P.N P.a p := by
  intro p hp
  have hpp := pd_prime hp
  have h1p : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hlog : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg h1p (pd_one_le_a L.sc)
  show flG L C p ≤ _
  unfold flG flF
  rw [tie.C, pd_f tie, tie.N, pd_a tie]
  have hC : C ≤ max C 0 := le_max_left _ _
  have e1 : C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a ≤
      max C 0 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a := by
    have := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a by positivity)
    simpa [mul_assoc] using this
  have e2 : C * (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 ≤ max C 0 * (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 := by
    have := mul_le_mul_of_nonneg_right hC (show 0 ≤ (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 by positivity)
    simpa [mul_assoc] using this
  linarith

/- English proof (translation)
Introduce `p hp _`. Establish `hpp` using `pd_prime hp`. Establish `h1p : (1 : ℝ) < (p : ℝ)` using `by exact_mod_cast hpp.one_lt`. Establish `hx : 0 < L.sc.x` using `lt_trans one_pos L.sc.one_lt_alt`. Establish `hk : (0 : ℝ) < (D.R.k : ℝ)`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 0 < D.R.k)` after adjusting the coercions. Establish `hy : 0 < (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A)` using `mul_pos (pow_pos hk 2) (Real.rpow_pos_of_pos hx _)`. Use `show P.K₀ ≤ (p : ℝ) ^ ((leastPowerExponent L p : ℝ) - 1)`. Rewrite using `[tie.K₀]`.

Unfold `leastPowerExponent`. Use `push_cast`. Rewrite using `[add_sub_cancel_right]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem loss_constant_le_prime_pow (tie : ParTie P L K C bo Cr) :
    ∀ p ∈ PsAt L, p < P.p₀ → P.K₀ ≤ (p : ℝ) ^ ((ldAt X K C bo).L₁ p - 1) := by
  intro p hp _
  have hpp := pd_prime hp
  have h1p : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hk : (0 : ℝ) < (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hy : 0 < (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) := mul_pos (pow_pos hk 2) (Real.rpow_pos_of_pos hx _)
  show P.K₀ ≤ (p : ℝ) ^ ((leastPowerExponent L p : ℝ) - 1)
  rw [tie.K₀]
  unfold leastPowerExponent
  push_cast
  rw [add_sub_cancel_right]
  calc (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A)
      = (p : ℝ) ^ Real.logb p ((D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A)) :=
        (Real.rpow_logb (by linarith) h1p.ne' hy).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1p.le (Nat.le_ceil _)

/- English proof (translation)
Distinguish the cases in `hX : ltX`. Distinguish the cases in `hc : c0`. Distinguish the cases in `h0 : lt0`. Simplify using `only [hX, hc, h0, if_true, and_self]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [hX, hc, h0, if_true, if_false, and_self]`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h0 : lt0`. Simplify using `only [hX, hc, h0, if_true, if_false, false_and]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [hX, hc, h0, if_true, if_false, false_and]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : ¬ lt0` using `fun h => hX (hlt h)`. Simplify using `only [hX, h0, if_false, and_false, ite_self, add_zero, le_refl]`.
-/
theorem pd_key (c0 lt0 ltX : Prop) [Decidable c0] [Decidable lt0] [Decidable ltX] (hlt : lt0 → ltX)
    (CA1 MA1 CupProductTensor MA2 bo CB MB : ℝ) (h1 : CA1 ≤ MA1) (h2 : CupProductTensor ≤ MA2) (h3 : CB ≤ MB) (n1 : 0 ≤ MA1) (n2 : 0 ≤ MA2)
    (n3 : 0 ≤ MB) (nb : 0 ≤ bo) :
    (if c0 then (if lt0 then CA1 else if ltX then CupProductTensor + bo else 0) else 0) + (if c0 ∧ ltX then CB else 0) ≤
      (if ltX then (if lt0 then MA1 else MA2 + bo) + MB else 0) := by
  by_cases hX : ltX
  · by_cases hc : c0
    · by_cases h0 : lt0
      · simp only [hX, hc, h0, if_true, and_self]; linarith
      · simp only [hX, hc, h0, if_true, if_false, and_self]; linarith
    · by_cases h0 : lt0
      · simp only [hX, hc, h0, if_true, if_false, false_and]; linarith
      · simp only [hX, hc, h0, if_true, if_false, false_and]; linarith
  · have h0 : ¬ lt0 := fun h => hX (hlt h)
    simp only [hX, h0, if_false, and_false, ite_self, add_zero, le_refl]

/- English proof (translation)
Introduce `p hp`. Establish `hpp` using `pd_prime hp`. Establish `h1p : (1 : ℝ) < (p : ℝ)` using `by exact_mod_cast hpp.one_lt`. Establish `hp0' : (0 : ℝ) < (p : ℝ)` using `by linarith`. Take `⟨hx, hb, ha, hX, hb'⟩` from `Lnk.sc_pos L.sc`.

Establish `hlx : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg L.sc.one_lt_alt.le`. Establish `hd1 : 0 < L.sc.delta1` using `by unfold Scale.delta1; exact Real.rpow_pos_of_pos hx _`. Establish `hw` using `pd_wpp_pos L`. Establish `hSc` using `L.Sc_pos`. Establish `hη` using `L.etaSz_pos`.

Establish `hC : C ≤ max C 0` using `le_max_left _ _`. Establish `hC0 : 0 ≤ max C 0` using `le_max_right _ _`. Establish `hk : (0 : ℝ) ≤ (D.R.k : ℝ)` using `Nat.cast_nonneg _`. Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `hrG : (0 : ℝ) ≤ (Formalism.MainNotions.rG L.sc.eps : ℝ)` using `Nat.cast_nonneg _`.

Establish `hlog2 : 0 ≤ Real.logb p (2 * L.sc.a)` using `Real.logb_nonneg h1p (by have := pd_one_le_a L.sc; linarith)`. Establish `hlt : ∀ q : ℕ, q < P.p₀ ↔ (q : ℝ) < L.sc.p0 D.R.k`. Introduce `q`. Rewrite using `[tie.p₀]`. Conclude with `Nat.lt_ceil`.

Use `set A1 : ℝ := (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x with hA1`. Use `set A2 : ℝ := L.sc.b' / L.sc.x + L.etaSz + L.Sc + (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.delta1 with hA2`. Establish `hA1n : 0 ≤ A1` using `by rw [hA1]; positivity`. Establish `hA2n : 0 ≤ A2` using `by rw [hA2]; positivity`. Establish `hQ1 : P.Q₁ = max C 0 * A1` using `by rw [first_loss_param_eq tie, hA1]; ring`.

Establish `hQ2 : P.Q₂ = max C 0 * A2 + bo` using `by rw [second_loss_param_eq tie]`. Use `set B : ℝ := L.LaG * L.sc.a / ((p : ℝ) * D.R.k) + (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(leastPowerExponent L p : ℝ)) else L.sc.a / (p : ℝ) ^ 2) with hB`. Establish `hBn : 0 ≤ B`. Rewrite using `[hB]`. Apply `add_nonneg (by positivity)` to reduce the goal to its premises.

Use `split_ifs`. Conclude with `mul_nonneg ha.le (Real.rpow_nonneg hp0'.le _)`. Check the signs of the components of the expression. Establish `hor : orF P.C P.lx P.La P.a P.k (ldAt X K C bo).L₁ P.p₀ p = max C 0 * Real.log L.sc.x * B`. Unfold `orF`.

Rewrite using `[tie.C, pd_lx tie, tie.La, pd_a tie, tie.k, hB]`. Use `congr 2`. Distinguish the cases in `h : (p : ℝ) < L.sc.p0 D.R.k`. Rewrite using `[if_pos h, if_pos ((hlt p).2 h)]`. Both sides reduce to the same expression.

Rewrite using `[if_neg h, if_neg (fun h' => h ((hlt p).1 h'))]`. Establish `hpr : prF P.p₀ P.Q₁ P.Q₂ p = if (p : ℝ) < L.sc.p0 D.R.k then max C 0 * A1 else max C 0 * A2 + bo`. Unfold `prF`. Distinguish the cases in `h : (p : ℝ) < L.sc.p0 D.R.k`. Rewrite using `[if_pos h, if_pos ((hlt p).2 h), hQ1]`.

Rewrite using `[if_neg h, if_neg (fun h' => h ((hlt p).1 h')), hQ2]`. Establish `hcp : C * (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ cpF P.C P.Sk P.a p`. Unfold `cpF`. Rewrite using `[tie.C, pd_Sk tie, pd_a tie]`. Use `mul_le_mul_of_nonneg_right hC (show 0 ≤ (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * L.sc.a) by positivity)` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Establish `hCA1 : C * A1 ≤ max C 0 * A1` using `mul_le_mul_of_nonneg_right hC hA1n`. Establish `hCA2 : C * A2 ≤ max C 0 * A2` using `mul_le_mul_of_nonneg_right hC hA2n`. Establish `hCB : C * Real.log L.sc.x * B ≤ max C 0 * Real.log L.sc.x * B`. Use `mul_le_mul_of_nonneg_right hC (mul_nonneg hlx hBn)` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Establish `hMB : 0 ≤ max C 0 * Real.log L.sc.x * B` using `by positivity`. Establish `hMA1 : 0 ≤ max C 0 * A1` using `by positivity`. Establish `hMA2 : 0 ≤ max C 0 * A2` using `by positivity`. Use `show loG L C bo p ≤ _`.

Unfold `loG loF`. Rewrite using `[pd_Xp tie, hor, hpr]`. Simplify using `only []`. Establish `key : (if D.host.cls p = PrimeClass.inertClass then (if (p : ℝ) < L.sc.p0 D.R.k then C * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x else if (p : ℝ) < L.sc.X' then C * (L.sc.b' / L.sc.x + L.etaSz + L.Sc + (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.d …`. Establish `e1 : C * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x ≤ max C 0 * A1`.

Establish `: C * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x = C * A1` using `by rw [hA1]; ring`. Rewrite using `[this]`. Conclude with `hCA1`. Conclude with `pd_key _ _ _ (fun h => lt_of_lt_of_le h hp0) _ _ _ _ _ _ _ e1 hCA2 hCB hMA1 hMA2 hMB hbo`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pd_lo (tie : ParTie P L K C bo Cr) (hbo : 0 ≤ bo) (hLa : 0 ≤ L.LaG) (hp0 : L.sc.p0 D.R.k ≤ L.sc.X') :
    ∀ p ∈ PsAt L, (ldAt X K C bo).lo p ≤
      loF P.C P.Sk P.a P.Xp P.Q₁ P.Q₂ P.lx P.La P.k (ldAt X K C bo).L₁ P.p₀ p := by
  intro p hp
  have hpp := pd_prime hp
  have h1p : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hp0' : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨hx, hb, ha, hX, hb'⟩ := Lnk.sc_pos L.sc
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have hd1 : 0 < L.sc.delta1 := by unfold Scale.delta1; exact Real.rpow_pos_of_pos hx _
  have hw := pd_wpp_pos L
  have hSc := L.Sc_pos
  have hη := L.etaSz_pos
  have hC : C ≤ max C 0 := le_max_left _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hrG : (0 : ℝ) ≤ (Formalism.MainNotions.rG L.sc.eps : ℝ) := Nat.cast_nonneg _
  have hlog2 : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg h1p (by have := pd_one_le_a L.sc; linarith)
  have hlt : ∀ q : ℕ, q < P.p₀ ↔ (q : ℝ) < L.sc.p0 D.R.k := by
    intro q; rw [tie.p₀]; exact Nat.lt_ceil

  set A1 : ℝ := (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x with hA1
  set A2 : ℝ := L.sc.b' / L.sc.x + L.etaSz + L.Sc + (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.delta1 with hA2
  have hA1n : 0 ≤ A1 := by rw [hA1]; positivity
  have hA2n : 0 ≤ A2 := by rw [hA2]; positivity
  have hQ1 : P.Q₁ = max C 0 * A1 := by rw [first_loss_param_eq tie, hA1]; ring
  have hQ2 : P.Q₂ = max C 0 * A2 + bo := by rw [second_loss_param_eq tie]

  set B : ℝ := L.LaG * L.sc.a / ((p : ℝ) * D.R.k) +
    (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(leastPowerExponent L p : ℝ)) else L.sc.a / (p : ℝ) ^ 2) with hB
  have hBn : 0 ≤ B := by
    rw [hB]
    apply add_nonneg (by positivity)
    split_ifs
    · exact mul_nonneg ha.le (Real.rpow_nonneg hp0'.le _)
    · positivity
  have hor : orF P.C P.lx P.La P.a P.k (ldAt X K C bo).L₁ P.p₀ p = max C 0 * Real.log L.sc.x * B := by
    unfold orF
    rw [tie.C, pd_lx tie, tie.La, pd_a tie, tie.k, hB]
    congr 2
    by_cases h : (p : ℝ) < L.sc.p0 D.R.k
    · rw [if_pos h, if_pos ((hlt p).2 h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h ((hlt p).1 h'))]
  have hpr : prF P.p₀ P.Q₁ P.Q₂ p = if (p : ℝ) < L.sc.p0 D.R.k then max C 0 * A1 else max C 0 * A2 + bo := by
    unfold prF
    by_cases h : (p : ℝ) < L.sc.p0 D.R.k
    · rw [if_pos h, if_pos ((hlt p).2 h), hQ1]
    · rw [if_neg h, if_neg (fun h' => h ((hlt p).1 h')), hQ2]
  have hcp : C * (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ cpF P.C P.Sk P.a p := by
    unfold cpF
    rw [tie.C, pd_Sk tie, pd_a tie]
    have := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * L.sc.a) by positivity)
    simpa [mul_assoc] using this
  have hCA1 : C * A1 ≤ max C 0 * A1 := mul_le_mul_of_nonneg_right hC hA1n
  have hCA2 : C * A2 ≤ max C 0 * A2 := mul_le_mul_of_nonneg_right hC hA2n
  have hCB : C * Real.log L.sc.x * B ≤ max C 0 * Real.log L.sc.x * B := by
    have := mul_le_mul_of_nonneg_right hC (mul_nonneg hlx hBn)
    simpa [mul_assoc] using this
  have hMB : 0 ≤ max C 0 * Real.log L.sc.x * B := by positivity
  have hMA1 : 0 ≤ max C 0 * A1 := by positivity
  have hMA2 : 0 ≤ max C 0 * A2 := by positivity
  show loG L C bo p ≤ _
  unfold loG loF
  rw [pd_Xp tie, hor, hpr]
  simp only []
  have key : (if D.host.cls p = PrimeClass.inertClass then
      (if (p : ℝ) < L.sc.p0 D.R.k then C * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x
       else if (p : ℝ) < L.sc.X' then
         C * (L.sc.b' / L.sc.x + L.etaSz + L.Sc + (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.delta1) + bo
       else 0) else 0) +
      (if D.host.cls p = PrimeClass.inertClass ∧ (p : ℝ) < L.sc.X' then
        C * Real.log L.sc.x * (L.LaG * L.sc.a / ((p : ℝ) * D.R.k) +
          (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(leastPowerExponent L p : ℝ)) else L.sc.a / (p : ℝ) ^ 2))
        else 0) ≤
      (if (p : ℝ) < L.sc.X' then
        (if (p : ℝ) < L.sc.p0 D.R.k then max C 0 * A1 else max C 0 * A2 + bo) + max C 0 * Real.log L.sc.x * B
        else 0) := by
    have e1 : C * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x ≤ max C 0 * A1 := by
      have : C * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x = C * A1 := by rw [hA1]; ring
      rw [this]; exact hCA1
    exact pd_key _ _ _ (fun h => lt_of_lt_of_le h hp0) _ _ _ _ _ _ _ e1 hCA2 hCB hMA1 hMA2 hMB hbo
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨pd_at tie, pd_wz tie, pd_wd H, pd_fl tie, pd_lo tie hbo hLa hp0, loss_constant_le_prime_pow tie, pd_Xpp tie, pd_a tie, pd_Xp tie, pd_th tie⟩`.
-/
theorem side_at (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ) (H : PtH X K Cr) (P : Par) (tie : ParTie P L K C bo Cr)
    (hbo : 0 ≤ bo) (hLa : 0 ≤ L.LaG) (hp0 : L.sc.p0 D.R.k ≤ L.sc.X') :
    (∀ t ∈ TTv D, 0 ≤ (ldAt X K C bo).at_ t ∧ (ldAt X K C bo).at_ t ≤ P.a * (1 + P.th)) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ t ∈ TTv D, ∀ p ∈ PsAt L, ∀ i ∈ (ldAt X K C bo).Iex j t p,
      Odd i ∧ P.wpp ≤ (ldAt X K C bo).wz j t p i) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ t ∈ TTv D, ∀ i ∈ (ldAt X K C bo).Id j t, 1 ≤ i ∧ 0 ≤ (ldAt X K C bo).wd j t i) ∧
    (∀ p ∈ PsAt L, (ldAt X K C bo).fl p ≤ flF P.C P.f P.N P.a p) ∧
    (∀ p ∈ PsAt L, (ldAt X K C bo).lo p ≤ loF P.C P.Sk P.a P.Xp P.Q₁ P.Q₂ P.lx P.La P.k (ldAt X K C bo).L₁ P.p₀ p) ∧
    (∀ p ∈ PsAt L, p < P.p₀ → P.K₀ ≤ (p : ℝ) ^ ((ldAt X K C bo).L₁ p - 1)) ∧
    P.Xpp = L.sc.X'' D.R.n ∧ P.a = L.sc.a ∧ P.Xp = L.sc.X' ∧ P.θ = L.sc.x ^ (-L.sc.eps) :=
  ⟨pd_at tie, pd_wz tie, pd_wd H, pd_fl tie, pd_lo tie hbo hLa hp0, loss_constant_le_prime_pow tie, pd_Xpp tie, pd_a tie, pd_Xp tie, pd_th tie⟩

end AtRecord

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

section AtRecord

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
The claim follows from `lt_trans one_pos s.one_lt_alt`.
-/
theorem scale_pos_alt (s : Scale) : 0 < s.x := lt_trans one_pos s.one_lt_alt

/- English proof (translation)
The claim follows from `(Real.rpow_natCast _ _).symm`.
-/
theorem pe_np (s : Scale) (n : ℕ) : s.x ^ n = s.x ^ (n : ℝ) := (Real.rpow_natCast _ _).symm

/- English proof (translation)
Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (scale_pos_alt s).le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pe_sq (s : Scale) (a : ℝ) : (s.x ^ a) ^ 2 = s.x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (scale_pos_alt s).le]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Real.rpow_neg (scale_pos_alt s).le, Real.rpow_two]`.
-/
theorem rpow_neg_two_eq_inv_sq_alt (s : Scale) : s.x ^ (-2 : ℝ) = (s.x ^ 2)⁻¹ := by
  rw [Real.rpow_neg (scale_pos_alt s).le, Real.rpow_two]

/- English proof (translation)
The claim follows from `Real.one_le_rpow s.one_lt_alt.le ha`.
-/
theorem pe_one_le (s : Scale) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ s.x ^ a := Real.one_le_rpow s.one_lt_alt.le ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `R.two_pow_le_n` after adjusting the coercions. Establish `h : R.n ≤ R.o * 2 ^ R.e` using `R.toFrame.ord_le_o_mul_two_pow`. Conclude with `h` after adjusting the coercions.
-/
theorem pe_n (R : Ranks) : (2 : ℝ) ^ R.e ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ (R.o : ℝ) * (2 : ℝ) ^ R.e := by
  constructor
  · exact_mod_cast R.two_pow_le_n
  · have h : R.n ≤ R.o * 2 ^ R.e := R.toFrame.ord_le_o_mul_two_pow
    exact_mod_cast h

/- English proof (translation)
Rewrite using `[Real.rpow_add (scale_pos_alt s), Real.rpow_one, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (scale_pos_alt s).le _)`.
-/
theorem pe_absorb (s : Scale) {c : ℝ} (hc : c ≤ s.x) (a : ℝ) : c * s.x ^ a ≤ s.x ^ (a + 1) := by
  rw [Real.rpow_add (scale_pos_alt s), Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (scale_pos_alt s).le _)

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `hp : 0 < L.sc.x ^ (L.sc.eps / 100)` using `Real.rpow_pos_of_pos hx _`. Establish `h1 : L.sc.x ^ (L.sc.eps / 100) * L.sc.x ^ 2 ≤ (D.R.n : ℝ)`. Rewrite using `[pe_np, ← Real.rpow_add hx]`. Use `le_trans (Lnk.rpow_mono' _ ?_) sN.1` and prove the remaining obligations.

Unfold `szTh`. Use `push_cast`. Combine the linear relations using `[L.sc.eps_pos]`. Establish `h2 : (D.R.o : ℝ) * (2 : ℝ) ^ D.R.e ≤ L.sc.x ^ (L.sc.eps / 100) * (2 : ℝ) ^ D.R.e` using `mul_le_mul_of_nonneg_right L.o_tie (by positivity)`. Conclude with `le_of_mul_le_mul_left (h1.trans ((pe_n D.R).2.trans h2)) hp`.
-/
theorem pe_n_ge (sN : SizeN L) : L.sc.x ^ 2 ≤ (2 : ℝ) ^ D.R.e := by
  have hx := scale_pos_alt L.sc
  have hp : 0 < L.sc.x ^ (L.sc.eps / 100) := Real.rpow_pos_of_pos hx _
  have h1 : L.sc.x ^ (L.sc.eps / 100) * L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    rw [pe_np, ← Real.rpow_add hx]
    refine le_trans (Lnk.rpow_mono' _ ?_) sN.1
    unfold szTh
    push_cast
    linarith [L.sc.eps_pos]
  have h2 : (D.R.o : ℝ) * (2 : ℝ) ^ D.R.e ≤ L.sc.x ^ (L.sc.eps / 100) * (2 : ℝ) ^ D.R.e :=
    mul_le_mul_of_nonneg_right L.o_tie (by positivity)
  exact le_of_mul_le_mul_left (h1.trans ((pe_n D.R).2.trans h2)) hp

/- English proof (translation)
Conclude with `(Lnk.n_le_x_cubed sN).trans (Lnk.rpow_mono' _ (by linarith))`.
-/
theorem pe_n_le (sN : SizeN L) {e : ℝ} (he : 40 ≤ e) : (D.R.n : ℝ) ≤ L.sc.x ^ e := by
  exact (Lnk.n_le_x_cubed sN).trans (Lnk.rpow_mono' _ (by linarith))

/- English proof (translation)
Rewrite using `[pe_np]`. Conclude with `le_trans (Lnk.rpow_mono' _ (by push_cast; norm_num)) (Lnk.x_pow_four_le_k sK)`.
-/
theorem pe_k_ge (sK : SizeK L) : L.sc.x ^ 2 ≤ (D.R.k : ℝ) := by
  rw [pe_np]
  exact le_trans (Lnk.rpow_mono' _ (by push_cast; norm_num)) (Lnk.x_pow_four_le_k sK)

/- English proof (translation)
The claim follows from `(Lnk.winC sK).trans (Lnk.rpow_mono' _ (by linarith))`.
-/
theorem pe_k_le (sK : SizeK L) {e : ℝ} (he : 40 ≤ e) : (D.R.k : ℝ) ≤ L.sc.x ^ e :=
  (Lnk.winC sK).trans (Lnk.rpow_mono' _ (by linarith))

/- English proof (translation)
The claim follows from `L.t_win.2.trans (Lnk.rpow_mono' _ (by linarith))`.
-/
theorem pe_t_le {e : ℝ} (he : L.Ct + 3 ≤ e) : (D.R.t : ℝ) ≤ L.sc.x ^ e :=
  L.t_win.2.trans (Lnk.rpow_mono' _ (by linarith))

/- English proof (translation)
Establish `h` using `(Lnk.winA sM).trans (Lnk.rpow_mono' L.sc (b := 1) (by linarith [L.sc.eps_lt]))`. Rewrite `h` using `[Real.rpow_one]`. Then use the resulting hypothesis.
-/
theorem pe_m_le (sM : SizeM L) : (D.R.m : ℝ) ≤ L.sc.x := by
  have h := (Lnk.winA sM).trans (Lnk.rpow_mono' L.sc (b := 1) (by linarith [L.sc.eps_lt]))
  rwa [Real.rpow_one] at h

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `hN : ((D.R.N D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)`. Unfold `Ranks.N`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `ht1 : (1 : ℝ) ≤ (D.R.t : ℝ)` using `by exact_mod_cast D.R.t_odd.pos`. Establish `hp : 0 ≤ L.sc.x ^ (e - 1)` using `Real.rpow_nonneg hx.le _`. Establish `a1 : (D.R.k : ℝ) ≤ L.sc.x ^ (e - 1)` using `(Lnk.winC sK).trans (Lnk.rpow_mono' _ (by linarith))`. Establish `a2 : (D.R.t : ℝ) ≤ L.sc.x ^ (e - 2)` using `L.t_win.2.trans (Lnk.rpow_mono' _ (by linarith))`. Establish `a3 : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 2 * L.sc.x ^ (e - 1)`.

Combine the equalities or inequalities in the displayed calculation. Use `pe_absorb L.sc (le_refl L.sc.x) (e - 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 2 * L.sc.x ^ (e - 1) := by`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `a4` using `pe_absorb L.sc h3 (e - 1)`. Rewrite `a4` using `[show e - 1 + 1 = e by ring]`. Rewrite using `[hN]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pe_N_le (sM : SizeM L) (sK : SizeK L) (h3 : 3 ≤ L.sc.x) {e : ℝ} (he : 40 ≤ e) (hc : L.Ct + 3 ≤ e) :
    ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.x ^ e := by
  have hx := scale_pos_alt L.sc
  have hN : ((D.R.N D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N
    push_cast
    ring
  have ht1 : (1 : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast D.R.t_odd.pos
  have hp : 0 ≤ L.sc.x ^ (e - 1) := Real.rpow_nonneg hx.le _
  have a1 : (D.R.k : ℝ) ≤ L.sc.x ^ (e - 1) := (Lnk.winC sK).trans (Lnk.rpow_mono' _ (by linarith))
  have a2 : (D.R.t : ℝ) ≤ L.sc.x ^ (e - 2) := L.t_win.2.trans (Lnk.rpow_mono' _ (by linarith))
  have a3 : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 2 * L.sc.x ^ (e - 1) := by
    calc (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ L.sc.x * (2 * L.sc.x ^ (e - 2)) :=
          mul_le_mul (pe_m_le sM) (by linarith) (by linarith) hx.le
      _ = 2 * (L.sc.x * L.sc.x ^ (e - 2)) := by ring
      _ ≤ 2 * L.sc.x ^ (e - 2 + 1) := by
          have := pe_absorb L.sc (le_refl L.sc.x) (e - 2)
          linarith
      _ = 2 * L.sc.x ^ (e - 1) := by
          congr 2; ring
  have a4 := pe_absorb L.sc h3 (e - 1)
  rw [show e - 1 + 1 = e by ring] at a4
  rw [hN]
  linarith

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Unfold `Scale.p0 Scale.A`. Establish `h1 : (D.R.k : ℝ) ^ 2 ≤ L.sc.x ^ (10 : ℝ)`. Use `pow_le_pow_left₀ (Nat.cast_nonneg D.R.k) (Lnk.winC sK) 2` as an intermediate fact. Rewrite `this` using `[pe_sq, show (2 : ℝ) * 5 = 10 by norm_num]`.

Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_add hx]`. Evaluate the numerical expressions.
-/
theorem threshold_prime_le_pow (sK : SizeK L) : L.sc.p0 D.R.k ≤ L.sc.x ^ (36 : ℝ) := by
  have hx := scale_pos_alt L.sc
  unfold Scale.p0 Scale.A
  have h1 : (D.R.k : ℝ) ^ 2 ≤ L.sc.x ^ (10 : ℝ) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg D.R.k) (Lnk.winC sK) 2
    rw [pe_sq, show (2 : ℝ) * 5 = 10 by norm_num] at this
    exact this
  calc (D.R.k : ℝ) ^ 2 * L.sc.x ^ (26 : ℝ) ≤ L.sc.x ^ (10 : ℝ) * L.sc.x ^ (26 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx.le _)
    _ = L.sc.x ^ (36 : ℝ) := by
        rw [← Real.rpow_add hx]; norm_num

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Unfold `Scale.p0`. Check the signs of the components of the expression.
-/
theorem threshold_prime_nonneg : 0 ≤ L.sc.p0 D.R.k := by
  have hx := scale_pos_alt L.sc
  unfold Scale.p0
  positivity

/- English proof (translation)
Establish `h1` using `(Nat.ceil_lt_add_one (threshold_prime_nonneg (L := L))).le`. Establish `h2` using `threshold_prime_le_pow sK`. Establish `h4 : (1 : ℝ) ≤ L.sc.x ^ (36 : ℝ)` using `pe_one_le _ (by norm_num)`. Establish `h5` using `pe_absorb L.sc (c := 2) (by linarith) 36`. Establish `h6 : L.sc.x ^ ((36 : ℝ) + 1) ≤ L.sc.x ^ e` using `Lnk.rpow_mono' _ (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ceil_threshold_prime_le_pow (sK : SizeK L) (h3 : 3 ≤ L.sc.x) {e : ℝ} (he : 40 ≤ e) :
    ((⌈L.sc.p0 D.R.k⌉₊ : ℕ) : ℝ) ≤ L.sc.x ^ e := by
  have h1 := (Nat.ceil_lt_add_one (threshold_prime_nonneg (L := L))).le
  have h2 := threshold_prime_le_pow sK
  have h4 : (1 : ℝ) ≤ L.sc.x ^ (36 : ℝ) := pe_one_le _ (by norm_num)
  have h5 := pe_absorb L.sc (c := 2) (by linarith) 36
  have h6 : L.sc.x ^ ((36 : ℝ) + 1) ≤ L.sc.x ^ e := Lnk.rpow_mono' _ (by linarith)
  linarith

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Use `le_trans ?_ (Nat.le_ceil _)` and prove the remaining obligations. Establish `hk` using `Lnk.x_pow_four_le_k sK`. Rewrite `hk` using `[show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `h4 : (1 : ℝ) ≤ L.sc.x ^ 4` using `one_le_pow₀ L.sc.one_lt_alt.le`.

Establish `hA : (2 : ℝ) ≤ L.sc.x ^ Scale.A`. Establish `: L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ Scale.A` using `Lnk.rpow_mono' _ (by unfold Scale.A; norm_num)`. Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1 : (1 : ℝ) ≤ (D.R.k : ℝ)` using `le_trans h4 hk`.

Unfold `Scale.p0`. Establish `h5 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2` using `by nlinarith`. Establish `h6 : (D.R.k : ℝ) ^ 2 * 2 ≤ (D.R.k : ℝ) ^ 2 * L.sc.x ^ Scale.A` using `mul_le_mul_of_nonneg_left hA (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pow_four_lt_ceil_threshold_prime (sK : SizeK L) (h3 : 3 ≤ L.sc.x) : L.sc.x ^ 4 + 1 ≤ ((⌈L.sc.p0 D.R.k⌉₊ : ℕ) : ℝ) := by
  have hx := scale_pos_alt L.sc
  refine le_trans ?_ (Nat.le_ceil _)
  have hk := Lnk.x_pow_four_le_k sK
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hk
  have h4 : (1 : ℝ) ≤ L.sc.x ^ 4 := one_le_pow₀ L.sc.one_lt_alt.le
  have hA : (2 : ℝ) ≤ L.sc.x ^ Scale.A := by
    have : L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ Scale.A := Lnk.rpow_mono' _ (by unfold Scale.A; norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := le_trans h4 hk
  unfold Scale.p0
  have h5 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
  have h6 : (D.R.k : ℝ) ^ 2 * 2 ≤ (D.R.k : ℝ) ^ 2 * L.sc.x ^ Scale.A :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨le_trans (Real.rpow_nonneg (scale_pos_alt L.sc).le _) sLa.1, sLa.2.trans (Lnk.rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_pos]))⟩`.
-/
theorem pe_La (sLa : SizeLa L) : 0 ≤ L.LaG ∧ L.LaG ≤ L.sc.x ^ (2 * L.sc.eps) :=
  ⟨le_trans (Real.rpow_nonneg (scale_pos_alt L.sc).le _) sLa.1,
    sLa.2.trans (Lnk.rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_pos]))⟩

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)` using `Nat.cast_nonneg _`. Establish `hpos` using `L.Sc_pos`. Rewrite `hpos` using `[L.Sc_eq]`. Establish `hD : 0 < (D.s.Del : ℝ)`.

Assume the negation of the conclusion as `hcon`. Establish `: (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hk0 (by linarith [not_lt.1 hcon])`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDle : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2)`. Rewrite using `[← Real.exp_log hD]`.

Conclude with `Real.exp_le_exp.mpr sDel.2.2.1`. Establish `h4 : (4 : ℝ) * L.sc.x ^ (5 : ℝ) ≤ L.sc.x ^ (7 : ℝ)`. Establish `e1 : L.sc.x ^ (7 : ℝ) = L.sc.x ^ (2 : ℝ) * L.sc.x ^ (5 : ℝ)`. Rewrite using `[← Real.rpow_add hx]`. Evaluate the numerical expressions.

Rewrite using `[e1, Real.rpow_two]`. Conclude with `mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg hx.le _)`. Establish `hexp : Real.exp (L.sc.x ^ (L.sc.eps / 4)) = Real.exp (1 / 2 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[L.Sc_eq, hexp]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul ?_ hDle hD.le (Real.exp_pos _).le` and prove the remaining obligations. Use `Lnk.winC sK` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pe_Sc_le (sK : SizeK L) (sDel : SizeDel L) (h3 : 3 ≤ L.sc.x)
    (hE : L.sc.x ^ (7 : ℝ) ≤ Real.exp (1 / 2 * L.sc.x ^ (L.sc.eps / 4))) :
    L.Sc ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := by
  have hx := scale_pos_alt L.sc
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hpos := L.Sc_pos
  rw [L.Sc_eq] at hpos
  have hD : 0 < (D.s.Del : ℝ) := by
    by_contra hcon
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hk0 (by linarith [not_lt.1 hcon])
    linarith
  have hDle : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := by
    rw [← Real.exp_log hD]
    exact Real.exp_le_exp.mpr sDel.2.2.1
  have h4 : (4 : ℝ) * L.sc.x ^ (5 : ℝ) ≤ L.sc.x ^ (7 : ℝ) := by
    have e1 : L.sc.x ^ (7 : ℝ) = L.sc.x ^ (2 : ℝ) * L.sc.x ^ (5 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    rw [e1, Real.rpow_two]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg hx.le _)
  have hexp : Real.exp (L.sc.x ^ (L.sc.eps / 4)) =
      Real.exp (1 / 2 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [L.Sc_eq, hexp]
  calc (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) = (4 * (D.R.k : ℝ)) * (D.s.Del : ℝ) := by ring
    _ ≤ Real.exp (1 / 2 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := by
        refine mul_le_mul ?_ hDle hD.le (Real.exp_pos _).le
        have := Lnk.winC sK
        linarith

/- English proof (translation)
Rewrite using `[← Real.exp_log L.etaSz_pos]`. Conclude with `Real.exp_le_exp.mpr sEta.2.2.1`.
-/
theorem pe_eta_le (sEta : SizeEta L) : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := by
  rw [← Real.exp_log L.etaSz_pos]
  exact Real.exp_le_exp.mpr sEta.2.2.1

/- English proof (translation)
Apply `Real.log_nonneg` to reduce the goal to its premises. Use `Lnk.one_le_b s` as an intermediate fact. Unfold `Scale.a`. Use polynomial arithmetic with `[s.one_lt_alt]`.
-/
theorem pe_log_a (s : Scale) : 0 ≤ Real.log s.a := by
  apply Real.log_nonneg
  have := Lnk.one_le_b s
  unfold Scale.a
  nlinarith [s.one_lt_alt]

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `h1 : 0 ≤ K.La` using `hK.1`. Establish `h2 : 0 ≤ K.rho` using `hK.2.1`. Establish `h2' : 0 ≤ K.CN` using `hK.2.2.2.2.2.2.2.2.2.2.2.2.2.2`. Establish `hlx : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg L.sc.one_lt_alt.le`.

Establish `h3` using `pe_log_a L.sc`. Establish `h4 : 0 ≤ L.sc.delta1` using `by unfold Scale.delta1; positivity`. Unfold `G.rhoB G.Nstar G.La`. Check the signs of the components of the expression.
-/
theorem pe_rho_nonneg (K : G.Consts) (hK : K.Nonneg) : 0 ≤ G.rhoB D K L.sc := by
  have hx := scale_pos_alt L.sc
  have h1 : 0 ≤ K.La := hK.1
  have h2 : 0 ≤ K.rho := hK.2.1
  have h2' : 0 ≤ K.CN := hK.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have h3 := pe_log_a L.sc
  have h4 : 0 ≤ L.sc.delta1 := by unfold Scale.delta1; positivity
  unfold G.rhoB G.Nstar G.La
  positivity

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `hk : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2)`.

Establish `: L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2)` using `Lnk.rpow_mono' _ (by unfold Scale.A; norm_num)`. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Check the signs of the components of the expression. Rewrite using `[one_div]`.

Apply `inv_anti₀ hx` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pe_th : 0 ≤ 1 / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ∧
    1 / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.x⁻¹ := by
  have hx := scale_pos_alt L.sc
  have hk : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2) := by
    have : L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) := Lnk.rpow_mono' _ (by unfold Scale.A; norm_num)
    rwa [Real.rpow_one] at this
  constructor
  · positivity
  · rw [one_div]
    apply inv_anti₀ hx
    nlinarith

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `h1` using `pe_k_ge sK`. Establish `h2 : (1 : ℝ) ≤ L.sc.x ^ (3 * Scale.A)` using `pe_one_le _ (by unfold Scale.A; norm_num)`. Establish `h3 : (1 : ℝ) ≤ L.sc.x ^ 2` using `one_le_pow₀ L.sc.one_lt_alt.le`. Establish `h4 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem scale_sq_le_rank_pow (sK : SizeK L) : L.sc.x ^ 2 ≤ (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) := by
  have hx := scale_pos_alt L.sc
  have h1 := pe_k_ge sK
  have h2 : (1 : ℝ) ≤ L.sc.x ^ (3 * Scale.A) := pe_one_le _ (by unfold Scale.A; norm_num)
  have h3 : (1 : ℝ) ≤ L.sc.x ^ 2 := one_le_pow₀ L.sc.one_lt_alt.le
  have h4 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
  nlinarith

/- English proof (translation)
Establish `hd : (0 : ℝ) < (D.host.d : ℝ)` using `by exact_mod_cast D.host.hyp.2.1.pos`. Rewrite `hE` using `[Real.rpow_two, one_mul]`. Rewrite using `[← Real.exp_log hd]`. Conclude with `hE.trans (Real.exp_le_exp.mpr sQD.2.2.2.1)`.
-/
theorem pe_d (sQD : SizeQD L)
    (hE : L.sc.x ^ (2 : ℝ) ≤ Real.exp (1 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100))) :
    L.sc.x ^ 2 ≤ (D.host.d : ℝ) := by
  have hd : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  rw [Real.rpow_two, one_mul] at hE
  rw [← Real.exp_log hd]
  exact hE.trans (Real.exp_le_exp.mpr sQD.2.2.2.1)

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `h0` using `pe_rho_nonneg (L := L) K hK`. Establish `hX : 1 ≤ L.sc.X'`. Unfold `Scale.X'`. Conclude with `Real.one_le_exp (Real.rpow_nonneg hx.le _)`.

Establish `hc : 0 ≤ Cr * G.rhoB D K L.sc` using `mul_nonneg (by linarith) h0`. Establish `hc1 : Cr * G.rhoB D K L.sc ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pe_Y (K : G.Consts) (hK : K.Nonneg) (Cr : ℝ) (hCr1 : 1 ≤ Cr) (hCr : Cr ≤ L.sc.x)
    (hρ : G.rhoB D K L.sc ≤ L.sc.x ^ (-2 : ℝ)) :
    1 ≤ L.sc.X' * (1 + Cr * G.rhoB D K L.sc) ∧ L.sc.X' * (1 + Cr * G.rhoB D K L.sc) ≤ 2 * L.sc.X' := by
  have hx := scale_pos_alt L.sc
  have h0 := pe_rho_nonneg (L := L) K hK
  have hX : 1 ≤ L.sc.X' := by
    unfold Scale.X'
    exact Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hc : 0 ≤ Cr * G.rhoB D K L.sc := mul_nonneg (by linarith) h0
  have hc1 : Cr * G.rhoB D K L.sc ≤ 1 := by
    calc Cr * G.rhoB D K L.sc ≤ L.sc.x * L.sc.x ^ (-2 : ℝ) := mul_le_mul hCr hρ h0 hx.le
      _ ≤ L.sc.x ^ ((-2 : ℝ) + 1) := pe_absorb L.sc (le_refl _) _
      _ ≤ L.sc.x ^ (0 : ℝ) := Lnk.rpow_mono' _ (by norm_num)
      _ = 1 := Real.rpow_zero _
  constructor
  · nlinarith
  · nlinarith

/- English proof (translation)
Establish `hx` using `scale_pos_alt L.sc`. Establish `hp : 0 ≤ L.sc.x ^ (-12 : ℝ)` using `Real.rpow_nonneg hx.le _`. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Establish `hd1 : L.sc.delta1 ≤ 1`. Unfold `Scale.delta1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hn` using `Lnk.n_le_x_cubed sN`. Establish `hn0 : (0 : ℝ) ≤ (D.R.n : ℝ)` using `Nat.cast_nonneg _`. Establish `hT : (D.host.TT.card : ℝ) ≤ L.sc.x ^ (4 : ℝ)`. Establish `h1` using `sTT.2`.

Unfold `szNst at h1`. Establish `h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * (D.R.n : ℝ) * 1` using `mul_le_mul_of_nonneg_left hd1 (by positivity)`. Establish `h4` using `pe_absorb L.sc (c := 2) (by linarith) 3`. Rewrite `h4` using `[show (3 : ℝ) + 1 = 4 by norm_num]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmT : (D.R.m : ℝ) * (D.host.TT.card : ℝ) ≤ L.sc.x ^ (5 : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← rpow_neg_two_eq_inv_sq_alt]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_count_scaled_bounds (sN : SizeN L) (sM : SizeM L) (sTT : SizeTT L) (h3 : 3 ≤ L.sc.x) :
    0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ) ∧
    (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ) ≤ (L.sc.x ^ 2)⁻¹ := by
  have hx := scale_pos_alt L.sc
  have hp : 0 ≤ L.sc.x ^ (-12 : ℝ) := Real.rpow_nonneg hx.le _
  refine ⟨by positivity, ?_⟩
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    calc L.sc.x ^ (-(L.sc.eps / 8)) ≤ L.sc.x ^ (0 : ℝ) := Lnk.rpow_mono' _ (by linarith [L.sc.eps_pos])
      _ = 1 := Real.rpow_zero _
  have hn := Lnk.n_le_x_cubed sN
  have hn0 : (0 : ℝ) ≤ (D.R.n : ℝ) := Nat.cast_nonneg _
  have hT : (D.host.TT.card : ℝ) ≤ L.sc.x ^ (4 : ℝ) := by
    have h1 := sTT.2
    unfold szNst at h1
    have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * (D.R.n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hd1 (by positivity)
    have h4 := pe_absorb L.sc (c := 2) (by linarith) 3
    rw [show (3 : ℝ) + 1 = 4 by norm_num] at h4
    linarith
  have hmT : (D.R.m : ℝ) * (D.host.TT.card : ℝ) ≤ L.sc.x ^ (5 : ℝ) := by
    calc (D.R.m : ℝ) * (D.host.TT.card : ℝ) ≤ L.sc.x * L.sc.x ^ (4 : ℝ) :=
          mul_le_mul (pe_m_le sM) hT (Nat.cast_nonneg _) hx.le
      _ ≤ L.sc.x ^ ((4 : ℝ) + 1) := pe_absorb L.sc (le_refl _) _
      _ = L.sc.x ^ (5 : ℝ) := by norm_num
  rw [← rpow_neg_two_eq_inv_sq_alt]
  calc (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ) ≤ L.sc.x ^ (5 : ℝ) * L.sc.x ^ (-12 : ℝ) :=
        mul_le_mul_of_nonneg_right hmT hp
    _ = L.sc.x ^ (-7 : ℝ) := by rw [← Real.rpow_add hx]; norm_num
    _ ≤ L.sc.x ^ (-2 : ℝ) := Lnk.rpow_mono' _ (by norm_num)

def pe_parAt (L : SizeData₂ D) (K : G.Consts) (Cr C bo Cb Cord : ℝ) : Par where
  x := L.sc.x
  ε := L.sc.eps
  e₂ := D.R.e
  nA := D.R.n
  k := D.R.k
  N := (D.R.N D.R.m : ℝ)
  t := D.R.t
  p₀ := ⌈L.sc.p0 D.R.k⌉₊
  La := L.LaG
  rG := (Formalism.MainNotions.rG L.sc.eps : ℝ)
  Sc := L.Sc
  η := L.etaSz
  ρ := G.rhoB D K L.sc
  th := 1 / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))
  K₀ := (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A)
  d := D.host.d
  C := max C 0
  β := max Cb 0 * L.sc.x ^ (-2 : ℝ)
  Cord := Cord
  Y := L.sc.X' * (1 + Cr * G.rhoB D K L.sc)
  s₀ := (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)
  bo := bo

/- English proof (translation)
Take `⟨sN, sM, sK, sKR, sT, sCond, sQD, sTT, sLa, sRho, sBot, sDe2, sLw, sEta, sNodes, sLstar, sDel, sW, sBm, sXpp, sG, sPde, sWords⟩` from `hS`. Establish `hx` using `scale_pos_alt L.sc`. Establish `hinv : 0 ≤ (L.sc.x ^ 2)⁻¹` using `by positivity`. Establish `hC1 : max C 0 ≤ 1 + |C| + |Cb| + Cord`. Use `abs_nonneg Cb` as an intermediate fact.

Conclude with `max_le (by linarith [le_abs_self C]) (by linarith [abs_nonneg C])`. Establish `hC2 : max Cb 0 ≤ 1 + |C| + |Cb| + Cord`. Use `abs_nonneg C` as an intermediate fact. Conclude with `max_le (by linarith [le_abs_self Cb]) (by linarith [abs_nonneg Cb])`. Establish `hrG' : (Formalism.MainNotions.rG L.sc.eps : ℝ) ≤ L.sc.x ^ e`.

Establish `: L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ e` using `Lnk.rpow_mono' _ (by linarith)`. Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hβ : max Cb 0 * L.sc.x ^ (-2 : ℝ) ≤ (1 + |C| + |Cb| + Cord) * (L.sc.x ^ 2)⁻¹`. Rewrite using `[rpow_neg_two_eq_inv_sq_alt]`.

Conclude with `mul_le_mul_of_nonneg_right hC2 hinv`. Establish `hε1 : L.sc.eps ≤ 1` using `by linarith [L.sc.eps_lt]`. Establish `hρ' : G.rhoB D K L.sc ≤ (L.sc.x ^ 2)⁻¹` using `by rw [← rpow_neg_two_eq_inv_sq_alt]; exact hρ`. Establish `hCo : Cord ≤ 1 + |C| + |Cb| + Cord` using `by linarith [abs_nonneg C, abs_nonneg Cb]`. Conclude with `⟨L.sc.eps_pos, hε1, by linarith, by linarith [abs_nonneg C, abs_nonneg Cb], ⟨pe_n_ge sN, (pe_n D.R).1⟩, pe_n_le sN he, pe_k_ge sK, pe_k_le sK he, Nat.cast_nonneg _, pe_N_le sM sK h3 he hc, Nat.cast_nonneg _, pe_t_le hc, pow_four_lt_ceil_threshold_prime sK h3, ceil_threshold_prime …`.
-/
theorem pe_windows_at (K : G.Consts) (hK : K.Nonneg) (Cr C bo Cb Cord e : ℝ) (hS : SizesAt L) (h3 : 3 ≤ L.sc.x)
    (hCr1 : 1 ≤ Cr) (hCr : Cr ≤ L.sc.x) (hρ : G.rhoB D K L.sc ≤ L.sc.x ^ (-2 : ℝ))
    (hrG : (Formalism.MainNotions.rG L.sc.eps : ℝ) ≤ L.sc.x)
    (hE7 : L.sc.x ^ (7 : ℝ) ≤ Real.exp (1 / 2 * L.sc.x ^ (L.sc.eps / 4)))
    (hE2 : L.sc.x ^ (2 : ℝ) ≤ Real.exp (1 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100)))
    (hbo0 : 0 ≤ bo) (hbo : bo ≤ Real.exp (L.sc.x ^ L.sc.eps / 2)) (hCord : 0 ≤ Cord)
    (he : 40 ≤ e) (hc : L.Ct + 3 ≤ e) :
    Windows (pe_parAt L K Cr C bo Cb Cord) e (1 + |C| + |Cb| + Cord) := by
  obtain ⟨sN, sM, sK, sKR, sT, sCond, sQD, sTT, sLa, sRho, sBot, sDe2, sLw, sEta, sNodes, sLstar, sDel, sW, sBm,
    sXpp, sG, sPde, sWords⟩ := hS
  have hx := scale_pos_alt L.sc
  have hinv : 0 ≤ (L.sc.x ^ 2)⁻¹ := by positivity
  have hC1 : max C 0 ≤ 1 + |C| + |Cb| + Cord := by
    have := abs_nonneg Cb
    exact max_le (by linarith [le_abs_self C]) (by linarith [abs_nonneg C])
  have hC2 : max Cb 0 ≤ 1 + |C| + |Cb| + Cord := by
    have := abs_nonneg C
    exact max_le (by linarith [le_abs_self Cb]) (by linarith [abs_nonneg Cb])
  have hrG' : (Formalism.MainNotions.rG L.sc.eps : ℝ) ≤ L.sc.x ^ e := by
    have : L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ e := Lnk.rpow_mono' _ (by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hβ : max Cb 0 * L.sc.x ^ (-2 : ℝ) ≤ (1 + |C| + |Cb| + Cord) * (L.sc.x ^ 2)⁻¹ := by
    rw [rpow_neg_two_eq_inv_sq_alt]
    exact mul_le_mul_of_nonneg_right hC2 hinv
  have hε1 : L.sc.eps ≤ 1 := by linarith [L.sc.eps_lt]
  have hρ' : G.rhoB D K L.sc ≤ (L.sc.x ^ 2)⁻¹ := by rw [← rpow_neg_two_eq_inv_sq_alt]; exact hρ
  have hCo : Cord ≤ 1 + |C| + |Cb| + Cord := by linarith [abs_nonneg C, abs_nonneg Cb]
  exact ⟨L.sc.eps_pos, hε1, by linarith, by linarith [abs_nonneg C, abs_nonneg Cb],
    ⟨pe_n_ge sN, (pe_n D.R).1⟩, pe_n_le sN he, pe_k_ge sK, pe_k_le sK he, Nat.cast_nonneg _, pe_N_le sM sK h3 he hc,
    Nat.cast_nonneg _, pe_t_le hc, pow_four_lt_ceil_threshold_prime sK h3, ceil_threshold_prime_le_pow sK h3 he, (pe_La sLa).1, (pe_La sLa).2,
    Nat.cast_nonneg _, hrG', L.Sc_pos.le, pe_Sc_le sK sDel h3 hE7, L.etaSz_pos.le, pe_eta_le sEta,
    pe_rho_nonneg K hK, hρ', pe_th.1, pe_th.2, scale_sq_le_rank_pow sK, pe_d sQD hE2,
    le_max_right _ _, hC1, mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx.le _), hβ, hCord,
    hCo, (pe_Y K hK Cr hCr1 hCr hρ).1, (pe_Y K hK Cr hCr1 hCr hρ).2,
    (rank_count_scaled_bounds sN sM sTT h3).1, (rank_count_scaled_bounds sN sM sTT h3).2, hbo0, hbo⟩

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pe_par_eq (x : ℝ) (i0 : Fm.Ix x) (C bo Cb Cord : ℝ) :
    par Fm x i0 C bo Cb Cord = pe_parAt (Fm.L x i0) Fm.GK Fm.Cr C bo Cb Cord := rfl

/- English proof (translation)
Establish `heps : 0 < eps` using `Lnk.fam_eps_pos Fm`. Take `⟨a7, h7⟩` from `Lnk.ev_pow_le_exp (1 / 2) (eps / 4) 7 (by norm_num) (by positivity)`. Establish `hez : 0 < Fm.ez` using `div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)`. Take `⟨a2, h2⟩` from `Lnk.ev_pow_le_exp 1 (Fm.ez / 5 - Fm.ez / 100) 2 (by norm_num) (by linarith)`. Take `⟨a36, h36⟩` from `Lnk.ev_pow_le_exp 1 (eps / 3) 36 (by norm_num) (by positivity)`.

Take `⟨aδ, hδ'⟩` from `Filter.eventually_atTop.mp (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))`. Use `⟨max 40 (Fm.Ct + 3), 1 + |C| + |Cb| + Cord, max (Fm.x1 + 1) (max 3 (max (Formalism.MainNotions.rG eps : ℝ) (max Fm.Cr (max a7 (max a2 (max a36 aδ)))))), fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [ge_iff_le, max_le_iff] at hx`. Take `⟨b1, b3, brG, bCr, b7, b2, b36, bδ⟩` from `hx`. Establish `hx1 : Fm.x1 < x` using `by linarith`.

Establish `h1x : 1 ≤ x` using `by linarith`. Use `⟨hx1, b3, fun i0 => ?_⟩` and prove the remaining obligations. Establish `hsx` using `Fm.L_x x i0 hx1`. Establish `hse` using `Fm.L_eps x i0`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `hS` using `Fm.sizes x hx1 i0`. Prove the components needed by the constructor for the conclusion. Rewrite using `[pe_par_eq]`. Use `pe_windows_at Fm.GK Fm.GK_nonneg Fm.Cr C _ Cb Cord _ hS (by rw [hsx]; exact b3) Fm.one_le_Cr (by rw [hsx]; exact bCr) (by rw [hsx]; exact Fm.rho_le x hx1 i0) (by rw [hsx, hse]; exact brG) (by rw [hsx, hse]; exact h7 x b7 h1x) (by rw [hsx, Fm.L_ez x i0]; exact h2 x b2 h1x) (Real.r …` and prove the remaining obligations. Unfold `Scale.b Scale.L`.

Rewrite using `[← Real.exp_mul, hsx, hse]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hp : 0 ≤ x ^ eps` using `Real.rpow_nonneg hx0.le _`. Use `mul_le_mul_of_nonneg_left (hδ' x bδ).le hp` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h` using `h36 x b36 h1x`. Rewrite `h` using `[one_mul]`. Use `(threshold_prime_le_pow hS.2.2.1).trans ?_` and prove the remaining obligations. Unfold `Scale.X'`. Rewrite using `[hsx, hse]`.

Conclude with `h`.
-/
theorem windows_ev (C Cb Cord : ℝ) (hCord : 0 ≤ Cord) (δ : ℝ → ℝ) (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    ∃ e K x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧ 3 ≤ x ∧ ∀ i0 : Fm.Ix x,
      Windows (par Fm x i0 C ((Fm.L x i0).sc.b ^ δ x) Cb Cord) e K ∧
      (Fm.L x i0).sc.p0 (Fm.D x i0).R.k ≤ (Fm.L x i0).sc.X' := by
  have heps : 0 < eps := Lnk.fam_eps_pos Fm
  obtain ⟨a7, h7⟩ := Lnk.ev_pow_le_exp (1 / 2) (eps / 4) 7 (by norm_num) (by positivity)
  have hez : 0 < Fm.ez := div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)
  obtain ⟨a2, h2⟩ := Lnk.ev_pow_le_exp 1 (Fm.ez / 5 - Fm.ez / 100) 2 (by norm_num) (by linarith)
  obtain ⟨a36, h36⟩ := Lnk.ev_pow_le_exp 1 (eps / 3) 36 (by norm_num) (by positivity)
  obtain ⟨aδ, hδ'⟩ := Filter.eventually_atTop.mp
    (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨max 40 (Fm.Ct + 3), 1 + |C| + |Cb| + Cord,
    max (Fm.x1 + 1) (max 3 (max (Formalism.MainNotions.rG eps : ℝ) (max Fm.Cr (max a7 (max a2 (max a36 aδ)))))), fun x hx => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨b1, b3, brG, bCr, b7, b2, b36, bδ⟩ := hx
  have hx1 : Fm.x1 < x := by linarith
  have h1x : 1 ≤ x := by linarith
  refine ⟨hx1, b3, fun i0 => ?_⟩
  have hsx := Fm.L_x x i0 hx1
  have hse := Fm.L_eps x i0
  have hx0 : 0 < x := by linarith
  have hS := Fm.sizes x hx1 i0
  constructor
  · rw [pe_par_eq]
    refine pe_windows_at Fm.GK Fm.GK_nonneg Fm.Cr C _ Cb Cord _ hS (by rw [hsx]; exact b3) Fm.one_le_Cr
      (by rw [hsx]; exact bCr) (by rw [hsx]; exact Fm.rho_le x hx1 i0) (by rw [hsx, hse]; exact brG)
      (by rw [hsx, hse]; exact h7 x b7 h1x) (by rw [hsx, Fm.L_ez x i0]; exact h2 x b2 h1x)
      (Real.rpow_nonneg (Real.exp_pos _).le _) ?_ hCord (le_max_left _ _)
      (by rw [Fm.Ct_eq x i0]; exact le_max_right _ _)
    unfold Scale.b Scale.L
    rw [← Real.exp_mul, hsx, hse]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ x ^ eps := Real.rpow_nonneg hx0.le _
    have := mul_le_mul_of_nonneg_left (hδ' x bδ).le hp
    linarith
  · have h := h36 x b36 h1x
    rw [one_mul] at h
    refine (threshold_prime_le_pow hS.2.2.1).trans ?_
    unfold Scale.X'
    rw [hsx, hse]
    exact h

end Family

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss.Marg

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

section marg

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

open Classical in

def margC (φ : β → α) (T : α → Finset ℤ) : ℕ := ∏ t, (if ∃ i, φ i = t then 1 else (T t).card)

open Classical in
/- English proof (translation)
Establish `: (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a') = Fintype.piFinset (fun t => if h : ∃ i, φ i = t then {a' h.choose} else T t)`. Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Fintype.mem_piFinset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ t`.

Distinguish the cases in `h : ∃ i, φ i = t`. Rewrite using `[dif_pos h, Finset.mem_singleton, ← h2] show a t = a (φ h.choose)`. Rewrite using `[h.choose_spec]`. Rewrite using `[dif_neg h]`. Conclude with `h1 t`.

Introduce `h1`. Establish `key : ∀ i, a (φ i) = a' i`. Introduce `i`. Establish `h : ∃ i', φ i' = φ i` using `⟨i, rfl⟩`. Establish `h2` using `h1 (φ i)`.

Rewrite `h2` using `[dif_pos h, Finset.mem_singleton]`. Rewrite using `[h2, hφ h.choose_spec]`. Use `⟨fun t => ?_, funext key⟩` and prove the remaining obligations. Distinguish the cases in `h : ∃ i, φ i = t`. Take `⟨i, rfl⟩` from `h`.

Rewrite using `[key]`. Conclude with `ha' i`. Establish `h2` using `h1 t`. Rewrite `h2` using `[dif_neg h]`. Then use the resulting hypothesis. Rewrite using `[this, Fintype.card_piFinset]`.

Unfold `margC`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `t _`. Distinguish the cases in `h : ∃ i, φ i = t`. Rewrite using `[dif_pos h, if_pos h, Finset.card_singleton]`.

Rewrite using `[dif_neg h, if_neg h]`.
-/
theorem marg_fibre (φ : β → α) (hφ : Function.Injective φ) (T : α → Finset ℤ) (a' : β → ℤ)
    (ha' : ∀ i, a' i ∈ T (φ i)) :
    ((Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a')).card = margC φ T := by
  have : (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a') =
      Fintype.piFinset (fun t => if h : ∃ i, φ i = t then {a' h.choose} else T t) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ t
      by_cases h : ∃ i, φ i = t
      · rw [dif_pos h, Finset.mem_singleton, ← h2]
        show a t = a (φ h.choose)
        rw [h.choose_spec]
      · rw [dif_neg h]; exact h1 t
    · intro h1
      have key : ∀ i, a (φ i) = a' i := by
        intro i
        have h : ∃ i', φ i' = φ i := ⟨i, rfl⟩
        have h2 := h1 (φ i)
        rw [dif_pos h, Finset.mem_singleton] at h2
        rw [h2, hφ h.choose_spec]
      refine ⟨fun t => ?_, funext key⟩
      by_cases h : ∃ i, φ i = t
      · obtain ⟨i, rfl⟩ := h
        rw [key]; exact ha' i
      · have h2 := h1 t
        rwa [dif_neg h] at h2
  rw [this, Fintype.card_piFinset]
  unfold margC
  apply Finset.prod_congr rfl
  intro t _
  by_cases h : ∃ i, φ i = t
  · rw [dif_pos h, if_pos h, Finset.card_singleton]
  · rw [dif_neg h, if_neg h]

open Classical in
/- English proof (translation)
Establish `hm : ∀ a ∈ Fintype.piFinset T, (fun i => a (φ i)) ∈ Fintype.piFinset T'`. Introduce `a ha`. Rewrite `ha`, the goal using `[Fintype.mem_piFinset]`. Introduce `i`. Rewrite using `[hT]`.

Conclude with `ha _`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hm, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a' ha'`. Rewrite `ha'` using `[Fintype.mem_piFinset]`.

Establish `h1 : ∀ a ∈ (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a'), F (fun i => a (φ i)) = F a'`. Introduce `a ha`. Rewrite using `[(Finset.mem_filter.1 ha).2]`. Establish `h2` using `marg_fibre φ hφ T a' (fun i => by rw [← hT]; exact ha' i)`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]`.

Use `congr 2`.
-/
theorem marg_sum (φ : β → α) (hφ : Function.Injective φ) (T : α → Finset ℤ) (T' : β → Finset ℤ)
    (hT : ∀ i, T' i = T (φ i)) (F : (β → ℤ) → ℝ) :
    ∑ a ∈ Fintype.piFinset T, F (fun i => a (φ i)) = (margC φ T : ℝ) * ∑ a' ∈ Fintype.piFinset T', F a' := by
  have hm : ∀ a ∈ Fintype.piFinset T, (fun i => a (φ i)) ∈ Fintype.piFinset T' := by
    intro a ha
    rw [Fintype.mem_piFinset] at ha ⊢
    intro i; rw [hT]; exact ha _
  rw [← Finset.sum_fiberwise_of_maps_to hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a' ha'
  rw [Fintype.mem_piFinset] at ha'
  have h1 : ∀ a ∈ (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a'),
      F (fun i => a (φ i)) = F a' := by
    intro a ha; rw [(Finset.mem_filter.1 ha).2]
  have h2 := marg_fibre φ hφ T a' (fun i => by rw [← hT]; exact ha' i)
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  congr 2

/- English proof (translation)
Establish `h` using `marg_sum φ hφ T T' hT (fun _ => 1)`. Simplify using `using h`.
-/
theorem marg_card (φ : β → α) (hφ : Function.Injective φ) (T : α → Finset ℤ) (T' : β → Finset ℤ)
    (hT : ∀ i, T' i = T (φ i)) :
    ((Fintype.piFinset T).card : ℝ) = (margC φ T : ℝ) * ((Fintype.piFinset T').card : ℝ) := by
  have h := marg_sum φ hφ T T' hT (fun _ => 1)
  simpa using h

end marg

def phi (D : D7) (p : ℕ) (t0 : HH D) : Fin (addOrderOf (hP D p)) → HH D := fun i => t0 + (i : ℕ) • hP D p

/- English proof (translation)
Introduce `i j hij`. Establish `h1 : (i : ℕ) • hP D p = (j : ℕ) • hP D p` using `add_left_cancel hij`. Conclude with `Fin.ext (nsmul_injOn_Iio_addOrderOf i.2 j.2 h1)`.
-/
theorem phi_inj (p : ℕ) (t0 : HH D) : Function.Injective (phi D p t0) := by
  intro i j hij
  have h1 : (i : ℕ) • hP D p = (j : ℕ) • hP D p := add_left_cancel hij
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf i.2 j.2 h1)

/- English proof (translation)
Unfold `Nv topsOn`. Rewrite using `[Finset.sum_card_fiberwise_eq_card_filter]`. Conclude with `Finset.card_filter_le _ _`.
-/
theorem sum_Nv_le (X : Inst D L) (p : ℕ) (S : Finset (HH D)) : ∑ t0 ∈ S, Nv X p t0 ≤ D.host.TT.card := by
  unfold Nv topsOn
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.card_filter_le _ _

/- English proof (translation)
Establish `hmem : ∀ i, i ∈ topsPos D p t0 ↔ phi D p t0 i ∈ D.host.TT`. Introduce `i`. Unfold `topsPos phi`. Simplify using the standard rewrite rules. Use `⟨(margC (phi D p t0) (fun t => if t ∈ D.host.TT then W else {0}) : ℕ), ?_, ?_⟩` and prove the remaining obligations.

Introduce `F`. Unfold `box boxLoc`. Conclude with `marg_sum (phi D p t0) (phi_inj p t0) _ _ (fun i => by`. Distinguish the cases in `h : phi D p t0 i ∈ D.host.TT`. Rewrite using `[if_pos h, if_pos ((hmem i).2 h)]`.

Rewrite using `[if_neg h, if_neg (mt (hmem i).1 h)]) F`. Unfold `box boxLoc`. Conclude with `marg_card (phi D p t0) (phi_inj p t0) _ _ (fun i => by`. Distinguish the cases in `h : phi D p t0 i ∈ D.host.TT`. Rewrite using `[if_pos h, if_pos ((hmem i).2 h)]`.

Rewrite using `[if_neg h, if_neg (mt (hmem i).1 h)])`.
-/
theorem box_marg (p : ℕ) (t0 : HH D) (W : Finset ℤ) :
    ∃ c : ℝ, (∀ F : (Fin (addOrderOf (hP D p)) → ℤ) → ℝ,
        ∑ a ∈ box D W, F (wPos D p t0 a) = c * ∑ a' ∈ boxLoc _ (topsPos D p t0) W, F a') ∧
      ((box D W).card : ℝ) = c * ((boxLoc _ (topsPos D p t0) W).card : ℝ) := by
  classical
  have hmem : ∀ i, i ∈ topsPos D p t0 ↔ phi D p t0 i ∈ D.host.TT := by
    intro i
    unfold topsPos phi
    simp
  refine ⟨(margC (phi D p t0) (fun t => if t ∈ D.host.TT then W else {0}) : ℕ), ?_, ?_⟩
  · intro F
    unfold box boxLoc
    exact marg_sum (phi D p t0) (phi_inj p t0) _ _ (fun i => by
      by_cases h : phi D p t0 i ∈ D.host.TT
      · rw [if_pos h, if_pos ((hmem i).2 h)]
      · rw [if_neg h, if_neg (mt (hmem i).1 h)]) F
  · unfold box boxLoc
    exact marg_card (phi D p t0) (phi_inj p t0) _ _ (fun i => by
      by_cases h : phi D p t0 i ∈ D.host.TT
      · rw [if_pos h, if_pos ((hmem i).2 h)]
      · rw [if_neg h, if_neg (mt (hmem i).1 h)])

end Formalism.L2.GlobalTheoryTheory.Loss.Marg

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions

section AtRecordMean

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Unfold `G.boxLoc`. Rewrite using `[Fintype.piFinset_nonempty]`. Introduce `i`. Use `split_ifs with h`. Apply `hW` to reduce the goal to its premises.

Unfold `G.topsPos at h`. Conclude with `⟨_, (Finset.mem_filter.1 h).2⟩`. Conclude with `Finset.singleton_nonempty _`.
-/
theorem pf_boxLoc_ne (p : ℕ) (t0 : G.HH D) (W : Finset ℤ) (hW : D.host.TT.Nonempty → W.Nonempty) :
    (G.boxLoc _ (G.topsPos D p t0) W).Nonempty := by
  classical
  unfold G.boxLoc
  rw [Fintype.piFinset_nonempty]
  intro i
  split_ifs with h
  · apply hW
    unfold G.topsPos at h
    exact ⟨_, (Finset.mem_filter.1 h).2⟩
  · exact Finset.singleton_nonempty _

/- English proof (translation)
Take `⟨cA, hA, hAc⟩` from `Marg.box_marg p t0 (G.winA D L.sc)`. Take `⟨cB, hB, hBc⟩` from `Marg.box_marg p t0 (G.winB D K L.sc)`. Establish `h1 : ∀ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), F (G.wPos D p t0 a) (G.wPos D p t0 b) = cB * ∑ b' ∈ G.boxLoc _ (G.topsPos D p t0) (G.winB D K L.sc), F (G.wPos D p t0 a) b'` using `fun a _ => hB (F (G.wPos D p t0 a))`. Rewrite using `[Finset.sum_congr rfl h1, hA (fun a' => cB * ∑ b' ∈ G.boxLoc _ (G.topsPos D p t0) (G.winB D K L.sc), F a' b'), ← Finset.mul_sum]`. Unfold `G.meanLoc`.

Rewrite using `[hAc, hBc]`. Establish `hSA : ((G.boxLoc _ (G.topsPos D p t0) (G.winA D L.sc)).card : ℝ) ≠ 0`. Use `(pf_boxLoc_ne p t0 _ hWA).card_pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Establish `hSB : ((G.boxLoc _ (G.topsPos D p t0) (G.winB D K L.sc)).card : ℝ) ≠ 0`.

Use `(pf_boxLoc_ne p t0 _ hWB).card_pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_box_product (K : G.Consts) (hWA : D.host.TT.Nonempty → (G.winA D L.sc).Nonempty)
    (hWB : D.host.TT.Nonempty → (G.winB D K L.sc).Nonempty) (p : ℕ) (t0 : G.HH D)
    (F : (Fin (addOrderOf (G.hP D p)) → ℤ) → (Fin (addOrderOf (G.hP D p)) → ℤ) → ℝ) :
    ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), F (G.wPos D p t0 a) (G.wPos D p t0 b) =
      ((G.box D (G.winA D L.sc)).card : ℝ) * ((G.box D (G.winB D K L.sc)).card : ℝ) *
        G.meanLoc D K L.sc _ (G.topsPos D p t0) F := by
  obtain ⟨cA, hA, hAc⟩ := Marg.box_marg p t0 (G.winA D L.sc)
  obtain ⟨cB, hB, hBc⟩ := Marg.box_marg p t0 (G.winB D K L.sc)
  have h1 : ∀ a ∈ G.box D (G.winA D L.sc),
      ∑ b ∈ G.box D (G.winB D K L.sc), F (G.wPos D p t0 a) (G.wPos D p t0 b) =
      cB * ∑ b' ∈ G.boxLoc _ (G.topsPos D p t0) (G.winB D K L.sc), F (G.wPos D p t0 a) b' :=
    fun a _ => hB (F (G.wPos D p t0 a))
  rw [Finset.sum_congr rfl h1,
    hA (fun a' => cB * ∑ b' ∈ G.boxLoc _ (G.topsPos D p t0) (G.winB D K L.sc), F a' b'), ← Finset.mul_sum]
  unfold G.meanLoc
  rw [hAc, hBc]
  have hSA : ((G.boxLoc _ (G.topsPos D p t0) (G.winA D L.sc)).card : ℝ) ≠ 0 := by
    have := (pf_boxLoc_ne p t0 _ hWA).card_pos
    exact_mod_cast this.ne'
  have hSB : ((G.boxLoc _ (G.topsPos D p t0) (G.winB D K L.sc)).card : ℝ) ≠ 0 := by
    have := (pf_boxLoc_ne p t0 _ hWB).card_pos
    exact_mod_cast this.ne'
  field_simp

/- English proof (translation)
Establish `h` using `sum_box_product K hWA hWB p t0 (fun a b => G.kapLoc X K p (addOrderOf (G.hP D p)) (G.topsPos D p t0) a b)`. Establish `h' : ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0 = ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), (fun a b => G.kapLoc X K p (addOrderOf (G.hP D p)) (G.topsPos D p t0) a b) (G.wPos D p t0 a) (G.wPos D p t0 b)` using `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => rfl`. Rewrite using `[h', h]`. Conclude with `mul_le_mul_of_nonneg_left (h2 p hc t0 ht0).1 (by positivity)`.
-/
theorem pf_sum_kapv_le (X : G.Inst D L) (K : G.Consts) (hWA : D.host.TT.Nonempty → (G.winA D L.sc).Nonempty)
    (hWB : D.host.TT.Nonempty → (G.winB D K L.sc).Nonempty) (h2 : G.MeanKappaBound X K)
    (p : ℕ) (hc : G.Cand D L K p) (t0 : G.HH D) (ht0 : t0 ∈ G.goodReps X p) :
    ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0 ≤
      ((G.box D (G.winA D L.sc)).card : ℝ) * ((G.box D (G.winB D K L.sc)).card : ℝ) *
        ((G.Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
  have h := sum_box_product K hWA hWB p t0
    (fun a b => G.kapLoc X K p (addOrderOf (G.hP D p)) (G.topsPos D p t0) a b)
  have h' : ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0 =
      ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc),
        (fun a b => G.kapLoc X K p (addOrderOf (G.hP D p)) (G.topsPos D p t0) a b)
          (G.wPos D p t0 a) (G.wPos D p t0 b) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => rfl
  rw [h', h]
  exact mul_le_mul_of_nonneg_left (h2 p hc t0 ht0).1 (by positivity)

/- English proof (translation)
Establish `hx12 : 0 ≤ L.sc.x ^ (-12 : ℝ)` using `Real.rpow_nonneg (lt_trans one_pos L.sc.one_lt_alt).le _`. Generalize the expression as in `hcc : ((G.box D (G.winA D L.sc)).card : ℝ) * ((G.box D (G.winB D K L.sc)).card : ℝ) = cc`. Establish `hcc0 : 0 ≤ cc` using `by rw [← hcc]; positivity`. Establish `e2 : ∀ t0 ∈ G.goodReps X p, ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0 ≤ cc * ((G.Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ))`. Introduce `t0 ht0`.

Rewrite using `[← hcc]`. Conclude with `pf_sum_kapv_le X K hWA hWB h2 p hc t0 ht0`. Unfold `G.Sig`. Establish `e1 : ∀ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), (D.R.m : ℝ) * ∑ t0 ∈ G.goodReps X p, G.kapv X K a b p t0 = (D.R.m : ℝ) * ∑ t0 ∈ G.goodReps X p, ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0`. Introduce `a _`.

Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Rewrite using `[Finset.sum_congr rfl e1, ← Finset.mul_sum, Finset.sum_comm]`. Establish `e3 : ∑ t0 ∈ G.goodReps X p, cc * ((G.Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ)) ≤ cc * ((D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ))`. Rewrite using `[← Finset.mul_sum, ← Finset.sum_mul]`. Establish `h : (∑ t0 ∈ G.goodReps X p, (G.Nv X p t0 : ℝ)) ≤ (D.host.TT.card : ℝ)`.

Conclude with `Marg.sum_Nv_le X p (G.goodReps X p)` after adjusting the coercions. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hx12) hcc0`. Establish `e4` using `mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum e2) e3) (Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pf_sum_Sig_le (X : G.Inst D L) (K : G.Consts) (hWA : D.host.TT.Nonempty → (G.winA D L.sc).Nonempty)
    (hWB : D.host.TT.Nonempty → (G.winB D K L.sc).Nonempty) (h2 : G.MeanKappaBound X K)
    (p : ℕ) (hc : G.Cand D L K p) :
    ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), G.Sig X K a b p ≤
      ((G.box D (G.winA D L.sc)).card : ℝ) * ((G.box D (G.winB D K L.sc)).card : ℝ) *
        ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
  have hx12 : 0 ≤ L.sc.x ^ (-12 : ℝ) := Real.rpow_nonneg (lt_trans one_pos L.sc.one_lt_alt).le _
  generalize hcc : ((G.box D (G.winA D L.sc)).card : ℝ) * ((G.box D (G.winB D K L.sc)).card : ℝ) = cc
  have hcc0 : 0 ≤ cc := by rw [← hcc]; positivity
  have e2 : ∀ t0 ∈ G.goodReps X p,
      ∑ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0 ≤
      cc * ((G.Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
    intro t0 ht0
    rw [← hcc]
    exact pf_sum_kapv_le X K hWA hWB h2 p hc t0 ht0
  unfold G.Sig
  have e1 : ∀ a ∈ G.box D (G.winA D L.sc), ∑ b ∈ G.box D (G.winB D K L.sc),
      (D.R.m : ℝ) * ∑ t0 ∈ G.goodReps X p, G.kapv X K a b p t0 =
      (D.R.m : ℝ) * ∑ t0 ∈ G.goodReps X p, ∑ b ∈ G.box D (G.winB D K L.sc), G.kapv X K a b p t0 := by
    intro a _
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, Finset.sum_comm]
  have e3 : ∑ t0 ∈ G.goodReps X p, cc * ((G.Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ)) ≤
      cc * ((D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h : (∑ t0 ∈ G.goodReps X p, (G.Nv X p t0 : ℝ)) ≤ (D.host.TT.card : ℝ) := by
      exact_mod_cast Marg.sum_Nv_le X p (G.goodReps X p)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hx12) hcc0
  have e4 := mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum e2) e3) (Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ _)
  calc _ ≤ (D.R.m : ℝ) * (cc * ((D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ))) := e4
    _ = _ := by ring

end AtRecordMean

section FamilyMean

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ} {i0 : Fm.Ix x}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pf_winA_eq : Lnk.winAz Fm x i0 = G.winA (Fm.D x i0) (Fm.L x i0).sc := rfl

/- English proof (translation)
Take `⟨w, -⟩` from `Lnk.place_over (Fm.D x i0) 2 Nat.prime_two`. Establish `hLa : G.La Fm.GK (Fm.L x i0).sc = (Fm.L x i0).LaG` using `(Fm.fills x hx i0 w).2.2.2.2.2.2`. Unfold `Lnk.winBz G.winB G.Nstar`. Rewrite using `[Fm.bTop_eq x hx i0, hLa, Fm.L_x x i0 hx, Fm.L_eps x i0]`.
-/
theorem pf_winB_eq (hx : Fm.x1 < x) : Lnk.winBz Fm x i0 = G.winB (Fm.D x i0) Fm.GK (Fm.L x i0).sc := by
  obtain ⟨w, -⟩ := Lnk.place_over (Fm.D x i0) 2 Nat.prime_two
  have hLa : G.La Fm.GK (Fm.L x i0).sc = (Fm.L x i0).LaG := (Fm.fills x hx i0 w).2.2.2.2.2.2
  unfold Lnk.winBz G.winB G.Nstar
  rw [Fm.bTop_eq x hx i0, hLa, Fm.L_x x i0 hx, Fm.L_eps x i0]

/- English proof (translation)
Rewrite using `[← Fm.TT_eq x i0, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨t, h, rfl⟩`. Introduce and unpack `⟨s, hs, hst⟩`.

Rewrite using `[← Formalism.HC.Frame.A.val_injective _ hst]` and apply the resulting hypothesis.
-/
theorem pf_mem_TT (t : G.HH (Fm.D x i0)) : t ∈ (Fm.D x i0).host.TT ↔ t.val ∈ Fm.TTn x := by
  rw [← Fm.TT_eq x i0, Finset.mem_image]
  constructor
  · intro h; exact ⟨t, h, rfl⟩
  · rintro ⟨s, hs, hst⟩
    rwa [← Formalism.HC.Frame.A.val_injective _ hst]

/- English proof (translation)
The claim follows from `(Fm.D x i0).R.toFrame.val_ofNat_of_lt (Lnk.TTn_lt Fm x i0 hn)`.
-/
theorem pf_cast_val {n : ℕ} (hn : n ∈ Fm.TTn x) : ((Fm.D x i0).R.ofNat n).val = n :=
  (Fm.D x i0).R.toFrame.val_ofNat_of_lt (Lnk.TTn_lt Fm x i0 hn)

/- English proof (translation)
Unfold `G.box`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `t`. Distinguish the cases in `h : t ∈ (Fm.D x i0).host.TT`. Rewrite using `[if_pos h]`.

Establish `h'` using `(pf_mem_TT t).1 h`. Unfold `aO Lnk.avOf`. Rewrite using `[dif_pos h', ← pf_winA_eq]`. Conclude with `(o ⟨_, h'⟩).1.2`. Rewrite using `[if_neg h]`.

Establish `h' : t.val ∉ Fm.TTn x` using `fun hh => h ((pf_mem_TT t).2 hh)`. Unfold `aO Lnk.avOf`. Rewrite using `[dif_neg h']`. Conclude with `Finset.mem_singleton_self _`.
-/
theorem pf_aO_mem (o : Lnk.Wt Fm x i0) : aO o ∈ G.box (Fm.D x i0) (G.winA (Fm.D x i0) (Fm.L x i0).sc) := by
  classical
  unfold G.box
  rw [Fintype.mem_piFinset]
  intro t
  by_cases h : t ∈ (Fm.D x i0).host.TT
  · rw [if_pos h]
    have h' := (pf_mem_TT t).1 h
    unfold aO Lnk.avOf
    rw [dif_pos h', ← pf_winA_eq]
    exact (o ⟨_, h'⟩).1.2
  · rw [if_neg h]
    have h' : t.val ∉ Fm.TTn x := fun hh => h ((pf_mem_TT t).2 hh)
    unfold aO Lnk.avOf
    rw [dif_neg h']
    exact Finset.mem_singleton_self _

/- English proof (translation)
Unfold `G.box`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `t`. Distinguish the cases in `h : t ∈ (Fm.D x i0).host.TT`. Rewrite using `[if_pos h]`.

Establish `h'` using `(pf_mem_TT t).1 h`. Unfold `bO Lnk.bvOf`. Rewrite using `[dif_pos h', ← pf_winB_eq hx]`. Conclude with `(o ⟨_, h'⟩).2.2`. Rewrite using `[if_neg h]`.

Establish `h' : t.val ∉ Fm.TTn x` using `fun hh => h ((pf_mem_TT t).2 hh)`. Unfold `bO Lnk.bvOf`. Rewrite using `[dif_neg h']`. Conclude with `Finset.mem_singleton_self _`.
-/
theorem pf_bO_mem (hx : Fm.x1 < x) (o : Lnk.Wt Fm x i0) :
    bO o ∈ G.box (Fm.D x i0) (G.winB (Fm.D x i0) Fm.GK (Fm.L x i0).sc) := by
  classical
  unfold G.box
  rw [Fintype.mem_piFinset]
  intro t
  by_cases h : t ∈ (Fm.D x i0).host.TT
  · rw [if_pos h]
    have h' := (pf_mem_TT t).1 h
    unfold bO Lnk.bvOf
    rw [dif_pos h', ← pf_winB_eq hx]
    exact (o ⟨_, h'⟩).2.2
  · rw [if_neg h]
    have h' : t.val ∉ Fm.TTn x := fun hh => h ((pf_mem_TT t).2 hh)
    unfold bO Lnk.bvOf
    rw [dif_neg h']
    exact Finset.mem_singleton_self _

/- English proof (translation)
Unfold `G.box at ha`. Rewrite `ha` using `[Fintype.mem_piFinset]`. Establish `h` using `ha ((Fm.D x i0).R.ofNat n)`. Rewrite `h` using `[if_pos ((pf_mem_TT _).2 (by rw [pf_cast_val hn]; exact hn))]`. Then use the resulting hypothesis.
-/
theorem pf_box_at {W : Finset ℤ} {a : G.HH (Fm.D x i0) → ℤ} (ha : a ∈ G.box (Fm.D x i0) W) {n : ℕ}
    (hn : n ∈ Fm.TTn x) : a ((Fm.D x i0).R.ofNat n) ∈ W := by
  classical
  unfold G.box at ha
  rw [Fintype.mem_piFinset] at ha
  have h := ha ((Fm.D x i0).R.ofNat n)
  rwa [if_pos ((pf_mem_TT _).2 (by rw [pf_cast_val hn]; exact hn))] at h

/- English proof (translation)
Unfold `G.box at ha`. Rewrite `ha` using `[Fintype.mem_piFinset]`. Establish `h` using `ha t`. Rewrite `h` using `[if_neg (fun hh => ht ((pf_mem_TT t).1 hh))]`. Conclude with `Finset.mem_singleton.1 h`.
-/
theorem pf_box_off {W : Finset ℤ} {a : G.HH (Fm.D x i0) → ℤ} (ha : a ∈ G.box (Fm.D x i0) W)
    {t : G.HH (Fm.D x i0)} (ht : t.val ∉ Fm.TTn x) : a t = 0 := by
  classical
  unfold G.box at ha
  rw [Fintype.mem_piFinset] at ha
  have h := ha t
  rw [if_neg (fun hh => ht ((pf_mem_TT t).1 hh))] at h
  exact Finset.mem_singleton.1 h

/- English proof (translation)
Rewrite using `[← Finset.sum_product']`. Use `Finset.sum_bij (fun o _ => (aO o, bO o)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `o _`. Conclude with `Finset.mem_product.2 ⟨pf_aO_mem o, pf_bO_mem hx o⟩`. Introduce `o _ o' _ h`.

Establish `h1 : aO o = aO o'` using `congrArg Prod.fst h`. Establish `h2 : bO o = bO o'` using `congrArg Prod.snd h`. Use function extensionality and compare the values at `τ`. Take `⟨n, hn⟩` from `τ`. Establish `e1` using `congrFun h1 ((Fm.D x i0).R.ofNat n)`.

Establish `e2` using `congrFun h2 ((Fm.D x i0).R.ofNat n)`. Unfold `aO Lnk.avOf at e1`. Unfold `bO Lnk.bvOf at e2`. Simplify using `only [pf_cast_val hn, dif_pos hn] at e1 e2`. Conclude with `Prod.ext (Subtype.ext e1) (Subtype.ext e2)`.

Introduce and unpack `⟨a, b⟩ hab`. Take `⟨ha, hb⟩` from `Finset.mem_product.1 hab`. Simplify using `only at ha hb`. Use `⟨fun τ => (⟨a ((Fm.D x i0).R.ofNat τ.1), by rw [pf_winA_eq]; exact pf_box_at ha τ.2⟩, ⟨b ((Fm.D x i0).R.ofNat τ.1), by rw [pf_winB_eq hx]; exact pf_box_at hb τ.2⟩), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `t dsimp only`. Unfold `aO Lnk.avOf`. Distinguish the cases in `h : t.val ∈ Fm.TTn x`. Rewrite using `[dif_pos h] show a ((Fm.D x i0).R.ofNat t.val) = a t`. Rewrite using `[(Fm.D x i0).R.toFrame.ofNat_val]`.

Rewrite using `[dif_neg h, pf_box_off ha h]`. Use function extensionality and compare the values at `t dsimp only`. Unfold `bO Lnk.bvOf`. Distinguish the cases in `h : t.val ∈ Fm.TTn x`. Rewrite using `[dif_pos h] show b ((Fm.D x i0).R.ofNat t.val) = b t`.

Rewrite using `[(Fm.D x i0).R.toFrame.ofNat_val]`. Rewrite using `[dif_neg h, pf_box_off hb h]`. Introduce `o _`. Both sides reduce to the same expression.
-/
theorem pf_sum_Wt (hx : Fm.x1 < x) (F : (G.HH (Fm.D x i0) → ℤ) → (G.HH (Fm.D x i0) → ℤ) → ℝ) :
    ∑ o : Lnk.Wt Fm x i0, F (aO o) (bO o) =
      ∑ a ∈ G.box (Fm.D x i0) (G.winA (Fm.D x i0) (Fm.L x i0).sc),
        ∑ b ∈ G.box (Fm.D x i0) (G.winB (Fm.D x i0) Fm.GK (Fm.L x i0).sc), F a b := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun o _ => (aO o, bO o)) ?_ ?_ ?_ ?_
  · intro o _
    exact Finset.mem_product.2 ⟨pf_aO_mem o, pf_bO_mem hx o⟩
  · intro o _ o' _ h
    have h1 : aO o = aO o' := congrArg Prod.fst h
    have h2 : bO o = bO o' := congrArg Prod.snd h
    funext τ
    obtain ⟨n, hn⟩ := τ
    have e1 := congrFun h1 ((Fm.D x i0).R.ofNat n)
    have e2 := congrFun h2 ((Fm.D x i0).R.ofNat n)
    unfold aO Lnk.avOf at e1
    unfold bO Lnk.bvOf at e2
    simp only [pf_cast_val hn, dif_pos hn] at e1 e2
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    simp only at ha hb
    refine ⟨fun τ => (⟨a ((Fm.D x i0).R.ofNat τ.1), by rw [pf_winA_eq]; exact pf_box_at ha τ.2⟩,
      ⟨b ((Fm.D x i0).R.ofNat τ.1), by rw [pf_winB_eq hx]; exact pf_box_at hb τ.2⟩), Finset.mem_univ _, ?_⟩
    refine Prod.ext ?_ ?_
    · funext t
      dsimp only
      unfold aO Lnk.avOf
      by_cases h : t.val ∈ Fm.TTn x
      · rw [dif_pos h]
        show a ((Fm.D x i0).R.ofNat t.val) = a t
        rw [(Fm.D x i0).R.toFrame.ofNat_val]
      · rw [dif_neg h, pf_box_off ha h]
    · funext t
      dsimp only
      unfold bO Lnk.bvOf
      by_cases h : t.val ∈ Fm.TTn x
      · rw [dif_pos h]
        show b ((Fm.D x i0).R.ofNat t.val) = b t
        rw [(Fm.D x i0).R.toFrame.ofNat_val]
      · rw [dif_neg h, pf_box_off hb h]
  · intro o _
    rfl

/- English proof (translation)
Establish `h` using `pf_sum_Wt (i0 := i0) hx (fun _ _ => (1 : ℝ))`. Simplify using `using h`.
-/
theorem pf_card_Wt (hx : Fm.x1 < x) :
    (Fintype.card (Lnk.Wt Fm x i0) : ℝ) =
      ((G.box (Fm.D x i0) (G.winA (Fm.D x i0) (Fm.L x i0).sc)).card : ℝ) *
        ((G.box (Fm.D x i0) (G.winB (Fm.D x i0) Fm.GK (Fm.L x i0).sc)).card : ℝ) := by
  have h := pf_sum_Wt (i0 := i0) hx (fun _ _ => (1 : ℝ))
  simpa using h

/- English proof (translation)
Establish `hne` using `Lnk.wt_nonempty (i0 := i0) hx`. Establish `hcard : (0 : ℝ) < (Fintype.card (Lnk.Wt Fm x i0) : ℝ)` using `by exact_mod_cast Fintype.card_pos`. Establish `hWA : (Fm.D x i0).host.TT.Nonempty → (G.winA (Fm.D x i0) (Fm.L x i0).sc).Nonempty`. Introduce and unpack `⟨t, ht⟩`. Conclude with `⟨(Fm.L x i0).aT ⟨t, ht⟩, Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr ((Fm.L x i0).aT_win _).1, Int.le_floor.mpr ((Fm.L x i0).aT_win _).2⟩⟩`.

Establish `hWB : (Fm.D x i0).host.TT.Nonempty → (G.winB (Fm.D x i0) Fm.GK (Fm.L x i0).sc).Nonempty`. Introduce and unpack `⟨t, ht⟩`. Rewrite using `[← pf_winB_eq hx]`. Conclude with `⟨(Fm.L x i0).bT ⟨t, ht⟩, Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr ((Fm.L x i0).bT_ge _), Int.le_floor.mpr (Fm.bT_le x hx i0 _)⟩⟩`. Rewrite using `[div_le_iff₀ hcard]`.

Establish `h1` using `pf_sum_Wt (i0 := i0) hx (fun a b => G.Sig (Fm.Gx x i0) Fm.GK a b p)`. Establish `h2` using `pf_sum_Sig_le (Fm.Gx x i0) Fm.GK hWA hWB h4 p hc`. Establish `h3 : ∑ o : Lnk.Wt Fm x i0, SigO p o = ∑ o : Lnk.Wt Fm x i0, G.Sig (Fm.Gx x i0) Fm.GK (aO o) (bO o) p` using `rfl`. Rewrite using `[h3, h1, pf_card_Wt hx]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mean_SigO (hx : Fm.x1 < x) (h4 : G.MeanKappaBound (Fm.Gx x i0) Fm.GK) (p : ℕ)
    (hc : G.Cand (Fm.D x i0) (Fm.L x i0) Fm.GK p) :
    (∑ o : Lnk.Wt Fm x i0, SigO p o) / (Fintype.card (Lnk.Wt Fm x i0) : ℝ) ≤
      ((Fm.D x i0).R.m : ℝ) * ((Fm.D x i0).host.TT.card : ℝ) * (Fm.L x i0).sc.x ^ (-12 : ℝ) := by
  have hne := Lnk.wt_nonempty (i0 := i0) hx
  have hcard : (0 : ℝ) < (Fintype.card (Lnk.Wt Fm x i0) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hWA : (Fm.D x i0).host.TT.Nonempty → (G.winA (Fm.D x i0) (Fm.L x i0).sc).Nonempty := by
    rintro ⟨t, ht⟩
    exact ⟨(Fm.L x i0).aT ⟨t, ht⟩, Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr ((Fm.L x i0).aT_win _).1, Int.le_floor.mpr ((Fm.L x i0).aT_win _).2⟩⟩
  have hWB : (Fm.D x i0).host.TT.Nonempty → (G.winB (Fm.D x i0) Fm.GK (Fm.L x i0).sc).Nonempty := by
    rintro ⟨t, ht⟩
    rw [← pf_winB_eq hx]
    exact ⟨(Fm.L x i0).bT ⟨t, ht⟩, Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr ((Fm.L x i0).bT_ge _), Int.le_floor.mpr (Fm.bT_le x hx i0 _)⟩⟩
  rw [div_le_iff₀ hcard]
  have h1 := pf_sum_Wt (i0 := i0) hx (fun a b => G.Sig (Fm.Gx x i0) Fm.GK a b p)
  have h2 := pf_sum_Sig_le (Fm.Gx x i0) Fm.GK hWA hWB h4 p hc
  have h3 : ∑ o : Lnk.Wt Fm x i0, SigO p o =
      ∑ o : Lnk.Wt Fm x i0, G.Sig (Fm.Gx x i0) Fm.GK (aO o) (bO o) p := rfl
  rw [h3, h1, pf_card_Wt hx]
  linarith

end FamilyMean

end Formalism.L2.GlobalTheoryTheory.Loss

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

section AtRecord

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ)

/- English proof (translation)
Use `⟨fun p hp => ?_, fun w _ _ => ⟨fun _ _ => rfl, rfl⟩, fun w hw hn => absurd hw hn⟩` and prove the remaining obligations. Use `show ∑ w ∈ (PsAt L).filter (fun w => w = p), Real.log (w : ℝ) = Real.log p`. Rewrite using `[Finset.filter_eq', if_pos hp, Finset.sum_singleton]`.
-/
theorem unitRule_at : UnitRule (ldAt X K C bo).W (ldAt X K C bo).below (ldAt X K C bo).l (PsAt L) (SizeData₂.lifts D)
    (ldAt X K C bo).gainW (ldAt X K C bo).tauW (ldAt X K C bo).gain (ldAt X K C bo).tau := by
  classical
  refine ⟨fun p hp => ?_, fun w _ _ => ⟨fun _ _ => rfl, rfl⟩, fun w hw hn => absurd hw hn⟩
  show ∑ w ∈ (PsAt L).filter (fun w => w = p), Real.log (w : ℝ) = Real.log p
  rw [Finset.filter_eq', if_pos hp, Finset.sum_singleton]

/- English proof (translation)
Take `⟨s1, s2, s3, s4, s5, s6, eX, -, -, -⟩` from `side_at X K Cr C bo H P tie hbo hLa hp0`. Use `⟨unitRule_at X K C bo, s1, s2, s3, fun p hp h => ?_, fun p hp h => ?_, fun p hp h => loss_bound_at X K Cr C bo H (T_not_inert D) (fun j hj t p hp hI => ask_at X K Cr C bo H j hj t p hp hI) hG p hp h, fun p hp h => ?_, fun p hp _ => s4 p hp, fun p hp _ => s5 p hp, s6⟩` and prove the remaining obligations. Rewrite using `[eX]`. Conclude with `served_le X K Cr H (T_not_inert D) p hp h`. Rewrite using `[eX]`.

Conclude with `high_gt X K p h`. Take `⟨a1, a2⟩` from `nonserved_zero X K Cr H (T_not_inert D) p hp h`. Conclude with `⟨fun j _ => a1 j, a2⟩`.
-/
theorem lossHyp_at (H : PtH X K Cr) (hG : LinkG_at X K C bo) (P : Par) (tie : ParTie P L K C bo Cr) (hbo : 0 ≤ bo)
    (hLa : 0 ≤ L.LaG) (hp0 : L.sc.p0 D.R.k ≤ L.sc.X') :
    ParametersHyp P (PsAt L) (SizeData₂.lifts D) (TTv D) (ldAt X K C bo) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, eX, -, -, -⟩ := side_at X K Cr C bo H P tie hbo hLa hp0
  refine ⟨unitRule_at X K C bo, s1, s2, s3, fun p hp h => ?_, fun p hp h => ?_, fun p hp h => loss_bound_at X K Cr C bo H (T_not_inert D) (fun j hj t p hp hI => ask_at X K Cr C bo H j hj t p hp hI) hG p hp h,
    fun p hp h => ?_, fun p hp _ => s4 p hp, fun p hp _ => s5 p hp, s6⟩
  · rw [eX]; exact served_le X K Cr H (T_not_inert D) p hp h
  · rw [eX]; exact high_gt X K p h
  · obtain ⟨a1, a2⟩ := nonserved_zero X K Cr H (T_not_inert D) p hp h
    exact ⟨fun j _ => a1 j, a2⟩

/- English proof (translation)
Conclude with `(Finset.mem_filter.mp hp).2`.
-/
theorem mem_PsAt {p : ℕ} (hp : p ∈ PsAt L) : p.Prime ∧ InertK D p := by
  classical
  exact (Finset.mem_filter.mp hp).2

/- English proof (translation)
Establish `hcl : D.host.cls 2 = PrimeClass.ram2` using `primeClass_two D.host.toHostRaw`. Apply the tactic sequence `rintro (h | h) <;> rw [hcl] at h <;> cases h`.
-/
theorem two_not_inert (D : D7) : ¬ InertK D 2 := by
  have hcl : D.host.cls 2 = PrimeClass.ram2 := primeClass_two D.host.toHostRaw
  rintro (h | h) <;> rw [hcl] at h <;> cases h

/- English proof (translation)
Unfold `sAt`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨fun h => h.2, fun h => ⟨Nat.lt_ceil.mpr h.2.1, h⟩⟩`.
-/
theorem mem_sAt {p : ℕ} : p ∈ sAt L K ↔ G.Cand D L K p := by
  classical
  unfold sAt
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_ceil.mpr h.2.1, h⟩⟩

/- English proof (translation)
Unfold `ChBad_at at h ⊢`. Use `le_trans h ?_` and prove the remaining obligations. Establish `hx : 0 < L.sc.x` using `lt_trans one_pos L.sc.one_lt_alt`. Establish `hS : 0 ≤ ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p` using `Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)`. Establish `hd : 0 ≤ L.sc.delta1` using `Real.rpow_nonneg hx.le _`.

Establish `h2 : 0 ≤ L.sc.x ^ (-2 : ℝ)` using `Real.rpow_nonneg hx.le _`. Establish `hn : (0 : ℝ) ≤ D.R.n` using `Nat.cast_nonneg _`. Establish `hm : Cb ≤ max Cb 0` using `le_max_left _ _`. Establish `: Cb * (L.sc.x ^ (-2 : ℝ) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p) ≤ max Cb 0 * (L.sc.x ^ (-2 : ℝ) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p)` using `mul_le_mul_of_nonneg_right hm (by positivity)`. Use polynomial arithmetic with `[this]`.
-/
theorem chBad_mono {Cb : ℝ} (h : ChBad_at X Cb) : ChBad_at X (max Cb 0) := by
  unfold ChBad_at at h ⊢
  refine le_trans h ?_
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hS : 0 ≤ ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hd : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx.le _
  have h2 : 0 ≤ L.sc.x ^ (-2 : ℝ) := Real.rpow_nonneg hx.le _
  have hn : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  have hm : Cb ≤ max Cb 0 := le_max_left _ _
  have : Cb * (L.sc.x ^ (-2 : ℝ) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p) ≤
      max Cb 0 * (L.sc.x ^ (-2 : ℝ) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p) :=
    mul_le_mul_of_nonneg_right hm (by positivity)
  nlinarith [this]

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Fm.fills x hx i, Fm.supp_sat x hx i, Fm.drop_iff x hx i, Fm.GK_nonneg, (Fm.ex x hx i).kapI_def, Fm.one_le_Cr, Lnk.numN_at (Fm.params x hx i) (Fm.sizes x hx i) (by rw [Fm.L_x x i hx]; exact h3)⟩`.
-/
theorem ptH {x : ℝ} (hx : Fm.x1 < x) (h3 : 3 ≤ x) (i : Fm.Ix x) : PtH (Fm.Gx x i) Fm.GK Fm.Cr :=
  ⟨Fm.fills x hx i, Fm.supp_sat x hx i, Fm.drop_iff x hx i, Fm.GK_nonneg, (Fm.ex x hx i).kapI_def, Fm.one_le_Cr,
    Lnk.numN_at (Fm.params x hx i) (Fm.sizes x hx i) (by rw [Fm.L_x x i hx]; exact h3)⟩

/- English proof (translation)
Introduce `Cord hCord`. Take `⟨xT, hTT⟩` from `hTT`. Take `⟨xB, hBad⟩` from `hBad`. Take `⟨C, xG, δ, hδ, hG⟩` from `hG`. Take `⟨xA, hAsk⟩` from `Lnk.askIsF Fm`.

Take `⟨e, K, x0, hW⟩` from `windows_ev Fm C Cb Cord hCord δ hδ`. Use `⟨e, K, max (max x0 xT) (max xB (max xG xA)), fun x hxx hwin => ?_⟩` and prove the remaining obligations. Establish `e0 : x ≥ x0` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxx`. Establish `eT : x ≥ xT` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxx`. Establish `eB : x ≥ xB` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx`.

Establish `eG : x ≥ xG` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxx`. Establish `eA : x ≥ xA` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hxx`. Take `⟨hx, h3, hW⟩` from `hW x e0`. Take `⟨i0⟩` from `Fm.Ix_win x hwin`. Take `⟨hW, hp0⟩` from `hW i0`.

Use `set bo : ℝ := (Fm.L x i0).sc.b ^ δ x with hbo`. Establish `hbo0 : 0 ≤ bo` using `Real.rpow_nonneg (Real.exp_pos _).le _`. Use `set P : Par := par Fm x i0 C bo Cb Cord with hP`. Establish `hGi : ∀ i : Fm.Ix x, LinkG_at (Fm.Gx x i) Fm.GK C bo` using `fun i => by`. Use `hG x eG i` as an intermediate fact.

Rewrite `this` using `[Lnk.sc_eq Fm hx i i0]`. Then use the resulting hypothesis. Establish `hH : ∀ i : Fm.Ix x, PtH (Fm.Gx x i) Fm.GK Fm.Cr` using `fun i => ptH Fm hx h3 i`. Establish `hLa : ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).LaG` using `fun i => by`. Establish `h1` using `(Fm.sizes x hx i).2.2.2.2.2.2.2.2.1.1`. Conclude with `le_trans (Real.rpow_nonneg (lt_trans one_pos (Fm.L x i).sc.one_lt_alt).le _) h1`.

Establish `hp0i : ∀ i : Fm.Ix x, (Fm.L x i).sc.p0 (Fm.D x i).R.k ≤ (Fm.L x i).sc.X'` using `fun i => by`. Rewrite using `[Lnk.sc_eq Fm hx i i0, Fm.R_eq x i i0]`. Conclude with `hp0`. Establish `hside` using `fun i : Fm.Ix x => side_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) P (parTie hx i C bo Cb Cord) hbo0 (hLa i) (hp0i i)`. Take `⟨-, -, -, -, -, -, -, ea0, eX0, eθ0⟩` from `hside i0`.

Establish `hρ0 : 0 ≤ G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc` using `hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hXp : 0 < (Fm.L x i0).sc.X'` using `Real.exp_pos _`. Establish `hJ : (SizeData₂.lifts (Fm.D x i0)).card = (Fm.D x i0).R.m`. Unfold `SizeData₂.lifts`. Rewrite using `[Nat.card_Icc]`.

Use linear arithmetic over natural numbers and integers. Establish `hTc : ∀ i : Fm.Ix x, (Fm.TTn x).card = (Fm.D x i).host.TT.card` using `fun i => by`. Rewrite using `[← Fm.TT_eq x i, Finset.card_image_of_injective _ (Formalism.HC.Frame.A.val_injective _)]`. Use `⟨i0, P, ℕ, ℕ, ℕ, PsAt (Fm.L x i0), sAt (Fm.L x i0) Fm.GK, largeOrderResiduePrimes (Fm.L x i0), SizeData₂.lifts (Fm.D x i0), Fm.TTn x, badAt (Fm.Gx x i0), SigO, fun i p => G.ioP (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p, fun i => ldAt (Fm.Gx x i) Fm.GK C bo, ⟨Fm.L_x …` and prove the remaining obligations. Rewrite using `[← Finset.card_pos, hTc i0]`.

Establish `h1` using `(hTT x eT i0).1`. Establish `hx0 : 0 < (Fm.L x i0).sc.x` using `lt_trans one_pos (Fm.L x i0).sc.one_lt_alt`. Establish `h2 : 0 < (Fm.L x i0).sc.delta1 * (Fm.D x i0).R.n / 2`. Establish `: 0 < (Fm.L x i0).sc.delta1` using `Real.rpow_pos_of_pos hx0 _`. Establish `h4 : (0 : ℝ) < (Fm.D x i0).R.n` using `lt_of_lt_of_le one_pos (Lnk.one_le_n _)`.

Check the signs of the components of the expression. Conclude with `lt_of_lt_of_le h2 h1` after adjusting the coercions. Introduce `p hp`. Take `⟨h1, h2⟩` from `mem_PsAt hp`. Conclude with `⟨h1, fun h => two_not_inert _ (h ▸ h2)⟩`.

Introduce `p hp`. Establish `hc` using `(mem_sAt Fm.GK).mp hp`. Use `⟨hc.1, le_trans hc.2.1.le ?_⟩` and prove the remaining obligations. Use `show (Fm.L x i0).sc.X' ≤ (Fm.L x i0).sc.X' * (1 + Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc)`. Establish `: 0 ≤ Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc` using `mul_nonneg (le_trans zero_le_one Fm.one_le_Cr) hρ0`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `p _ o`. Conclude with `Lnk.Sig_nonneg (Fm.Gx x i0) Fm.GK Fm.GK_nonneg (Fm.ex x hx i0).kapI_def _ _ p`. Introduce `p hp`. Conclude with `mean_SigO hx (hGi i0).2.2.2.2 p ((mem_sAt Fm.GK).mp hp)`.

Introduce `p hp`. Take `⟨h1, h2⟩` from `Finset.mem_filter.mp hp`. Rewrite using `[eX0]`. Conclude with `⟨h2.1, (Nat.lt_ceil.mp (Finset.mem_range.mp h1)).le⟩`. Establish `h` using `Lnk.tops_clause (Fm.Gx x i0) (max Cb 0) ((Fm.D x i0).R.m : ℝ) (le_max_right _ _) (Nat.cast_nonneg _) (hTT x eT i0) (chBad_mono _ (hBad x eB i0))`.

Rewrite using `[hJ, ea0, hTc i0]`. Simplify using `only [bad_card]`. Conclude with `h`. Introduce `o i hcar`. Establish `eP` using `PsAt_eq (i0 := i0) hx i`.

Establish `eS` using `sAt_eq (i0 := i0) hx i`. Establish `eL` using `lifts_eq (i0 := i0) i`. Establish `eC` using `large_order_primes_eq_filter (i0 := i0) hx i`. Establish `eR` using `Fm.R_eq x i i0`. Establish `tie` using `parTie (i0 := i0) hx i C bo Cb Cord`.

Take `⟨-, -, -, -, -, -, -, ea, eX, eθ⟩` from `hside i`. Establish `em : (Fm.D x i).R.m = (Fm.D x i0).R.m` using `congrArg Ranks.m eR`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, hTc i, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p _`. Establish `h` using `Lnk.ioP_le (Fm.Gx x i) Fm.GK p ((hGi i).2.1 p) (Lnk.Sig_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx i).kapI_def _ _ p)`.

Rewrite `h` using `[Sig_eq hx i o hcar p]`. Rewrite using `[hJ, hTc i, ea, ← em]`. Conclude with `h`. Establish `h` using `lossHyp_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) (hGi i) P tie hbo0 (hLa i) (hp0i i)`. Rewrite `h` using `[eP, eL]`.

Establish `e2 : TTv (Fm.D x i) = Fm.TTn x` using `Fm.TT_eq x i`. Rewrite `h` using `[e2]`. Then use the resulting hypothesis. Establish `h` using `firstHyp_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) (T_not_inert _) P tie`. Rewrite `h` using `[eP]`. Then use the resulting hypothesis. Introduce `p _ h`.

Take `⟨h1, h2⟩` from `second_spec (Fm.Gx x i) Fm.GK p h`. Rewrite using `[← eS, eθ, ← Sig_eq hx i o hcar p]`. Conclude with `⟨(mem_sAt Fm.GK).mpr h1, h2⟩`. Introduce `p hp h n hn`. Rewrite `hp` using `[← eP]`.

Establish `e2 : Fm.TTn x = TTv (Fm.D x i)` using `(Fm.TT_eq x i).symm`. Rewrite `hn` using `[e2]`. Establish `hn' : n ∈ TTv (Fm.D x i) ∧ n ∉ (ldAt (Fm.Gx x i) Fm.GK C bo).TTp p`. Simplify `hn` using `only [Finset.mem_sdiff]`. Take `⟨hn1, hn2⟩` from `hn'`.

Take `⟨h1, h2⟩` from `unserved_bad (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) (T_not_inert _) p hp h n (Finset.mem_sdiff.mpr ⟨hn1, hn2⟩)`. Rewrite using `[← eC]`. Conclude with `⟨h1, (badAt_iff hx i p n).mp h2⟩`. Rewrite using `[hJ, em]`. Rewrite using `[← eL]`.

Conclude with `Ga_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i)`. Rewrite using `[← eS]`. Conclude with `IO_at (Fm.Gx x i) Fm.GK Fm.Cr (hH i)`. Establish `h` using `ASK_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i)`. Establish `e2 : TTv (Fm.D x i) = Fm.TTn x` using `Fm.TT_eq x i`.

Rewrite `h` using `[eP, eL, e2, ← tie.d]`. Rewrite using `[h]`. Conclude with `hAsk x eA i`.
-/
theorem loss_points_of_choices (Cb : ℝ) (hTT : ChosenTT Fm) (hBad : ChosenBad Fm Cb) (hG : LinkG Fm) : Lnk.StatementsAtPointsLargeScales Fm := by
  classical
  intro Cord hCord
  obtain ⟨xT, hTT⟩ := hTT
  obtain ⟨xB, hBad⟩ := hBad
  obtain ⟨C, xG, δ, hδ, hG⟩ := hG
  obtain ⟨xA, hAsk⟩ := Lnk.askIsF Fm
  obtain ⟨e, K, x0, hW⟩ := windows_ev Fm C Cb Cord hCord δ hδ
  refine ⟨e, K, max (max x0 xT) (max xB (max xG xA)), fun x hxx hwin => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxx
  have eT : x ≥ xT := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxx
  have eB : x ≥ xB := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx
  have eG : x ≥ xG := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxx
  have eA : x ≥ xA := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hxx
  obtain ⟨hx, h3, hW⟩ := hW x e0
  obtain ⟨i0⟩ := Fm.Ix_win x hwin
  obtain ⟨hW, hp0⟩ := hW i0
  set bo : ℝ := (Fm.L x i0).sc.b ^ δ x with hbo
  have hbo0 : 0 ≤ bo := Real.rpow_nonneg (Real.exp_pos _).le _
  set P : Par := par Fm x i0 C bo Cb Cord with hP
  have hGi : ∀ i : Fm.Ix x, LinkG_at (Fm.Gx x i) Fm.GK C bo := fun i => by
    have := hG x eG i
    rwa [Lnk.sc_eq Fm hx i i0] at this
  have hH : ∀ i : Fm.Ix x, PtH (Fm.Gx x i) Fm.GK Fm.Cr := fun i => ptH Fm hx h3 i
  have hLa : ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).LaG := fun i => by
    have h1 := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.1.1
    exact le_trans (Real.rpow_nonneg (lt_trans one_pos (Fm.L x i).sc.one_lt_alt).le _) h1
  have hp0i : ∀ i : Fm.Ix x, (Fm.L x i).sc.p0 (Fm.D x i).R.k ≤ (Fm.L x i).sc.X' := fun i => by
    rw [Lnk.sc_eq Fm hx i i0, Fm.R_eq x i i0]; exact hp0
  have hside := fun i : Fm.Ix x => side_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) P (parTie hx i C bo Cb Cord) hbo0 (hLa i) (hp0i i)
  obtain ⟨-, -, -, -, -, -, -, ea0, eX0, eθ0⟩ := hside i0
  have hρ0 : 0 ≤ G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hXp : 0 < (Fm.L x i0).sc.X' := Real.exp_pos _
  have hJ : (SizeData₂.lifts (Fm.D x i0)).card = (Fm.D x i0).R.m := by
    unfold SizeData₂.lifts; rw [Nat.card_Icc]; omega
  have hTc : ∀ i : Fm.Ix x, (Fm.TTn x).card = (Fm.D x i).host.TT.card := fun i => by
    rw [← Fm.TT_eq x i, Finset.card_image_of_injective _ (Formalism.HC.Frame.A.val_injective _)]
  refine ⟨i0, P, ℕ, ℕ, ℕ, PsAt (Fm.L x i0), sAt (Fm.L x i0) Fm.GK, largeOrderResiduePrimes (Fm.L x i0), SizeData₂.lifts (Fm.D x i0), Fm.TTn x,
    badAt (Fm.Gx x i0), SigO, fun i p => G.ioP (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p,
    fun i => ldAt (Fm.Gx x i) Fm.GK C bo, ⟨Fm.L_x x i0 hx, Fm.L_eps x i0, rfl, hW⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← Finset.card_pos, hTc i0]
    have h1 := (hTT x eT i0).1
    have hx0 : 0 < (Fm.L x i0).sc.x := lt_trans one_pos (Fm.L x i0).sc.one_lt_alt
    have h2 : 0 < (Fm.L x i0).sc.delta1 * (Fm.D x i0).R.n / 2 := by
      have : 0 < (Fm.L x i0).sc.delta1 := Real.rpow_pos_of_pos hx0 _
      have h4 : (0 : ℝ) < (Fm.D x i0).R.n := lt_of_lt_of_le one_pos (Lnk.one_le_n _)
      positivity
    exact_mod_cast lt_of_lt_of_le h2 h1
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_PsAt hp
    exact ⟨h1, fun h => two_not_inert _ (h ▸ h2)⟩
  · intro p hp
    have hc := (mem_sAt Fm.GK).mp hp
    refine ⟨hc.1, le_trans hc.2.1.le ?_⟩
    show (Fm.L x i0).sc.X' ≤ (Fm.L x i0).sc.X' * (1 + Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc)
    have : 0 ≤ Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc :=
      mul_nonneg (le_trans zero_le_one Fm.one_le_Cr) hρ0
    nlinarith
  · intro p _ o
    exact Lnk.Sig_nonneg (Fm.Gx x i0) Fm.GK Fm.GK_nonneg (Fm.ex x hx i0).kapI_def _ _ p
  · intro p hp
    exact mean_SigO hx (hGi i0).2.2.2.2 p ((mem_sAt Fm.GK).mp hp)
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    rw [eX0]
    exact ⟨h2.1, (Nat.lt_ceil.mp (Finset.mem_range.mp h1)).le⟩
  · have h := Lnk.tops_clause (Fm.Gx x i0) (max Cb 0) ((Fm.D x i0).R.m : ℝ) (le_max_right _ _) (Nat.cast_nonneg _)
      (hTT x eT i0) (chBad_mono _ (hBad x eB i0))
    rw [hJ, ea0, hTc i0]
    simp only [bad_card]
    exact h
  · intro o i hcar
    have eP := PsAt_eq (i0 := i0) hx i
    have eS := sAt_eq (i0 := i0) hx i
    have eL := lifts_eq (i0 := i0) i
    have eC := large_order_primes_eq_filter (i0 := i0) hx i
    have eR := Fm.R_eq x i i0
    have tie := parTie (i0 := i0) hx i C bo Cb Cord
    obtain ⟨-, -, -, -, -, -, -, ea, eX, eθ⟩ := hside i
    have em : (Fm.D x i).R.m = (Fm.D x i0).R.m := congrArg Ranks.m eR
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hTc i, ?_, ?_, ?_⟩
    · intro p _
      have h := Lnk.ioP_le (Fm.Gx x i) Fm.GK p ((hGi i).2.1 p)
        (Lnk.Sig_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx i).kapI_def _ _ p)
      rw [Sig_eq hx i o hcar p] at h
      rw [hJ, hTc i, ea, ← em]
      exact h
    · have h := lossHyp_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) (hGi i) P tie hbo0 (hLa i) (hp0i i)
      rw [eP, eL] at h
      have e2 : TTv (Fm.D x i) = Fm.TTn x := Fm.TT_eq x i
      rwa [e2] at h
    · have h := firstHyp_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) (T_not_inert _) P tie
      rwa [eP] at h
    · intro p _ h
      obtain ⟨h1, h2⟩ := second_spec (Fm.Gx x i) Fm.GK p h
      rw [← eS, eθ, ← Sig_eq hx i o hcar p]
      exact ⟨(mem_sAt Fm.GK).mpr h1, h2⟩
    · intro p hp h n hn
      rw [← eP] at hp
      have e2 : Fm.TTn x = TTv (Fm.D x i) := (Fm.TT_eq x i).symm
      rw [e2] at hn
      have hn' : n ∈ TTv (Fm.D x i) ∧ n ∉ (ldAt (Fm.Gx x i) Fm.GK C bo).TTp p := by
        simpa only [Finset.mem_sdiff] using hn
      obtain ⟨hn1, hn2⟩ := hn'
      obtain ⟨h1, h2⟩ := unserved_bad (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i) (T_not_inert _) p hp h n (Finset.mem_sdiff.mpr ⟨hn1, hn2⟩)
      rw [← eC]
      exact ⟨h1, (badAt_iff hx i p n).mp h2⟩
    · rw [hJ, em]
    · rw [← eL]; exact Ga_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i)
    · rw [← eS]; exact IO_at (Fm.Gx x i) Fm.GK Fm.Cr (hH i)
    · have h := ASK_at (Fm.Gx x i) Fm.GK Fm.Cr C bo (hH i)
      have e2 : TTv (Fm.D x i) = Fm.TTn x := Fm.TT_eq x i
      rw [eP, eL, e2, ← tie.d] at h
      rw [h]
      exact hAsk x eA i

/- English proof (translation)
Introduce `_ Fm Cb h1 h2 h3 hc` and use `Lnk.estimates_of_points_family Fm hc (loss_points_of_choices Fm Cb h1 h2 h3)`.
-/
theorem stCore : StCore := fun _ Fm Cb h1 h2 h3 hc => Lnk.estimates_of_points_family Fm hc (loss_points_of_choices Fm Cb h1 h2 h3)

/- English proof (translation)
Introduce `_ Fm Cb h1 h2 h3 hc` and use `Lnk.lossF_of_core Fm (stCore _ Fm Cb h1 h2 h3 hc)`.
-/
theorem stLoss : StLoss := fun _ Fm Cb h1 h2 h3 hc => Lnk.lossF_of_core Fm (stCore _ Fm Cb h1 h2 h3 hc)

end Family

section Conclusion5₂

open Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.characterSumData

variable {eps : ℝ} (Fm : FamP eps)

/- English proof (translation)
Use `⟨Finset.univ.filter (fun h => hval D.R.toFrame h ∈ D.host.TT.image Formalism.HC.Frame.A.val), fun h => if hh : ∃ t : D.host.TT, hval D.R.toFrame h = (t : D.R.A).val then (L.aT hh.choose : ℝ) else 0, fun j g => if hh : ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = m …` and prove the remaining obligations. Introduce `t h hh`. Establish `hex : ∃ t : D.host.TT, hval D.R.toFrame h = (t : D.R.A).val` using `⟨t, hh⟩`. Establish `hc : hex.choose = t` using `Subtype.ext (Formalism.HC.Frame.A.val_injective _ (hex.choose_spec.symm.trans hh))`. Simplify using `only [dif_pos hex, hc]`.

Introduce `j g τ hh`. Establish `hex : ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode D.R.toFrame g` using `⟨τ, hh⟩`. Establish `hc : hex.choose = τ` using `D.eTau.injective (Subtype.ext (Lnk.gcode_injective _ (hex.choose_spec.trans hh.symm)))`. Simplify using `only [dif_pos hex, hc]`.
-/
theorem reads_nonempty {D : D7} (L : SizeData₂ D) :
    ∃ (TT : Finset (D.R.A)) (a : D.R.A → ℝ) (w : Fin D.R.m → E0 × D.R.A → ℝ),
      Lnk.Reads L D.R.toFrame D.R.m TT a w := by
  classical
  refine ⟨Finset.univ.filter (fun h => hval D.R.toFrame h ∈ D.host.TT.image Formalism.HC.Frame.A.val),
    fun h => if hh : ∃ t : D.host.TT, hval D.R.toFrame h = (t : D.R.A).val then (L.aT hh.choose : ℝ) else 0,
    fun j g => if hh : ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode D.R.toFrame g
      then wj D (j.val + 1) hh.choose else 0, rfl, rfl, fun h => by simp, ?_, ?_⟩
  · intro t h hh
    have hex : ∃ t : D.host.TT, hval D.R.toFrame h = (t : D.R.A).val := ⟨t, hh⟩
    have hc : hex.choose = t :=
      Subtype.ext (Formalism.HC.Frame.A.val_injective _ (hex.choose_spec.symm.trans hh))
    simp only [dif_pos hex, hc]
  · intro j g τ hh
    have hex : ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode D.R.toFrame g := ⟨τ, hh⟩
    have hc : hex.choose = τ :=
      D.eTau.injective (Subtype.ext (Lnk.gcode_injective _ (hex.choose_spec.trans hh.symm)))
    simp only [dif_pos hex, hc]

/- English proof (translation)
Take `⟨C, x0, -, h⟩` from `h`. Take `⟨xA, hAsk⟩` from `Lnk.askIsF Fm`. Use `⟨C, max x0 xA, fun x hx hwin => ?_⟩` and prove the remaining obligations. Take `⟨i0, av, bv, hadm, hl⟩` from `h x (le_trans (le_max_left _ _) hx) hwin`. Use `⟨i0, av, bv, hadm, fun i u0 hr => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hl i hr.2`. Take `⟨TT, a, w, hrd⟩` from `reads_nonempty (Fm.L x i)`. Take `⟨M, hM⟩` from `(Finset.univ.image (fun z : Fin (Fm.D x i).R.m × (Fm.D x i).R.A × (E0 × (Fm.D x i).R.A) => a z.2.1 / w z.1 z.2.2)).exists_le`. Establish `hcut : ∀ j t ρ, t ∈ TT → InPhi ρ → a t / w j ρ ≤ (⌈M⌉₊ : ℕ)` using `fun j t ρ _ _ => le_trans (hM _ (Finset.mem_image.mpr ⟨(j, t, ρ), Finset.mem_univ _, rfl⟩)) (Nat.le_ceil M)`. Establish `h3` using `h2 _ _ _ ⌈M⌉₊ TT a w hrd HEq.rfl hcut`.

Rewrite `h3` using `[hAsk x (le_trans (le_max_right _ _) hx) i _ _ _ ⌈M⌉₊ TT a w hrd HEq.rfl hcut]`. Rewrite `h1`, `h3` using `[Fm.L_eps x i]`. Conclude with `⟨h3, h1⟩`.
-/
theorem slope_loss_lemma_of_losses (eL : ℝ) (h : Lnk.LossF Fm eL) : LocalQuadraticParts.SlopeLossFamily Fm eL := by
  classical
  obtain ⟨C, x0, -, h⟩ := h
  obtain ⟨xA, hAsk⟩ := Lnk.askIsF Fm
  refine ⟨C, max x0 xA, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, hadm, hl⟩ := h x (le_trans (le_max_left _ _) hx) hwin
  refine ⟨i0, av, bv, hadm, fun i u0 hr => ?_⟩
  obtain ⟨h1, h2⟩ := hl i hr.2
  obtain ⟨TT, a, w, hrd⟩ := reads_nonempty (Fm.L x i)
  obtain ⟨M, hM⟩ := (Finset.univ.image (fun z : Fin (Fm.D x i).R.m × (Fm.D x i).R.A × (E0 × (Fm.D x i).R.A) =>
    a z.2.1 / w z.1 z.2.2)).exists_le
  have hcut : ∀ j t ρ, t ∈ TT → InPhi ρ → a t / w j ρ ≤ (⌈M⌉₊ : ℕ) := fun j t ρ _ _ =>
    le_trans (hM _ (Finset.mem_image.mpr ⟨(j, t, ρ), Finset.mem_univ _, rfl⟩)) (Nat.le_ceil M)
  have h3 := h2 _ _ _ ⌈M⌉₊ TT a w hrd HEq.rfl hcut
  rw [hAsk x (le_trans (le_max_right _ _) hx) i _ _ _ ⌈M⌉₊ TT a w hrd HEq.rfl hcut] at h3
  rw [Fm.L_eps x i] at h1 h3
  exact ⟨h3, h1⟩

/- English proof (translation)
Introduce `_ Fm Cb eL heL h1 h2 h3 hc` and use `slope_loss_lemma_of_losses Fm eL (Lnk.lossF_mono Fm heL (stLoss _ Fm Cb h1 h2 h3 hc))`.
-/
theorem slope_loss : SlopeLoss := fun _ Fm Cb eL heL h1 h2 h3 hc =>
  slope_loss_lemma_of_losses Fm eL (Lnk.lossF_mono Fm heL (stLoss _ Fm Cb h1 h2 h3 hc))

/- English proof (translation)
The claim follows from `slope_loss _ Fm Cb eL heL h1 h2 h3 hc`.
-/
theorem slope_loss_lemma_family (Cb eL : ℝ) (heL : 0 ≤ eL) (h1 : ChosenTT Fm) (h2 : ChosenBad Fm Cb) (h3 : LinkG Fm)
    (hc : Fm.CoverAll) : LocalQuadraticParts.SlopeLossFamily Fm eL :=
  slope_loss _ Fm Cb eL heL h1 h2 h3 hc

end Conclusion5₂

end Formalism.L2.GlobalTheoryTheory.Loss

end
