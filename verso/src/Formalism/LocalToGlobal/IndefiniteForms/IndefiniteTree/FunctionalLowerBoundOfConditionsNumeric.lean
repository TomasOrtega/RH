import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.GridSquaresIndexEstimate
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlobIncl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw meanLog matLat)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef htMap)

noncomputable section

namespace Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure FunData (K : Type) [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs) where

  n : ℕ

  X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ

  M : Submodule (𝓞 K) (Fin n → K)

  vmu : ∀ t : Bs.Tup, Matrix (Fin n) (Fin (Df.nV t)) K

  Tf : Finset (Pl K)

  dF : Pl K → ℤ

  m : ℕ

  rq : Bs.Tup → Fin m × Fin m → K

  dl : Pl K → ℝ

  Sd : Finset ℕ

  Se : Finset ℕ

  N0 : Fin m × Fin m → ℤ → ℕ → ℝ

  zA : Fin m × Fin m → K

  zA' : Fin m × Fin m → K

  zT : Fin m × Fin m → ℤ → K

  zTd : Fin m × Fin m → Bool → ℤ → K

  gT : Fin m × Fin m → ℤ → Pl K → ℤ

  ch : Pl K → Bool

  dd : Fin m × Fin m → ℕ

  hd : Fin m × Fin m → ℕ

  yy : Fin m × Fin m → ℕ

  Sq : Type

  S0 : Finset Sq

  sv0 : Sq

  cc : Sq → ℕ

  qq : Sq → ℕ

  f : ℕ

  k : ℕ

  tt : ℕ

  cl : ℕ → ℕ → ℤ

  g1 : ℕ

  g2 : ℕ

  pd : ℕ

  pd' : ℕ

  dE : ℤ

  Bw : ℝ

namespace FunData

variable {Bs : DefBase K} {Df : DefSide Bs} (O : FunData K Df)

def r : ℝ := (O.k : ℝ) + O.m - 1

def nr : ℕ := O.k + O.m

def s : ℕ := O.k + O.m + 5

def N : ℕ := O.k + O.m * (O.tt + O.s + 1)

def np : ℝ := (O.r + 1) + O.m * (O.r + 5)

def Lc : ℕ := (Finset.range O.f).sup fun τ => (O.cl τ 2 - O.cl τ O.k).toNat

def ga (C : ℝ) : ℕ :=
  max (max ⌈C * (O.N : ℝ) ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊
    (2 * O.N ^ 3 + 2 * O.s + 3)) ⌈48 * (O.nr : ℝ) ^ 2 * Real.sqrt (O.m : ℝ)⌉₊

def Rp (C : ℝ) : ℝ := ((O.m : ℝ) + 1) * ((O.ga C : ℝ) + 1) + O.Lc + O.np

def EMM (C : ℝ) : ℝ := 4 * (O.f : ℝ) * O.np * O.Rp C * Real.log (O.np * O.Rp C)

def PPF (C b : ℝ) : ℝ :=
  C * (O.f : ℝ) ^ 2 * (O.nr : ℝ) ^ 6 *
    Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|)

open Classical in

def ee (C b : ℝ) (q : O.Sq) : ℕ :=
  if q = O.sv0 then ⌊O.PPF C b / Real.log (O.qq O.sv0)⌋₊ + 1 else 2

def Sig0 (C b : ℝ) : ℝ := ∑ q ∈ O.S0, (O.ee C b q : ℝ) * Real.log (O.qq q)

def cS : ℝ := ∑ q ∈ O.S0, (O.cc q : ℝ) * Real.log (O.qq q)

def bFP (C b : ℝ) : ℝ :=
  C * O.f * b * O.N * O.m * (O.m * Real.log b + O.m * O.Sig0 C b) +
    C * O.f * (O.m : ℝ) ^ 2 * (O.N : ℝ) ^ 2 * (Real.log b + O.Sig0 C b) * b

def bIPa (C b : ℝ) : ℝ := C * O.f * O.m * O.N * b * Real.log b + C * (O.m : ℝ) ^ 2 * (O.N : ℝ) ^ 2 * O.Sig0 C b

def bIP (C b : ℝ) : ℝ := O.bIPa C b + 3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * Real.log b

def bDel (C b : ℝ) : ℝ :=
  C * O.f * (2 * (O.N : ℝ)) * Real.log ((O.f : ℝ) * (2 * (O.N : ℝ))) + C * O.f * (2 * (O.N : ℝ)) * O.Bw * Real.log b +
    C * O.f * (2 * (O.N : ℝ)) ^ 2 * O.Bw * O.cS

def bArch (C b : ℝ) : ℝ :=
  C * O.f * (2 * (O.N : ℝ)) * O.Bw * (Real.log b + Real.log (O.Bw * (2 * (O.N : ℝ)))) +
    C * O.f * (O.N : ℝ) ^ 2 * (Real.log b + Real.log ((O.f : ℝ) * (2 * (O.N : ℝ)) * O.Bw)) + C * (O.N : ℝ) ^ 2 * O.cS

def bTH (C x b : ℝ) : ℝ := C * O.f * b * (Real.log b + Real.log x)

def pol (C b : ℝ) : ℝ :=
  100000 * C ^ 3 * O.f * (O.m : ℝ) ^ 2 * (O.N : ℝ) ^ 2 * (O.r * O.N * Real.log b + O.PPF C b)

end FunData

section Leaves

variable {Bs : DefBase K} {Df : DefSide Bs}

def LeafMM (O : FunData K Df) (C : ℝ) : Prop :=
  O.M.FG ∧ O.M ≠ ⊥ ∧ (∀ v, IsUnit (O.X' v).det) ∧ muMaxDef (Pi.basisFun K (Fin O.n)) O.X' O.M ≤ O.EMM C

def LeafC (S : IndefData Df) (O : FunData K Df) : Prop :=
  ∃ Ψ : Matrix (Fin O.n) (Fin S.D) K, ∀ t, (t = Bs.μ0 ∨ ∃ w, S.μ w = t) →
    Ψ * S.ι t * Df.Pq t = (∏ ij, O.rq t ij)⁻¹ • O.vmu t

def LeafKer (O : FunData K Df) : Prop :=
  LinearMap.ker (O.vmu Bs.μ0).mulVecLin = Df.U Bs.μ0

def LeafFP (O : FunData K Df) (μ : Pl K → Bs.Tup) (C b : ℝ) : Prop :=
  (∀ w : Pl K, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (O.vmu (μ w)) (Df.Mt (μ w))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(O.dF w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) O.M)) ∧
    (∀ w : Pl K, w ∉ O.Tf → O.dF w = 0) ∧ 2 * ∑ w ∈ O.Tf, lw w * (O.dF w : ℝ) ≤ O.bFP C b

def LeafIP (S : IndefData Df) (O : FunData K Df) (C b : ℝ) : Prop :=
  (∀ vb : Matrix (Fin O.n) (Fin (Df.dQ Bs.μ0)) K, vb * Df.Pq Bs.μ0 = O.vmu Bs.μ0 →
      htMap (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin O.n)) O.X'
        (Matrix.mulVecLin vb) ≤ O.bIPa C b) ∧
    ∃ g : InfinitePlace K → ℝ, (∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) ∧
      -(3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * Real.log b) ≤ meanInf K g

def LeafOneSquare (O : FunData K Df) (μ : Pl K → Bs.Tup) (C b : ℝ) : Prop :=
  (∀ ij, O.rq Bs.μ0 ij = 1) ∧ (∀ w ij, O.rq (μ w) ij ≠ 0) ∧ (∀ l ∈ O.Se, l.Prime) ∧
    (∀ ij, O.dd ij = 2 * O.hd ij) ∧ (∀ ij, O.dd ij ≤ 2 * O.N) ∧ (∀ ij, O.yy ij + 1 ≤ O.m) ∧
    (∀ q ∈ O.S0, O.cc q ≤ O.ee C b q) ∧
    ∀ w : Pl K, ∀ ij, (vw w (O.rq (μ w) ij) : ℝ) ≤ |(vw w (O.zA ij) : ℝ)| + |(vw w (O.zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (O.hd ij), (|((vw w (O.zT ij s) + O.gT ij s w : ℤ) : ℝ)| +
        |((vw w (O.zTd ij (O.ch w) s) + O.gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (O.hd ij), wt O.Sd (O.N0 ij s) w) +
      O.dd ij * wt O.Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * O.dl w +
      O.yy ij * (2 * ∑ q ∈ O.S0, (O.cc q : ℝ) * (vw w (O.qq q : K) : ℝ))

def PrimeCountingSumBound (O : FunData K Df) (C x b : ℝ) : Prop :=
  (∀ l ∈ O.Sd, l.Prime) ∧ ∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ O.hd ij →
    (∀ l ∈ O.Sd, 0 ≤ O.N0 ij s l) ∧ ∑ l ∈ O.Sd, O.N0 ij s l * Real.log l ≤ O.bTH C x b

def LeafINT (O : FunData K Df) (C b : ℝ) : Prop :=
  (∀ w, 0 ≤ O.dl w) ∧ (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * O.dl w ≤ O.bDel C b) ∧
    ∀ ij, O.zA ij ≠ 0 ∧ O.zA' ij ≠ 0 ∧
      ∀ w, -(3 * O.dl w) ≤ (vw w (O.zA ij) : ℝ) ∧ -(3 * O.dl w) ≤ (vw w (O.zA' ij) : ℝ)

def LeafARCH (O : FunData K Df) (C b : ℝ) : Prop :=
  ∀ ij, meanInf K (fun v => Real.posLog ‖v.embedding (O.zA ij)‖) ≤ O.bArch C b ∧
    meanInf K (fun v => Real.posLog ‖v.embedding (O.zA' ij)‖) ≤ O.bArch C b

def LeafTHB (O : FunData K Df) (C x b : ℝ) : Prop :=
  (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ O.hd ij → O.zT ij s ≠ 0 ∧ ∀ c, O.zTd ij c s ≠ 0) ∧
    (∀ ij s, HtLe (O.gT ij s) (O.zT ij s) (O.bTH C x b)) ∧ ∀ ij c s, HtLe (O.gT ij s) (O.zTd ij c s) (O.bTH C x b)

def leafHypothesesConst (O : FunData K Df) : Prop :=
  2 ≤ O.m ∧ O.m + 3 ≤ O.k ∧ O.m ^ 4 ≤ O.f ∧ O.f ≤ O.k

def LatticeConstantBound (O : FunData K Df) (b : ℝ) : Prop := (O.Lc : ℝ) ≤ b

def DegreeAndSizeBounds (O : FunData K Df) (C b : ℝ) : Prop :=
  (O.m : ℝ) * O.f * (O.N : ℝ) ^ 2 ≤ b ∧ 80 * O.r ^ 4 ≤ O.N ∧ O.np ≤ 2 * O.m * O.r ∧
    O.Rp C ≤ C * O.m * (O.N : ℝ) ^ 3 * b ∧ Real.log (O.np * O.Rp C) ≤ 4 * Real.log b

def PrimePowerModuliSumBound (O : FunData K Df) (C b : ℝ) : Prop :=
  (∀ q ∈ O.S0, IsPrimePow (O.qq q)) ∧ O.Sig0 C b ≤ 2 * O.PPF C b

def LeafCS (O : FunData K Df) (b : ℝ) : Prop := O.cS ≤ 45 * O.f * Real.log b

def LeafWt (O : FunData K Df) (C b : ℝ) : Prop :=
  1 ≤ O.Bw ∧ O.Bw ≤ C * b ∧ Real.log O.Bw ≤ C * Real.log b

def LeafPol (O : FunData K Df) (C x CH b : ℝ) : Prop := O.pol C b ≤ x ^ CH

end Leaves

macro "pos_tac" : tactic =>
  `(tactic| (repeat' (first | (positivity) | (apply mul_nonneg) | (apply add_nonneg) | (apply pow_nonneg))) <;> linarith)

macro "onele_tac" : tactic =>
  `(tactic| (repeat' (first | exact one_le_pow₀ (by assumption) | apply one_le_mul_of_one_le_of_one_le)) <;> assumption)

/- English proof (translation)
Rewrite using `[← ht]`. Conclude with `le_mul_of_one_le_right ha hz`.
-/
theorem le_mul_one_le {a z t : ℝ} (ha : 0 ≤ a) (hz : 1 ≤ z) (ht : a * z = t) : a ≤ t := by
  rw [← ht]
  exact le_mul_of_one_le_right ha hz

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Substitute `hEM hIP hFP hDel hArch hT` using the available equality. Use `set R := k + m - 1 with hRd`. Establish `o : ∀ {x y : ℝ}, 1 ≤ x → 1 ≤ y → 1 ≤ x * y` using `fun hx hy => one_le_mul_of_one_le_of_one_le hx hy`. Establish `hf0 : 0 ≤ f` using `by linarith`. Establish `hm0 : 0 ≤ m` using `by linarith`.

Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hL0 : 0 ≤ L` using `by linarith`. Establish `hC0 : 0 ≤ C` using `by linarith`. Establish `hR1 : 1 ≤ R` using `by linarith`. Establish `hR0 : 0 ≤ R` using `by linarith`.

Establish `hfR : f ≤ R` using `by linarith`. Establish `hN1 : 1 ≤ N` using `by linarith`. Establish `hN0 : 0 ≤ N` using `by linarith`. Establish `hmN : m ≤ N` using `by linarith`. Establish `hPPF : 0 ≤ PPF` using `by linarith`.

Establish `hC2 : 1 ≤ C ^ 2` using `by nlinarith`. Establish `hC3 : C ≤ C ^ 3` using `by nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ C ^ 2 - 1)]`. Establish `hC23 : C ^ 2 ≤ C ^ 3` using `by nlinarith [mul_nonneg (sq_nonneg C) (by linarith : (0 : ℝ) ≤ C - 1)]`. Establish `hC31 : 1 ≤ C ^ 3` using `by linarith`. Establish `hC30 : 0 ≤ C ^ 3` using `by linarith`.

Establish `hN2 : 1 ≤ N ^ 2` using `by nlinarith`. Establish `hN3 : 0 ≤ N ^ 3` using `pow_nonneg hN0 3`. Establish `hm2 : 0 ≤ m ^ 2` using `sq_nonneg m`. Establish `pN2 : 0 ≤ N ^ 2` using `sq_nonneg N`. Establish `pCf : 0 ≤ C * f` using `mul_nonneg hC0 hf0`.

Establish `hW : 0 ≤ m ^ 2 * R * N ^ 3 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm2 hR0) hN3) hb0) hL0`. Establish `h2mR : 0 ≤ 2 * m * R` using `mul_nonneg (mul_nonneg (by norm_num) hm0) hR0`. Establish `hCmNb : 0 ≤ C * m * N ^ 3 * b` using `mul_nonneg (mul_nonneg (mul_nonneg hC0 hm0) hN3) hb0`. Establish `a1a : np * Rp ≤ (2 * m * R) * (C * m * N ^ 3 * b)` using `mul_le_mul hnp hRp hRp0 h2mR`. Establish `a1b : np * Rp * lg ≤ (2 * m * R) * (C * m * N ^ 3 * b) * (4 * L)` using `mul_le_mul a1a hlg hlg0 (mul_nonneg h2mR hCmNb)`.

Establish `a1c : C * (m ^ 2 * R * N ^ 3 * b * L) ≤ C ^ 3 * (m ^ 2 * R * N ^ 3 * b * L)` using `mul_le_mul_of_nonneg_right hC3 hW`. Establish `a1 : 4 * f * (np * Rp * lg) ≤ 4 * f * (8 * (C ^ 3 * (m ^ 2 * R * N ^ 3 * b * L)))` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `v2 : 0 ≤ C * f * m * N * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pCf hm0) hN0) hb0) hL0`. Establish `a2` using `le_mul_of_one_le_right v2 (o (o (o hC2 hm) hR1) hN2)`. Establish `v3 : 0 ≤ C * m ^ 2 * N ^ 2` using `mul_nonneg (mul_nonneg hC0 hm2) pN2`.

Establish `a3a` using `mul_le_mul_of_nonneg_left hSg v3`. Establish `a3b` using `le_mul_of_one_le_right (mul_nonneg v3 hPPF) (o (o hC2 hf) hb)`. Establish `v4 : 0 ≤ C * f * m * N ^ 2 * L` using `mul_nonneg (mul_nonneg (mul_nonneg pCf hm0) pN2) hL0`. Establish `a4` using `le_mul_of_one_le_right v4 (o (o (o (o hC2 hm) hR1) hN1) hb)`. Establish `v5 : 0 ≤ C * f * (2 * N)` using `mul_nonneg pCf (by linarith)`.

Establish `d1a` using `mul_le_mul_of_nonneg_left hl1 v5`. Establish `d1c` using `mul_le_mul_of_nonneg_left (by linarith : 1 + L ≤ 2 * L) v5`. Establish `v6 : 0 ≤ C * f * N * L` using `mul_nonneg (mul_nonneg pCf hN0) hL0`. Establish `d1b` using `le_mul_of_one_le_right v6 (o (o (o hC hf) hN1) hb)`. Establish `v7 : 0 ≤ C * f * (2 * N) * L` using `mul_nonneg v5 hL0`.

Establish `d2a` using `mul_le_mul_of_nonneg_left hBw v7`. Establish `v8 : 0 ≤ C ^ 2 * f * N * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hf0) hN0) hb0) hL0`. Establish `d2b` using `le_mul_of_one_le_right v8 (o hf hN1)`. Establish `hCb0 : 0 ≤ C * b` using `mul_nonneg hC0 hb0`. Establish `d3a : Bw * cs ≤ (C * b) * (45 * f * L)` using `mul_le_mul hBw hcs hcs0 hCb0`.

Establish `v9 : 0 ≤ C * f * (2 * N) ^ 2` using `mul_nonneg pCf (sq_nonneg _)`. Establish `d3b` using `mul_le_mul_of_nonneg_left d3a v9`. Establish `hDel' : C * f * (2 * N) * l1 + C * f * (2 * N) * Bw * L + C * f * (2 * N) ^ 2 * Bw * cs ≤ 186 * (C ^ 2 * f ^ 2 * N ^ 2 * b * L)` using `by linarith`. Establish `hCL : 1 ≤ C * L` using `o hC hL`. Establish `hLC : 0 ≤ L * (C - 1)` using `mul_nonneg hL0 (by linarith)`.

Establish `e1 : L + l2 ≤ 4 * C * L` using `by nlinarith`. Establish `e3 : L + l3 ≤ 4 * C * L` using `by nlinarith`. Establish `h4CL : 0 ≤ 4 * C * L` using `mul_nonneg (mul_nonneg (by norm_num) hC0) hL0`. Establish `e2 : Bw * (L + l2) ≤ (C * b) * (4 * C * L)`. Use `mul_le_mul_of_nonneg_left e1 hBw0` as an intermediate fact.

Use `mul_le_mul_of_nonneg_right hBw h4CL` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a5a` using `mul_le_mul_of_nonneg_left e2 v5`. Establish `v10 : 0 ≤ C ^ 3 * f * N * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hN0) hb0) hL0`. Establish `a5b` using `le_mul_of_one_le_right v10 hN1`.

Establish `v11 : 0 ≤ C * f * N ^ 2` using `mul_nonneg pCf pN2`. Establish `a6a` using `mul_le_mul_of_nonneg_left e3 v11`. Establish `v12 : 0 ≤ C ^ 2 * f * N ^ 2 * L` using `mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hf0) pN2) hL0`. Establish `a6b` using `le_mul_of_one_le_right v12 (o hC hb)`. Establish `v13 : 0 ≤ C * N ^ 2` using `mul_nonneg hC0 pN2`.

Establish `a7a` using `mul_le_mul_of_nonneg_left hcs v13`. Establish `v14 : 0 ≤ C * f * N ^ 2 * L` using `mul_nonneg v11 hL0`. Establish `a7b` using `le_mul_of_one_le_right v14 (o hC2 hb)`. Establish `hArch' : C * f * (2 * N) * Bw * (L + l2) + C * f * N ^ 2 * (L + l3) + C * N ^ 2 * cs ≤ 57 * (C ^ 3 * f * N ^ 2 * b * L)` using `by linarith`. Establish `v15 : 0 ≤ C * f * b` using `mul_nonneg pCf hb0`.

Establish `hT' : C * f * b * (L + lx) ≤ 3 * (C * f * b * L)`. Use `mul_le_mul_of_nonneg_left (by linarith : L + lx ≤ 3 * L) v15` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `v16 : 0 ≤ C ^ 3 * f * N ^ 2 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) pN2) hb0) hL0`. Establish `m1` using `le_mul_of_one_le_right v16 hf`.

Establish `v17 : 0 ≤ f ^ 2 * N ^ 2 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg f) pN2) hb0) hL0`. Establish `m2` using `mul_le_mul_of_nonneg_right hC23 v17`. Establish `v18 : 0 ≤ C * f * b * L` using `mul_nonneg v15 hL0`. Establish `m3` using `le_mul_of_one_le_right v18 (o (o hC2 hf) hN2)`. Establish `v19 : 0 ≤ C ^ 3 * f ^ 2 * N ^ 2 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 (sq_nonneg f)) pN2) hb0) hL0`.

Establish `hmax : max (C * f * (2 * N) * Bw * (L + l2) + C * f * N ^ 2 * (L + l3) + C * N ^ 2 * cs + 6 * (C * f * (2 * N) * l1 + C * f * (2 * N) * Bw * L + C * f * (2 * N) ^ 2 * Bw * cs)) (C * f * b * (L + lx)) ≤ 1176 * (C ^ 3 * f ^ 2 * N ^ 2 * b * L)`. Apply the tactic sequence `apply max_le <;> linarith`. Establish `a8a` using `mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ 2 * (2 + 8 * N))`. Establish `a8b` using `mul_le_mul_of_nonneg_right (by linarith : 2 * (2 + 8 * N) ≤ 20 * N) (by linarith : (0 : ℝ) ≤ 1176 * (C ^ 3 * f ^ 2 * N ^ 2 * b * L))`. Establish `a8c` using `mul_le_mul_of_nonneg_left (a8a.trans a8b) hm2`.

Establish `v20 : 0 ≤ C ^ 3 * f * m ^ 2 * N ^ 3 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hm2) hN3) hb0) hL0`. Establish `a8d` using `mul_le_mul_of_nonneg_left hfR v20`. Establish `a9a` using `mul_le_mul_of_nonneg_left hT' (mul_nonneg hm2 (by linarith : (0 : ℝ) ≤ 10 * N))`. Establish `v21 : 0 ≤ C * f * m ^ 2 * N * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pCf hm2) hN0) hb0) hL0`. Establish `a9b` using `le_mul_of_one_le_right v21 (o (o hC2 hR1) hN2)`.

Establish `v22 : 0 ≤ m ^ 2 * N` using `mul_nonneg hm2 hN0`. Establish `a10` using `le_mul_of_one_le_right v22 (o (o (o (o (o hC31 hf) hR1) hN2) hb) hL)`. Establish `a11a` using `mul_le_mul_of_nonneg_left hDel' (by positivity : (0 : ℝ) ≤ 6 * m ^ 2)`. Establish `v23 : 0 ≤ C ^ 2 * f * m ^ 2 * N ^ 2 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hf0) hm2) pN2) hb0) hL0`. Establish `a11b` using `mul_le_mul_of_nonneg_left hfR v23`.

Establish `v24 : 0 ≤ C ^ 2 * f * m ^ 2 * N ^ 2 * b * L * R` using `mul_nonneg v23 hR0`. Establish `a11c` using `le_mul_of_one_le_right v24 (o hC hN1)`. Establish `a12a` using `mul_le_mul_of_nonneg_left hSg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg hm0 3))`. Establish `g25 : 1 ≤ C ^ 3 * f * N * b` using `o (o (o hC31 hf) hN1) hb`. Establish `a12b : m ≤ C ^ 3 * f * N ^ 2 * b`.

Use `le_mul_of_one_le_right hN0 g25` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a12c` using `mul_le_mul_of_nonneg_left a12b (mul_nonneg hm2 hPPF)`. Establish `v27 : 0 ≤ C * f * b * N * m ^ 2` using `mul_nonneg (mul_nonneg (mul_nonneg pCf hb0) hN0) hm2`. Establish `a13a` using `mul_le_mul_of_nonneg_left hSg v27`.

Establish `a13b` using `le_mul_of_one_le_right (mul_nonneg v27 hPPF) (o hC2 hN1)`. Establish `v28 : 0 ≤ C * f * m ^ 2 * N ^ 2 * L * b` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pCf hm2) pN2) hL0) hb0`. Establish `a14` using `le_mul_of_one_le_right v28 (o (o hC2 hR1) hN1)`. Establish `v29 : 0 ≤ C * f * m ^ 2 * N ^ 2 * b` using `mul_nonneg (mul_nonneg (mul_nonneg pCf hm2) pN2) hb0`. Establish `a15a` using `mul_le_mul_of_nonneg_left hSg v29`.

Establish `a15b` using `le_mul_of_one_le_right (mul_nonneg v29 hPPF) hC2`. Establish `hX0 : 0 ≤ C ^ 3 * f * m ^ 2 * R * N ^ 3 * b * L` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hm2) hR0) hN3) hb0) hL0`. Establish `hY0 : 0 ≤ C ^ 3 * f * m ^ 2 * N ^ 2 * PPF * b` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hm2) pN2) hPPF) hb0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_arith (f k m N L PPF Bw C b lx Sg cs np Rp lg l1 l2 l3 EM hI FP Arch Del T : ℝ)
    (hm : 1 ≤ m) (hf : 1 ≤ f) (hfk : f ≤ k) (hrN : k + m - 1 ≤ N) (hb : 1 ≤ b) (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hSg0 : 0 ≤ Sg) (hSg : Sg ≤ 2 * PPF) (hcs0 : 0 ≤ cs) (hcs : cs ≤ 45 * f * L) (hlx : lx ≤ 2 * L)
    (hnp0 : 0 ≤ np) (hnp : np ≤ 2 * m * (k + m - 1)) (hRp0 : 0 ≤ Rp) (hRp : Rp ≤ C * m * N ^ 3 * b)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ 4 * L) (hl1 : l1 ≤ 1 + L) (hl2 : l2 ≤ C * L + 1 + L) (hl3 : l3 ≤ 1 + L + C * L)
    (hBw0 : 0 ≤ Bw) (hBw : Bw ≤ C * b)
    (hEM : EM = 4 * f * np * Rp * lg)
    (hIP : hI = C * f * m * N * b * L + C * m ^ 2 * N ^ 2 * Sg + 3 * C * f * m * N ^ 2 * L)
    (hFP : FP = C * f * b * N * m * (m * L + m * Sg) + C * f * m ^ 2 * N ^ 2 * (L + Sg) * b)
    (hDel : Del = C * f * (2 * N) * l1 + C * f * (2 * N) * Bw * L + C * f * (2 * N) ^ 2 * Bw * cs)
    (hArch : Arch = C * f * (2 * N) * Bw * (L + l2) + C * f * N ^ 2 * (L + l3) + C * N ^ 2 * cs)
    (hT : T = C * f * b * (L + lx)) :
    EM + hI + 2 * (m ^ 2 * (2 * (2 + 8 * N) * max (Arch + 6 * Del) T + 10 * N * T + 2 * N + 6 * Del + 4 * m * Sg) +
      FP / 2) ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * ((k + m - 1) * N * L + PPF) * b := by
  subst hEM hIP hFP hDel hArch hT
  set R := k + m - 1 with hRd
  have o : ∀ {x y : ℝ}, 1 ≤ x → 1 ≤ y → 1 ≤ x * y := fun hx hy => one_le_mul_of_one_le_of_one_le hx hy
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hfR : f ≤ R := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hmN : m ≤ N := by linarith
  have hPPF : 0 ≤ PPF := by linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hC3 : C ≤ C ^ 3 := by nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ C ^ 2 - 1)]
  have hC23 : C ^ 2 ≤ C ^ 3 := by nlinarith [mul_nonneg (sq_nonneg C) (by linarith : (0 : ℝ) ≤ C - 1)]
  have hC31 : 1 ≤ C ^ 3 := by linarith
  have hC30 : 0 ≤ C ^ 3 := by linarith
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have hN3 : 0 ≤ N ^ 3 := pow_nonneg hN0 3
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  have pN2 : 0 ≤ N ^ 2 := sq_nonneg N
  have pCf : 0 ≤ C * f := mul_nonneg hC0 hf0
  have hW : 0 ≤ m ^ 2 * R * N ^ 3 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm2 hR0) hN3) hb0) hL0
  have h2mR : 0 ≤ 2 * m * R := mul_nonneg (mul_nonneg (by norm_num) hm0) hR0
  have hCmNb : 0 ≤ C * m * N ^ 3 * b := mul_nonneg (mul_nonneg (mul_nonneg hC0 hm0) hN3) hb0
  have a1a : np * Rp ≤ (2 * m * R) * (C * m * N ^ 3 * b) := mul_le_mul hnp hRp hRp0 h2mR
  have a1b : np * Rp * lg ≤ (2 * m * R) * (C * m * N ^ 3 * b) * (4 * L) :=
    mul_le_mul a1a hlg hlg0 (mul_nonneg h2mR hCmNb)
  have a1c : C * (m ^ 2 * R * N ^ 3 * b * L) ≤ C ^ 3 * (m ^ 2 * R * N ^ 3 * b * L) :=
    mul_le_mul_of_nonneg_right hC3 hW
  have a1 : 4 * f * (np * Rp * lg) ≤ 4 * f * (8 * (C ^ 3 * (m ^ 2 * R * N ^ 3 * b * L))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have v2 : 0 ≤ C * f * m * N * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pCf hm0) hN0) hb0) hL0
  have a2 := le_mul_of_one_le_right v2 (o (o (o hC2 hm) hR1) hN2)
  have v3 : 0 ≤ C * m ^ 2 * N ^ 2 := mul_nonneg (mul_nonneg hC0 hm2) pN2
  have a3a := mul_le_mul_of_nonneg_left hSg v3
  have a3b := le_mul_of_one_le_right (mul_nonneg v3 hPPF) (o (o hC2 hf) hb)
  have v4 : 0 ≤ C * f * m * N ^ 2 * L := mul_nonneg (mul_nonneg (mul_nonneg pCf hm0) pN2) hL0
  have a4 := le_mul_of_one_le_right v4 (o (o (o (o hC2 hm) hR1) hN1) hb)
  have v5 : 0 ≤ C * f * (2 * N) := mul_nonneg pCf (by linarith)
  have d1a := mul_le_mul_of_nonneg_left hl1 v5
  have d1c := mul_le_mul_of_nonneg_left (by linarith : 1 + L ≤ 2 * L) v5
  have v6 : 0 ≤ C * f * N * L := mul_nonneg (mul_nonneg pCf hN0) hL0
  have d1b := le_mul_of_one_le_right v6 (o (o (o hC hf) hN1) hb)
  have v7 : 0 ≤ C * f * (2 * N) * L := mul_nonneg v5 hL0
  have d2a := mul_le_mul_of_nonneg_left hBw v7
  have v8 : 0 ≤ C ^ 2 * f * N * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hf0) hN0) hb0) hL0
  have d2b := le_mul_of_one_le_right v8 (o hf hN1)
  have hCb0 : 0 ≤ C * b := mul_nonneg hC0 hb0
  have d3a : Bw * cs ≤ (C * b) * (45 * f * L) := mul_le_mul hBw hcs hcs0 hCb0
  have v9 : 0 ≤ C * f * (2 * N) ^ 2 := mul_nonneg pCf (sq_nonneg _)
  have d3b := mul_le_mul_of_nonneg_left d3a v9
  have hDel' : C * f * (2 * N) * l1 + C * f * (2 * N) * Bw * L + C * f * (2 * N) ^ 2 * Bw * cs ≤
      186 * (C ^ 2 * f ^ 2 * N ^ 2 * b * L) := by linarith
  have hCL : 1 ≤ C * L := o hC hL
  have hLC : 0 ≤ L * (C - 1) := mul_nonneg hL0 (by linarith)
  have e1 : L + l2 ≤ 4 * C * L := by nlinarith
  have e3 : L + l3 ≤ 4 * C * L := by nlinarith
  have h4CL : 0 ≤ 4 * C * L := mul_nonneg (mul_nonneg (by norm_num) hC0) hL0
  have e2 : Bw * (L + l2) ≤ (C * b) * (4 * C * L) := by
    have := mul_le_mul_of_nonneg_left e1 hBw0
    have := mul_le_mul_of_nonneg_right hBw h4CL
    linarith
  have a5a := mul_le_mul_of_nonneg_left e2 v5
  have v10 : 0 ≤ C ^ 3 * f * N * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hN0) hb0) hL0
  have a5b := le_mul_of_one_le_right v10 hN1
  have v11 : 0 ≤ C * f * N ^ 2 := mul_nonneg pCf pN2
  have a6a := mul_le_mul_of_nonneg_left e3 v11
  have v12 : 0 ≤ C ^ 2 * f * N ^ 2 * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hf0) pN2) hL0
  have a6b := le_mul_of_one_le_right v12 (o hC hb)
  have v13 : 0 ≤ C * N ^ 2 := mul_nonneg hC0 pN2
  have a7a := mul_le_mul_of_nonneg_left hcs v13
  have v14 : 0 ≤ C * f * N ^ 2 * L := mul_nonneg v11 hL0
  have a7b := le_mul_of_one_le_right v14 (o hC2 hb)
  have hArch' : C * f * (2 * N) * Bw * (L + l2) + C * f * N ^ 2 * (L + l3) + C * N ^ 2 * cs ≤
      57 * (C ^ 3 * f * N ^ 2 * b * L) := by linarith
  have v15 : 0 ≤ C * f * b := mul_nonneg pCf hb0
  have hT' : C * f * b * (L + lx) ≤ 3 * (C * f * b * L) := by
    have := mul_le_mul_of_nonneg_left (by linarith : L + lx ≤ 3 * L) v15
    linarith
  have v16 : 0 ≤ C ^ 3 * f * N ^ 2 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) pN2) hb0) hL0
  have m1 := le_mul_of_one_le_right v16 hf
  have v17 : 0 ≤ f ^ 2 * N ^ 2 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg f) pN2) hb0) hL0
  have m2 := mul_le_mul_of_nonneg_right hC23 v17
  have v18 : 0 ≤ C * f * b * L := mul_nonneg v15 hL0
  have m3 := le_mul_of_one_le_right v18 (o (o hC2 hf) hN2)
  have v19 : 0 ≤ C ^ 3 * f ^ 2 * N ^ 2 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 (sq_nonneg f)) pN2) hb0) hL0
  have hmax : max (C * f * (2 * N) * Bw * (L + l2) + C * f * N ^ 2 * (L + l3) + C * N ^ 2 * cs +
      6 * (C * f * (2 * N) * l1 + C * f * (2 * N) * Bw * L + C * f * (2 * N) ^ 2 * Bw * cs))
      (C * f * b * (L + lx)) ≤ 1176 * (C ^ 3 * f ^ 2 * N ^ 2 * b * L) := by
    apply max_le <;> linarith
  have a8a := mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ 2 * (2 + 8 * N))
  have a8b := mul_le_mul_of_nonneg_right (by linarith : 2 * (2 + 8 * N) ≤ 20 * N)
    (by linarith : (0 : ℝ) ≤ 1176 * (C ^ 3 * f ^ 2 * N ^ 2 * b * L))
  have a8c := mul_le_mul_of_nonneg_left (a8a.trans a8b) hm2
  have v20 : 0 ≤ C ^ 3 * f * m ^ 2 * N ^ 3 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hm2) hN3) hb0) hL0
  have a8d := mul_le_mul_of_nonneg_left hfR v20
  have a9a := mul_le_mul_of_nonneg_left hT' (mul_nonneg hm2 (by linarith : (0 : ℝ) ≤ 10 * N))
  have v21 : 0 ≤ C * f * m ^ 2 * N * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pCf hm2) hN0) hb0) hL0
  have a9b := le_mul_of_one_le_right v21 (o (o hC2 hR1) hN2)
  have v22 : 0 ≤ m ^ 2 * N := mul_nonneg hm2 hN0
  have a10 := le_mul_of_one_le_right v22 (o (o (o (o (o hC31 hf) hR1) hN2) hb) hL)
  have a11a := mul_le_mul_of_nonneg_left hDel' (by positivity : (0 : ℝ) ≤ 6 * m ^ 2)
  have v23 : 0 ≤ C ^ 2 * f * m ^ 2 * N ^ 2 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hf0) hm2) pN2) hb0) hL0
  have a11b := mul_le_mul_of_nonneg_left hfR v23
  have v24 : 0 ≤ C ^ 2 * f * m ^ 2 * N ^ 2 * b * L * R := mul_nonneg v23 hR0
  have a11c := le_mul_of_one_le_right v24 (o hC hN1)
  have a12a := mul_le_mul_of_nonneg_left hSg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg hm0 3))
  have g25 : 1 ≤ C ^ 3 * f * N * b := o (o (o hC31 hf) hN1) hb
  have a12b : m ≤ C ^ 3 * f * N ^ 2 * b := by
    have := le_mul_of_one_le_right hN0 g25
    linarith
  have a12c := mul_le_mul_of_nonneg_left a12b (mul_nonneg hm2 hPPF)
  have v27 : 0 ≤ C * f * b * N * m ^ 2 := mul_nonneg (mul_nonneg (mul_nonneg pCf hb0) hN0) hm2
  have a13a := mul_le_mul_of_nonneg_left hSg v27
  have a13b := le_mul_of_one_le_right (mul_nonneg v27 hPPF) (o hC2 hN1)
  have v28 : 0 ≤ C * f * m ^ 2 * N ^ 2 * L * b :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg pCf hm2) pN2) hL0) hb0
  have a14 := le_mul_of_one_le_right v28 (o (o hC2 hR1) hN1)
  have v29 : 0 ≤ C * f * m ^ 2 * N ^ 2 * b := mul_nonneg (mul_nonneg (mul_nonneg pCf hm2) pN2) hb0
  have a15a := mul_le_mul_of_nonneg_left hSg v29
  have a15b := le_mul_of_one_le_right (mul_nonneg v29 hPPF) hC2
  have hX0 : 0 ≤ C ^ 3 * f * m ^ 2 * R * N ^ 3 * b * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hm2) hR0) hN3) hb0) hL0
  have hY0 : 0 ≤ C ^ 3 * f * m ^ 2 * N ^ 2 * PPF * b :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC30 hf0) hm2) pN2) hPPF) hb0
  linarith

/- English proof (translation)
Unfold `Formalism.PairingDivisionLocalBalance.HtLe at h ⊢`. Conclude with `⟨h.1, h.2.trans hB⟩`.
-/
theorem htLe_mono {g : Pl K → ℤ} {z : K} {B B' : ℝ} (h : HtLe g z B) (hB : B ≤ B') : HtLe g z B' := by
  unfold Formalism.PairingDivisionLocalBalance.HtLe at h ⊢
  exact ⟨h.1, h.2.trans hB⟩

/- English proof (translation)
Break down `eq_or_lt_of_le ha with h | h` into its components or cases. Rewrite using `[← h, zero_mul, Real.log_zero, max_self, zero_add]`. Conclude with `Real.log_nonneg hy`. Rewrite using `[Real.log_mul h.ne' (by linarith)]`. Use `le_max_left (Real.log a) 0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_mul_le {a y : ℝ} (ha : 0 ≤ a) (hy : 1 ≤ y) : Real.log (a * y) ≤ max (Real.log a) 0 + Real.log y := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, zero_mul, Real.log_zero, max_self, zero_add]
    exact Real.log_nonneg hy
  · rw [Real.log_mul h.ne' (by linarith)]
    have := le_max_left (Real.log a) 0
    linarith

section Sizes

variable {Bs : DefBase K} {Df : DefSide Bs}

/- English proof (translation)
Unfold `FunData.Sig0`. Conclude with `Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`.
-/
theorem Sig0_nonneg (O : FunData K Df) (C b : ℝ) : 0 ≤ O.Sig0 C b := by
  unfold FunData.Sig0
  exact Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨hm2, hmk, hmf4, hfk⟩` from `hH1`. Take `⟨hB5a, hB5b, hB5c, hB5d, hB5e⟩` from `hB5`. Take `⟨_, hB7b⟩` from `hB7`. Take `⟨hWt1, hWt2, hWt3⟩` from `hWt`. Establish `hP : O.pol C b ≤ x ^ CH` using `hPol`.

Establish `hCS' : O.cS ≤ 45 * O.f * Real.log b` using `hCS`. Establish `hm4 : 1 ≤ O.m ^ 4` using `Nat.one_le_pow _ _ (by omega)`. Establish `hf1n : 1 ≤ O.f` using `le_trans hm4 hmf4`. Establish `hm : (1 : ℝ) ≤ O.m` using `by exact_mod_cast (by omega : 1 ≤ O.m)`. Establish `hm2r : (2 : ℝ) ≤ O.m` using `by exact_mod_cast hm2`.

Establish `hk : (O.m : ℝ) + 3 ≤ O.k` using `by exact_mod_cast hmk`. Establish `hf : (1 : ℝ) ≤ O.f` using `by exact_mod_cast hf1n`. Establish `hfk' : (O.f : ℝ) ≤ O.k` using `by exact_mod_cast hfk`. Establish `hN : (O.N : ℝ) = O.k + O.m * (O.tt + (O.k + O.m + 5) + 1)`. Simplify using `only [FunData.N, FunData.s]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hrN : (O.k : ℝ) + O.m - 1 ≤ O.N`. Rewrite using `[hN]`. Establish `h0 : (0 : ℝ) ≤ O.m * (O.tt + (O.k + O.m + 5))` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hN1 : (1 : ℝ) ≤ O.N` using `by linarith`. Establish `hmf : (2 : ℝ) ≤ O.m * O.f` using `by nlinarith`. Establish `hNN : (O.N : ℝ) ≤ (O.N : ℝ) ^ 2` using `by nlinarith`. Establish `hb2N : 2 * (O.N : ℝ) ≤ b`.

Establish `h1` using `mul_le_mul_of_nonneg_right hmf (sq_nonneg (O.N : ℝ))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbfN : (O.f : ℝ) * (2 * (O.N : ℝ)) ≤ b`. Establish `h2 : (0 : ℝ) ≤ (O.f : ℝ) * O.N * (O.m * O.N - 2)`. Apply `mul_nonneg (by positivity)` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hb : 1 ≤ b` using `by linarith`. Establish `hSg0` using `Sig0_nonneg O C b`. Establish `hcs0 : 0 ≤ O.cS`.

Unfold `FunData.cS`. Conclude with `Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`. Establish `hlx : Real.log x ≤ 2 * Real.log b` using `by linarith`. Establish `hnp1 : 1 ≤ O.np`. Unfold `FunData.np FunData.r`.

Establish `h0 : (0 : ℝ) ≤ O.m * (O.k + O.m + 4)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hRp1 : 1 ≤ O.Rp C`. Unfold `FunData.Rp`. Establish `h1 : (0 : ℝ) ≤ ((O.m : ℝ) + 1) * ((O.ga C : ℝ) + 1)` using `by positivity`.

Establish `h2 : (0 : ℝ) ≤ (O.Lc : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlg0 : 0 ≤ Real.log (O.np * O.Rp C)` using `Real.log_nonneg (one_le_mul_of_one_le_of_one_le hnp1 hRp1)`. Establish `hfN0 : (0 : ℝ) < (O.f : ℝ) * (2 * (O.N : ℝ))` using `mul_pos (by linarith) (by linarith)`. Establish `hBw0 : (0 : ℝ) < O.Bw` using `by linarith`.

Establish `hlfN : Real.log ((O.f : ℝ) * (2 * (O.N : ℝ))) ≤ Real.log b` using `Real.log_le_log hfN0 hbfN`. Establish `hl2N : Real.log (2 * (O.N : ℝ)) ≤ Real.log b` using `Real.log_le_log (by linarith) hb2N`. Establish `hl1 : Real.log ((O.f : ℝ) * (2 * (O.N : ℝ))) ≤ 1 + Real.log b` using `by linarith`. Establish `hl2 : Real.log (O.Bw * (2 * (O.N : ℝ))) ≤ C * Real.log b + 1 + Real.log b`. Rewrite using `[Real.log_mul hBw0.ne' (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl3 : Real.log ((O.f : ℝ) * (2 * (O.N : ℝ)) * O.Bw) ≤ 1 + Real.log b + C * Real.log b`. Rewrite using `[Real.log_mul hfN0.ne' hBw0.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `size_arith (O.f : ℝ) O.k O.m O.N (Real.log b) (O.PPF C b) O.Bw C b (Real.log x) (O.Sig0 C b) O.cS O.np (O.Rp C) (Real.log (O.np * O.Rp C)) (Real.log ((O.f : ℝ) * (2 * (O.N : ℝ)))) (Real.log (O.Bw * (2 * (O.N : ℝ)))) (Real.log ((O.f : ℝ) * (2 * (O.N : ℝ)) * O.Bw)) (O.EMM C) (O.bIP …`.

Conclude with `le_trans key (mul_le_mul_of_nonneg_right hP (by linarith))`.
-/
theorem size_le (O : FunData K Df) (C x CH b : ℝ) (hC : 1 ≤ C) (hx : 1 ≤ x)
    (hL1 : 1 ≤ Real.log b) (hLx : Real.log b + Real.log x ≤ 3 * Real.log b)
    (hH1 : leafHypothesesConst O) (hB5 : DegreeAndSizeBounds O C b) (hB7 : PrimePowerModuliSumBound O C b) (hCS : LeafCS O b) (hWt : LeafWt O C b)
    (hPol : LeafPol O C x CH b) :
    O.EMM C + O.bIP C b + 2 * (Formalism.AtG.gridBudgetIdx O.m O.N (max (O.bArch C b + 6 * O.bDel C b) (O.bTH C x b))
      (O.bTH C x b) (O.bDel C b) O.S0 (O.ee C b) O.qq + O.bFP C b / 2) ≤ x ^ CH * b := by
  obtain ⟨hm2, hmk, hmf4, hfk⟩ := hH1
  obtain ⟨hB5a, hB5b, hB5c, hB5d, hB5e⟩ := hB5
  obtain ⟨_, hB7b⟩ := hB7
  obtain ⟨hWt1, hWt2, hWt3⟩ := hWt
  have hP : O.pol C b ≤ x ^ CH := hPol
  have hCS' : O.cS ≤ 45 * O.f * Real.log b := hCS
  have hm4 : 1 ≤ O.m ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hf1n : 1 ≤ O.f := le_trans hm4 hmf4
  have hm : (1 : ℝ) ≤ O.m := by exact_mod_cast (by omega : 1 ≤ O.m)
  have hm2r : (2 : ℝ) ≤ O.m := by exact_mod_cast hm2
  have hk : (O.m : ℝ) + 3 ≤ O.k := by exact_mod_cast hmk
  have hf : (1 : ℝ) ≤ O.f := by exact_mod_cast hf1n
  have hfk' : (O.f : ℝ) ≤ O.k := by exact_mod_cast hfk
  have hN : (O.N : ℝ) = O.k + O.m * (O.tt + (O.k + O.m + 5) + 1) := by
    simp only [FunData.N, FunData.s]
    push_cast
    ring
  have hrN : (O.k : ℝ) + O.m - 1 ≤ O.N := by
    rw [hN]
    have h0 : (0 : ℝ) ≤ O.m * (O.tt + (O.k + O.m + 5)) := by positivity
    nlinarith
  have hN1 : (1 : ℝ) ≤ O.N := by linarith
  have hmf : (2 : ℝ) ≤ O.m * O.f := by nlinarith
  have hNN : (O.N : ℝ) ≤ (O.N : ℝ) ^ 2 := by nlinarith
  have hb2N : 2 * (O.N : ℝ) ≤ b := by
    have h1 := mul_le_mul_of_nonneg_right hmf (sq_nonneg (O.N : ℝ))
    linarith
  have hbfN : (O.f : ℝ) * (2 * (O.N : ℝ)) ≤ b := by
    have h2 : (0 : ℝ) ≤ (O.f : ℝ) * O.N * (O.m * O.N - 2) := by
      apply mul_nonneg (by positivity)
      nlinarith
    nlinarith
  have hb : 1 ≤ b := by linarith
  have hSg0 := Sig0_nonneg O C b
  have hcs0 : 0 ≤ O.cS := by
    unfold FunData.cS
    exact Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlx : Real.log x ≤ 2 * Real.log b := by linarith
  have hnp1 : 1 ≤ O.np := by
    unfold FunData.np FunData.r
    have h0 : (0 : ℝ) ≤ O.m * (O.k + O.m + 4) := by positivity
    nlinarith
  have hRp1 : 1 ≤ O.Rp C := by
    unfold FunData.Rp
    have h1 : (0 : ℝ) ≤ ((O.m : ℝ) + 1) * ((O.ga C : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) ≤ (O.Lc : ℝ) := Nat.cast_nonneg _
    linarith
  have hlg0 : 0 ≤ Real.log (O.np * O.Rp C) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hnp1 hRp1)
  have hfN0 : (0 : ℝ) < (O.f : ℝ) * (2 * (O.N : ℝ)) := mul_pos (by linarith) (by linarith)
  have hBw0 : (0 : ℝ) < O.Bw := by linarith
  have hlfN : Real.log ((O.f : ℝ) * (2 * (O.N : ℝ))) ≤ Real.log b := Real.log_le_log hfN0 hbfN
  have hl2N : Real.log (2 * (O.N : ℝ)) ≤ Real.log b := Real.log_le_log (by linarith) hb2N
  have hl1 : Real.log ((O.f : ℝ) * (2 * (O.N : ℝ))) ≤ 1 + Real.log b := by linarith
  have hl2 : Real.log (O.Bw * (2 * (O.N : ℝ))) ≤ C * Real.log b + 1 + Real.log b := by
    rw [Real.log_mul hBw0.ne' (by linarith)]
    linarith
  have hl3 : Real.log ((O.f : ℝ) * (2 * (O.N : ℝ)) * O.Bw) ≤ 1 + Real.log b + C * Real.log b := by
    rw [Real.log_mul hfN0.ne' hBw0.ne']
    linarith
  have key := size_arith (O.f : ℝ) O.k O.m O.N (Real.log b) (O.PPF C b) O.Bw C b (Real.log x) (O.Sig0 C b)
    O.cS O.np (O.Rp C) (Real.log (O.np * O.Rp C)) (Real.log ((O.f : ℝ) * (2 * (O.N : ℝ))))
    (Real.log (O.Bw * (2 * (O.N : ℝ)))) (Real.log ((O.f : ℝ) * (2 * (O.N : ℝ)) * O.Bw)) (O.EMM C) (O.bIP C b)
    (O.bFP C b) (O.bArch C b) (O.bDel C b) (O.bTH C x b) hm hf hfk' hrN hb hL1 hC hSg0 hB7b hcs0 hCS' hlx
    (by linarith) hB5c (by linarith) hB5d hlg0 hB5e hl1 hl2 hl3 (by linarith) hWt2 rfl rfl rfl rfl rfl rfl
  exact le_trans key (mul_le_mul_of_nonneg_right hP (by linarith))

end Sizes

section Hence

open PI.LocGlobInclWork

/- English proof (translation)
Introduce `x hx`. Take `⟨s, hs, hx'⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L` from `hx`. Conclude with `(⟨s, hs, h hx'⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L')`.
-/
theorem localization_mono {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    {L L' : Submodule (𝓞 K) W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  obtain ⟨s, hs, hx'⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L := hx
  exact (⟨s, hs, h hx'⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L')

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.idealSmul at hy ⊢`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨a * c, FractionalIdeal.mul_mem_mul ha hc, x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem smulK_mem_idealSmul {d : ℕ} (I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (B : Submodule (𝓞 K) (Fin d → K)) (c : K) (hc : c ∈ J) {y : Fin d → K}
    (hy : y ∈ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) B) :
    c • y ∈ Formalism.HermitianLatticesTheory.idealSmul ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) B := by
  unfold Formalism.HermitianLatticesTheory.idealSmul at hy ⊢
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨a * c, FractionalIdeal.mul_mem_mul ha hc, x, hx, ?_⟩
    rw [smul_smul, mul_comm]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.idealSmul`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `z ⟨a, ha, x, hx, rfl⟩`. Rewrite `ha` using `[FractionalIdeal.coe_one, Submodule.mem_one]`. Take `⟨r, rfl⟩` from `ha`.

Rewrite using `[algebraMap_smul]`. Conclude with `M.smul_mem r hx`.
-/
theorem idealSmul_one_le {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K)) :
    Formalism.HermitianLatticesTheory.idealSmul (((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) M ≤ M := by
  unfold Formalism.HermitianLatticesTheory.idealSmul
  rw [Submodule.span_le]
  rintro z ⟨a, ha, x, hx, rfl⟩
  rw [FractionalIdeal.coe_one, Submodule.mem_one] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [algebraMap_smul]
  exact M.smul_mem r hx

/- English proof (translation)
Establish `hP : (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot`. Establish `hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.mpr hc`. Use `set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(vw w c)) * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c with hJ`. Establish `hJ0 : J ≠ 0` using `mul_ne_zero (zpow_ne_zero _ hP) hs`. Establish `hcw : FractionalIdeal.count K w J = 0`.

Rewrite using `[hJ, FractionalIdeal.count_mul K w (zpow_ne_zero _ hP) hs, FractionalIdeal.count_zpow_self]`. Simplify using `[vw]`. Establish `hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ FractionalIdeal.count K v J = 0}.Finite` using `Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)`. Establish `hwS : w ∉ hfin.toFinset` using `by simp [hcw]`. Establish `hfac : ∏ v ∈ hfin.toFinset, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (FractionalIdeal.count K v J) = J`.

Rewrite using `[← finprod_eq_prod_of_mulSupport_subset]`. Conclude with `FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ0`. Introduce `v hv`. Simplify using `only [Function.mem_mulSupport] at hv`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]`.

Introduce `h0; exact hv (by rw [h0, zpow_zero])`. Take `⟨t, htw, ht⟩` from `exists_unit_at w hfin.toFinset hwS (fun v => FractionalIdeal.count K v J)`. Use `⟨t, htw, ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[hfac]`. Establish `h2` using `FractionalIdeal.mul_mem_mul ht (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K)) c⁻¹)`.

Rewrite `h2` using `[hJ, mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hc, FractionalIdeal.spanSingleton_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem unit_at_val (w : Pl K) (c : K) (hc : c ≠ 0) : ∃ t : 𝓞 K, t ∉ w.asIdeal ∧
    algebraMap (𝓞 K) K t * c⁻¹ ∈ (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(vw w c)) := by
  classical
  have hP : (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hc
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(vw w c)) *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c with hJ
  have hJ0 : J ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) hs
  have hcw : FractionalIdeal.count K w J = 0 := by
    rw [hJ, FractionalIdeal.count_mul K w (zpow_ne_zero _ hP) hs, FractionalIdeal.count_zpow_self]
    simp [vw]
  have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ FractionalIdeal.count K v J = 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  have hwS : w ∉ hfin.toFinset := by simp [hcw]
  have hfac : ∏ v ∈ hfin.toFinset,
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (FractionalIdeal.count K v J) = J := by
    rw [← finprod_eq_prod_of_mulSupport_subset]
    · exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ0
    · intro v hv
      simp only [Function.mem_mulSupport] at hv
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      intro h0; exact hv (by rw [h0, zpow_zero])
  obtain ⟨t, htw, ht⟩ := exists_unit_at w hfin.toFinset hwS (fun v => FractionalIdeal.count K v J)
  refine ⟨t, htw, ?_⟩
  rw [hfac] at ht
  have h2 := FractionalIdeal.mul_mem_mul ht
    (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K)) c⁻¹)
  rwa [hJ, mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hc,
    FractionalIdeal.spanSingleton_one, mul_one] at h2

/- English proof (translation)
Introduce `y hy`. Take `⟨s, hs, hsy⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K))` from `hy`. Take `⟨r, hr, hry⟩` from `Submodule.mem_map.mp hsy`. Establish `hr' : r ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat Pq Mt))`. Rewrite using `[← hRR]`.

Conclude with `(⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hr⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • r ∈ RR)`. Take `⟨s1, hs1, hs1r⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • r ∈ matLat ι (matLat Pq Mt)` from `hr'`. Establish `hs1r' : s1 • r ∈ (matLat Pq Mt).map ((Matrix.mulVecLin ι).restrictScalars (𝓞 K))` using `hs1r`. Take `⟨q, hq, hqr⟩` from `Submodule.mem_map.mp hs1r'`. Establish `hq' : q ∈ Mt.map ((Matrix.mulVecLin Pq).restrictScalars (𝓞 K))` using `hq`.

Take `⟨z, hz, hzq⟩` from `Submodule.mem_map.mp hq'`. Establish `hvz : v.mulVec z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat v Mt)` using `(⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_map_of_mem hz⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • (v.mulVec z) ∈ matLat v Mt)`. Take `⟨s2, hs2, hs2v⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • (v.mulVec z) ∈ Formalism.HermitianLatticesTheory.idealSmul (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M` from `hFP hvz`. Establish `e1 : (s1 * s) • y = c⁻¹ • (v.mulVec z)`. Establish `h2 : ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K)) (s1 • r) = s1 • (s • y)`.

Rewrite using `[map_smul, hry]`. Rewrite using `[mul_smul, ← h2, ← hqr, ← hzq]`. Express the relevant statement in the definitionally equal form `Ψ.mulVec (ι.mulVec (Pq.mulVec z)) = c⁻¹ • (v.mulVec z)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, heq]`. Use `first`.

Consider the case `exact Matrix.smul_mulVec _ _ _`. Consider the case `exact Matrix.smul_mulVec_assoc _ _ _`. Take `⟨t, ht, htc⟩` from `unit_at_val w c hc`. Establish `hw0 : ((w.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot`. Establish `hmem` using `smulK_mem_idealSmul _ _ M _ htc hs2v`.

Rewrite `hmem` using `[← zpow_add₀ hw0, show -δ + -vw w c = -(vw w c + δ) by ring]`. Use `(⟨t * s2 * (s1 * s), ?_, ?_⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Formalism.HermitianLatticesTheory.idealSmul _ M)` and prove the remaining obligations. Conclude with `mul_mem (mul_mem (Ideal.mem_primeCompl_iff.mpr ht) hs2) (mul_mem hs1 hs)`. Use `hmem using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_smul (t * s2) (s1 * s) y, e1, ← algebraMap_smul K (t * s2), ← algebraMap_smul K s2, smul_smul, smul_smul, map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hence_local {D nV dQ n : ℕ} (w : Pl K) (RR : Submodule (𝓞 K) (Fin D → K)) (ι : Matrix (Fin D) (Fin dQ) K)
    (Pq : Matrix (Fin dQ) (Fin nV) K) (Mt : Submodule (𝓞 K) (Fin nV → K)) (Ψ : Matrix (Fin n) (Fin D) K)
    (v : Matrix (Fin n) (Fin nV) K) (M : Submodule (𝓞 K) (Fin n → K)) (c : K) (hc : c ≠ 0) (δ : ℤ)
    (hRR : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal RR = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat Pq Mt)))
    (heq : Ψ * ι * Pq = c⁻¹ • v)
    (hFP : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat v Mt) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(vw w c + δ)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) := by
  intro y hy
  obtain ⟨s, hs, hsy⟩ : ∃ s ∈ w.asIdeal.primeCompl,
      s • y ∈ RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K)) := hy
  obtain ⟨r, hr, hry⟩ := Submodule.mem_map.mp hsy
  have hr' : r ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat Pq Mt)) := by
    rw [← hRR]
    exact (⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hr⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • r ∈ RR)
  obtain ⟨s1, hs1, hs1r⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • r ∈ matLat ι (matLat Pq Mt) := hr'
  have hs1r' : s1 • r ∈ (matLat Pq Mt).map ((Matrix.mulVecLin ι).restrictScalars (𝓞 K)) := hs1r
  obtain ⟨q, hq, hqr⟩ := Submodule.mem_map.mp hs1r'
  have hq' : q ∈ Mt.map ((Matrix.mulVecLin Pq).restrictScalars (𝓞 K)) := hq
  obtain ⟨z, hz, hzq⟩ := Submodule.mem_map.mp hq'
  have hvz : v.mulVec z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat v Mt) :=
    (⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_map_of_mem hz⟩ :
      ∃ s ∈ w.asIdeal.primeCompl, s • (v.mulVec z) ∈ matLat v Mt)
  obtain ⟨s2, hs2, hs2v⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • (v.mulVec z) ∈ Formalism.HermitianLatticesTheory.idealSmul
      (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M := hFP hvz
  have e1 : (s1 * s) • y = c⁻¹ • (v.mulVec z) := by
    have h2 : ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K)) (s1 • r) = s1 • (s • y) := by
      rw [map_smul, hry]
    rw [mul_smul, ← h2, ← hqr, ← hzq]
    change Ψ.mulVec (ι.mulVec (Pq.mulVec z)) = c⁻¹ • (v.mulVec z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, heq]
    first
      | exact Matrix.smul_mulVec _ _ _
      | exact Matrix.smul_mulVec_assoc _ _ _
  obtain ⟨t, ht, htc⟩ := unit_at_val w c hc
  have hw0 : ((w.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  have hmem := smulK_mem_idealSmul _ _ M _ htc hs2v
  rw [← zpow_add₀ hw0, show -δ + -vw w c = -(vw w c + δ) by ring] at hmem
  refine (⟨t * s2 * (s1 * s), ?_, ?_⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Formalism.HermitianLatticesTheory.idealSmul _ M)
  · exact mul_mem (mul_mem (Ideal.mem_primeCompl_iff.mpr ht) hs2) (mul_mem hs1 hs)
  · convert hmem using 1
    rw [mul_smul (t * s2) (s1 * s) y, e1, ← algebraMap_smul K (t * s2), ← algebraMap_smul K s2,
      smul_smul, smul_smul, map_mul]
    congr 1
    ring

end Hence

section IPFirst

/- English proof (translation)
Simplify using `only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem dot_conj {ι : Type} [Fintype ι] (a b : ι → ℂ) : star (star a ⬝ᵥ b) = star b ⬝ᵥ a := by
  simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Simplify using `only [dotProduct, Complex.re_sum, Pi.star_apply]`. Use `Finset.sum_nonneg fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_re]`. Establish `h1 : (star (z i)).re = (z i).re` using `Complex.conj_re (z i)`. Establish `h2 : (star (z i)).im = -(z i).im` using `Complex.conj_im (z i)`.

Rewrite using `[h1, h2]`. Use polynomial arithmetic with `[sq_nonneg (z i).re, sq_nonneg (z i).im]`.
-/
theorem re_dot_self_nonneg {ι : Type} [Fintype ι] (z : ι → ℂ) : 0 ≤ (star z ⬝ᵥ z).re := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.mul_re]
  have h1 : (star (z i)).re = (z i).re := Complex.conj_re (z i)
  have h2 : (star (z i)).im = -(z i).im := Complex.conj_im (z i)
  rw [h1, h2]
  nlinarith [sq_nonneg (z i).re, sq_nonneg (z i).im]

/- English proof (translation)
Simplify using `only [dotProduct, Finset.sum_apply, Pi.star_apply, star_sum, Finset.sum_mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
private theorem star_sum_dotProduct_sum {ι P : Type} [Fintype ι] [Fintype P] (x y : P → ι → ℂ) :
    star (∑ p, x p) ⬝ᵥ ∑ p, y p = ∑ p, ∑ p', star (x p) ⬝ᵥ y p' := by
  simp only [dotProduct, Finset.sum_apply, Pi.star_apply, star_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `hx : star (x : ℂ) = x` using `Complex.conj_ofReal x`. Simplify using `only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', hx, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem star_ofReal_smul_dotProduct_ofReal_smul {ι : Type} [Fintype ι] (x y : ℝ) (u w : ι → ℂ) :
    star ((x : ℂ) • u) ⬝ᵥ ((y : ℂ) • w) = ((x * y : ℝ) : ℂ) * (star u ⬝ᵥ w) := by
  have hx : star (x : ℂ) = x := Complex.conj_ofReal x
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/- English proof (translation)
Use `set c : P → ℝ := fun p => Real.sqrt (max (s p - m) 0) with hc`. Establish `key : ∀ p p', (s p : ℂ) * (star (a p) ⬝ᵥ a p') = ((m : ℂ) + ((c p * c p' : ℝ) : ℂ)) * (star (a p) ⬝ᵥ a p')`. Introduce `p p'`. Distinguish the cases in `h0 : star (a p) ⬝ᵥ a p' = 0`. Rewrite using `[h0, mul_zero, mul_zero]`.

Establish `hp : a p ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Simplify using `[h]`. Establish `hs : s p = s p'`.

Establish `e1` using `hA p' p`. Establish `e2` using `congrArg star (hA p p')`. Rewrite `e2` using `[dot_conj, star_mul', dot_conj]`. Rewrite `e1` using `[e2]`. Establish `h0' : star (a p') ⬝ᵥ a p ≠ 0`.

Rewrite using `[← dot_conj]`. Conclude with `star_ne_zero.mpr h0`. Establish `e3` using `mul_right_cancel₀ h0' e1`. Establish `e4 : star ((s p : ℝ) : ℂ) = ((s p : ℝ) : ℂ)` using `Complex.conj_ofReal _`. Rewrite `e3` using `[e4]`.

Conclude with `e3` after adjusting the coercions. Establish `hm1 : m ≤ s p` using `hm p hp`. Establish `hcc : c p * c p' = s p - m`. Simplify using `only [hc]`. Rewrite using `[← hs, Real.mul_self_sqrt (le_max_right _ _), max_eq_left (by linarith)]`.

Rewrite using `[hcc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : star (∑ p, A p) ⬝ᵥ ∑ p, A p = ∑ p, ∑ p', (s p : ℂ) * (star (a p) ⬝ᵥ a p')`. Rewrite using `[star_sum_dotProduct_sum]`.

Simplify using `only [hA]`. Establish `hR : ∑ p, ∑ p', (s p : ℂ) * (star (a p) ⬝ᵥ a p') = (m : ℂ) * (star (∑ p, a p) ⬝ᵥ ∑ p, a p) + star (∑ p, ((c p : ℝ) : ℂ) • a p) ⬝ᵥ ∑ p, ((c p : ℝ) : ℂ) • a p`. Rewrite using `[star_sum_dotProduct_sum a a, star_sum_dotProduct_sum (fun p => ((c p : ℝ) : ℂ) • a p) (fun p => ((c p : ℝ) : ℂ) • a p)]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_` and prove the remaining obligations.

Rewrite using `[key p p', star_ofReal_smul_dotProduct_ofReal_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL, hR, Complex.add_re, Complex.re_ofReal_mul]`. Combine the linear relations using `[re_dot_self_nonneg (∑ p, ((c p : ℝ) : ℂ) • a p)]`.
-/
theorem gram_core {ι₁ ι₂ P : Type} [Fintype ι₁] [Fintype ι₂] [Fintype P] (a : P → ι₁ → ℂ) (A : P → ι₂ → ℂ)
    (s : P → ℝ) (m : ℝ)
    (hA : ∀ p p', star (A p) ⬝ᵥ A p' = (s p : ℂ) * (star (a p) ⬝ᵥ a p'))
    (hm : ∀ p, a p ≠ 0 → m ≤ s p) :
    m * (star (∑ p, a p) ⬝ᵥ ∑ p, a p).re ≤ (star (∑ p, A p) ⬝ᵥ ∑ p, A p).re := by
  set c : P → ℝ := fun p => Real.sqrt (max (s p - m) 0) with hc
  have key : ∀ p p', (s p : ℂ) * (star (a p) ⬝ᵥ a p') =
      ((m : ℂ) + ((c p * c p' : ℝ) : ℂ)) * (star (a p) ⬝ᵥ a p') := by
    intro p p'
    by_cases h0 : star (a p) ⬝ᵥ a p' = 0
    · rw [h0, mul_zero, mul_zero]
    · have hp : a p ≠ 0 := by
        intro h
        apply h0
        simp [h]
      have hs : s p = s p' := by
        have e1 := hA p' p
        have e2 := congrArg star (hA p p')
        rw [dot_conj, star_mul', dot_conj] at e2
        rw [e2] at e1
        have h0' : star (a p') ⬝ᵥ a p ≠ 0 := by
          rw [← dot_conj]
          exact star_ne_zero.mpr h0
        have e3 := mul_right_cancel₀ h0' e1
        have e4 : star ((s p : ℝ) : ℂ) = ((s p : ℝ) : ℂ) := Complex.conj_ofReal _
        rw [e4] at e3
        exact_mod_cast e3
      have hm1 : m ≤ s p := hm p hp
      have hcc : c p * c p' = s p - m := by
        simp only [hc]
        rw [← hs, Real.mul_self_sqrt (le_max_right _ _), max_eq_left (by linarith)]
      rw [hcc]
      push_cast
      ring
  have hL : star (∑ p, A p) ⬝ᵥ ∑ p, A p = ∑ p, ∑ p', (s p : ℂ) * (star (a p) ⬝ᵥ a p') := by
    rw [star_sum_dotProduct_sum]
    simp only [hA]
  have hR : ∑ p, ∑ p', (s p : ℂ) * (star (a p) ⬝ᵥ a p') =
      (m : ℂ) * (star (∑ p, a p) ⬝ᵥ ∑ p, a p) +
        star (∑ p, ((c p : ℝ) : ℂ) • a p) ⬝ᵥ ∑ p, ((c p : ℝ) : ℂ) • a p := by
    rw [star_sum_dotProduct_sum a a, star_sum_dotProduct_sum (fun p => ((c p : ℝ) : ℂ) • a p) (fun p => ((c p : ℝ) : ℂ) • a p)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    rw [key p p', star_ofReal_smul_dotProduct_ofReal_smul]
    push_cast
    ring
  rw [hL, hR, Complex.add_re, Complex.re_ofReal_mul]
  linarith [re_dot_self_nonneg (∑ p, ((c p : ℝ) : ℂ) • a p)]

variable {Bs : DefBase K} {Df : DefSide Bs}

/- English proof (translation)
Establish `hv : Formalism.HermitianLatticesTheory.vecAt b v (∑ p ∈ s, f p) = ∑ p ∈ s, Formalism.HermitianLatticesTheory.vecAt b v (f p)`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.HermitianLatticesTheory.vecAt, map_sum, Finsupp.finset_sum_apply, Finset.sum_apply]`. Unfold `Formalism.HermitianLatticesTheory.fcoord`. Rewrite using `[hv]`.

Use `first`. Consider the case `exact Matrix.mulVec_sum _ _ _`. Consider the case `exact map_sum (Matrix.mulVecLin ((X v)⁻¹)) _ _`.
-/
theorem fcoord_sum {ι V P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (s : Finset P) (f : P → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ p ∈ s, f p) = ∑ p ∈ s, Formalism.HermitianLatticesTheory.fcoord b X v (f p) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (∑ p ∈ s, f p) = ∑ p ∈ s, Formalism.HermitianLatticesTheory.vecAt b v (f p) := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, map_sum, Finsupp.finset_sum_apply, Finset.sum_apply]
  unfold Formalism.HermitianLatticesTheory.fcoord
  rw [hv]
  first
    | exact Matrix.mulVec_sum _ _ _
    | exact map_sum (Matrix.mulVecLin ((X v)⁻¹)) _ _

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]`. Simplify using `only [dotProduct, Complex.re_sum, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Generalize the expression as in `Formalism.HermitianLatticesTheory.fcoord b X v x i = z`.

Rewrite using `[Complex.mul_re]`. Establish `h1 : (star z).re = z.re` using `Complex.conj_re z`. Establish `h2 : (star z).im = -z.im` using `Complex.conj_im z`. Rewrite using `[h1, h2]`. Use `first`.

Consider the case `rw [Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `rw [Complex.sq_abs, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem normAt_sq_eq {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 = (star (Formalism.HermitianLatticesTheory.fcoord b X v x) ⬝ᵥ Formalism.HermitianLatticesTheory.fcoord b X v x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize Formalism.HermitianLatticesTheory.fcoord b X v x i = z
  rw [Complex.mul_re]
  have h1 : (star z).re = z.re := Complex.conj_re z
  have h2 : (star z).im = -z.im := Complex.conj_im z
  rw [h1, h2]
  first
    | rw [Complex.sq_norm, Complex.normSq_apply]; ring
    | rw [Complex.sq_abs, Complex.normSq_apply]; ring
    | rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/- English proof (translation)
Establish `hc : (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')`. Establish `hinv : ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)⁻¹ = ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ))⁻¹ • (X v)⁻¹`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (hX v), smul_smul, inv_mul_cancel₀ hc, one_smul]`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, Formalism.DivisionValues.scaleFrame]`.

Rewrite using `[hinv, Complex.ofReal_inv, inv_inv]`. Use `first`. Consider the case `exact Matrix.smul_mulVec _ _ _`. Consider the case `exact Matrix.smul_mulVec_assoc _ _ _`. Consider the case `(funext i`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc])`.
-/
theorem fcoord_scale {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) (Formalism.DivisionValues.scaleFrame t X) v x =
      ((Real.sqrt (t v) : ℝ) : ℂ) • Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v x := by
  have hc : (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')
  have hinv : ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)⁻¹ = ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ))⁻¹ • (X v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (hX v), smul_smul, inv_mul_cancel₀ hc, one_smul]
  simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.DivisionValues.scaleFrame]
  rw [hinv, Complex.ofReal_inv, inv_inv]
  first
    | exact Matrix.smul_mulVec _ _ _
    | exact Matrix.smul_mulVec_assoc _ _ _
    | (funext i
       simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc])

/- English proof (translation)
Simplify using `only [Formalism.DivisionValues.scaleFrame]`. Rewrite using `[Matrix.det_smul]`. Conclude with `(IsUnit.pow _ (Ne.isUnit (Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')))).mul (hX v)`.
-/
theorem isUnit_scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    IsUnit (Formalism.DivisionValues.scaleFrame t X v).det := by
  simp only [Formalism.DivisionValues.scaleFrame]
  rw [Matrix.det_smul]
  exact (IsUnit.pow _ (Ne.isUnit (Complex.ofReal_ne_zero.mpr
    (inv_ne_zero (Real.sqrt_pos.mpr (ht v)).ne')))).mul (hX v)

/- English proof (translation)
Establish `hκ : ∀ v, 0 < S.κ v` using `hl1c.2.2.1`. Establish `hκi : ∀ v, 0 < (S.κ v)⁻¹` using `fun v => inv_pos.mpr (hκ v)`. Establish `hinj : Function.Injective (S.ι Bs.μ0).mulVecLin` using `(hl1c.1 Bs.μ0).1`. Establish `hq : q ∈ ⨆ p, Df.Qp Bs.μ0 p` using `by rw [wf.Qp_top]; exact Submodule.mem_top`. Choose the witnesses or unpack the hypotheses as in `⟨qp, hqp, hqs⟩ : ∃ qp : Bs.Ix → Fin (Df.dQ Bs.μ0) → K, (∀ p, qp p ∈ Df.Qp Bs.μ0 p) ∧ ∑ p, qp p = q := by`.

Proceed by induction on `hq using Submodule.iSup_induction' with`. Consider the case `mem i y hy`. Use `⟨Pi.single i y, fun j => ?_, by simp⟩` and prove the remaining obligations. Break down `eq_or_ne j i with rfl | h` into its components or cases. Simplify using `using hy`.

Simplify using `[h]`. Consider the case `zero => exact ⟨0, fun _ => Submodule.zero_mem _, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨f1, hf1, rfl⟩` from `hy`. Take `⟨f2, hf2, rfl⟩` from `hz`.

Conclude with `⟨f1 + f2, fun i => Submodule.add_mem _ (hf1 i) (hf2 i), by simp [Finset.sum_add_distrib]⟩`. Establish `hpart : ∀ p, S.Qpart Bs.μ0 p = Df.Qp Bs.μ0 p`. Introduce `p`. Unfold `IndefData.Qpart`. Rewrite using `[← hl1a.1 p]`.

Conclude with `Submodule.comap_map_eq_of_injective hinj _`. Use `set bQ := Pi.basisFun K (Fin (Df.dQ Bs.μ0))`. Use `set bE := Pi.basisFun K (Fin S.D)`. Use `set XE' := Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE`. Use `set a : Bs.Ix → Fin (Df.dQ Bs.μ0) → ℂ := fun p => Formalism.HermitianLatticesTheory.fcoord bQ (Df.XQ Bs.μ0) v (qp p)`.

Use `set A : Bs.Ix → Fin S.D → ℂ := fun p => Formalism.HermitianLatticesTheory.fcoord bE XE' v ((S.ι Bs.μ0).mulVec (qp p))`. Use `set s : Bs.Ix → ℝ := fun p => ∏ j, S.lam j Bs.μ0 p v`. Establish `hA : ∀ p p', star (A p) ⬝ᵥ A p' = (s p : ℂ) * (star (a p) ⬝ᵥ a p')`. Introduce `p p'`. Establish `hsc` using `hl1c.2.2.2.2.1 Bs.μ0 v (Or.inl rfl) p (qp p) (by rw [hpart]; exact hqp p) (qp p')`.

Simplify using `only [A, a, XE']`. Rewrite using `[fcoord_scale _ hκi _ hXE, fcoord_scale _ hκi _ hXE, star_smul, smul_dotProduct, dotProduct_smul]`. Establish `e1 : star (Formalism.HermitianLatticesTheory.fcoord bE S.XE v ((S.ι Bs.μ0).mulVec (qp p))) ⬝ᵥ Formalism.HermitianLatticesTheory.fcoord bE S.XE v ((S.ι Bs.μ0).mulVec (qp p')) = ((S.κ v * ∏ j, S.lam j Bs.μ0 p v : ℝ) : ℂ) * (star (a p) ⬝ᵥ a p')` using `hsc`. Rewrite using `[e1, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul]`. Establish `hsq : ((Real.sqrt (S.κ v)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (S.κ v)⁻¹ : ℝ) : ℂ) = (((S.κ v)⁻¹ : ℝ) : ℂ)`.

Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hκi v).le]`. Establish `hk : (((S.κ v)⁻¹ : ℝ) : ℂ) * ((S.κ v : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, inv_mul_cancel₀ (hκ v).ne', Complex.ofReal_one]`. Simplify using `only [s]`. Move the coercions through the operations in `at hsq hk ⊢`.

Take the linear combination `((S.κ v : ℂ) * (∏ j, (S.lam j Bs.μ0 p v : ℂ)) * (star (a p) ⬝ᵥ a p')) * hsq + ((∏ j, (S.lam j Bs.μ0 p v : ℂ)) * (star (a p) ⬝ᵥ a p')) * hk`. Establish `hm : ∀ p, a p ≠ 0 → Real.exp (g v) ≤ s p`. Introduce `p hap`. Establish `hne : Df.Qp Bs.μ0 p ≠ ⊥`. Introduce `h`.

Apply `hap` to reduce the goal to its premises. Establish `: qp p = 0` using `by have := hqp p; rw [h] at this; exact (Submodule.mem_bot K).mp this`. Establish `hv0 : Formalism.HermitianLatticesTheory.vecAt bQ v (0 : Fin (Df.dQ Bs.μ0) → K) = 0` using `by funext i; simp [Formalism.HermitianLatticesTheory.vecAt]`. Simplify using `only [a, this, Formalism.HermitianLatticesTheory.fcoord, hv0, Matrix.mulVec_zero]`. Establish `h1` using `hg v p hne`.

Establish `hpos : ∀ j, 0 < S.lam j Bs.μ0 p v` using `fun j => hl1c.2.2.2.1 j Bs.μ0 p v`. Combine the equalities or inequalities in the displayed calculation. Establish `hcore` using `gram_core a A s (Real.exp (g v)) hA hm`. Establish `eq1 : Formalism.HermitianLatticesTheory.fcoord bQ (Df.XQ Bs.μ0) v q = ∑ p, a p` using `by rw [← hqs, fcoord_sum]`. Establish `eq2 : Formalism.HermitianLatticesTheory.fcoord bE XE' v ((S.ι Bs.μ0).mulVec q) = ∑ p, A p`.

Rewrite using `[← hqs, Matrix.mulVec_sum, fcoord_sum]`. Rewrite using `[normAt_sq_eq, normAt_sq_eq, eq1, eq2]`. Conclude with `hcore`.
-/
theorem ip_point (wf : Df.WF) (S : IndefData Df) (hl1a : S.BaseTypeSubspacesMapOntoBothSides) (hl1c : S.RowLatticeBoundForBasis) (hXE : ∀ v, IsUnit (S.XE v).det)
    (g : InfinitePlace K → ℝ) (hg : ∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v))
    (v : InfinitePlace K) (q : Fin (Df.dQ Bs.μ0) → K) :
    Real.exp (g v) * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) v q ^ 2 ≤
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin S.D)) (Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE) v
        ((S.ι Bs.μ0).mulVec q) ^ 2 := by
  classical
  have hκ : ∀ v, 0 < S.κ v := hl1c.2.2.1
  have hκi : ∀ v, 0 < (S.κ v)⁻¹ := fun v => inv_pos.mpr (hκ v)
  have hinj : Function.Injective (S.ι Bs.μ0).mulVecLin := (hl1c.1 Bs.μ0).1

  have hq : q ∈ ⨆ p, Df.Qp Bs.μ0 p := by rw [wf.Qp_top]; exact Submodule.mem_top
  obtain ⟨qp, hqp, hqs⟩ : ∃ qp : Bs.Ix → Fin (Df.dQ Bs.μ0) → K, (∀ p, qp p ∈ Df.Qp Bs.μ0 p) ∧ ∑ p, qp p = q := by
    induction hq using Submodule.iSup_induction' with
    | mem i y hy =>
      refine ⟨Pi.single i y, fun j => ?_, by simp⟩
      rcases eq_or_ne j i with rfl | h
      · simpa using hy
      · simp [h]
    | zero => exact ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨f1, hf1, rfl⟩ := hy
      obtain ⟨f2, hf2, rfl⟩ := hz
      exact ⟨f1 + f2, fun i => Submodule.add_mem _ (hf1 i) (hf2 i), by simp [Finset.sum_add_distrib]⟩

  have hpart : ∀ p, S.Qpart Bs.μ0 p = Df.Qp Bs.μ0 p := by
    intro p
    unfold IndefData.Qpart
    rw [← hl1a.1 p]
    exact Submodule.comap_map_eq_of_injective hinj _
  set bQ := Pi.basisFun K (Fin (Df.dQ Bs.μ0))
  set bE := Pi.basisFun K (Fin S.D)
  set XE' := Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE
  set a : Bs.Ix → Fin (Df.dQ Bs.μ0) → ℂ := fun p => Formalism.HermitianLatticesTheory.fcoord bQ (Df.XQ Bs.μ0) v (qp p)
  set A : Bs.Ix → Fin S.D → ℂ := fun p => Formalism.HermitianLatticesTheory.fcoord bE XE' v ((S.ι Bs.μ0).mulVec (qp p))
  set s : Bs.Ix → ℝ := fun p => ∏ j, S.lam j Bs.μ0 p v
  have hA : ∀ p p', star (A p) ⬝ᵥ A p' = (s p : ℂ) * (star (a p) ⬝ᵥ a p') := by
    intro p p'
    have hsc := hl1c.2.2.2.2.1 Bs.μ0 v (Or.inl rfl) p (qp p) (by rw [hpart]; exact hqp p) (qp p')
    simp only [A, a, XE']
    rw [fcoord_scale _ hκi _ hXE, fcoord_scale _ hκi _ hXE, star_smul, smul_dotProduct, dotProduct_smul]
    have e1 : star (Formalism.HermitianLatticesTheory.fcoord bE S.XE v ((S.ι Bs.μ0).mulVec (qp p))) ⬝ᵥ
        Formalism.HermitianLatticesTheory.fcoord bE S.XE v ((S.ι Bs.μ0).mulVec (qp p')) =
        ((S.κ v * ∏ j, S.lam j Bs.μ0 p v : ℝ) : ℂ) * (star (a p) ⬝ᵥ a p') := hsc
    rw [e1, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul]
    have hsq : ((Real.sqrt (S.κ v)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (S.κ v)⁻¹ : ℝ) : ℂ) = (((S.κ v)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hκi v).le]
    have hk : (((S.κ v)⁻¹ : ℝ) : ℂ) * ((S.κ v : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hκ v).ne', Complex.ofReal_one]
    simp only [s]
    push_cast at hsq hk ⊢
    linear_combination ((S.κ v : ℂ) * (∏ j, (S.lam j Bs.μ0 p v : ℂ)) * (star (a p) ⬝ᵥ a p')) * hsq +
      ((∏ j, (S.lam j Bs.μ0 p v : ℂ)) * (star (a p) ⬝ᵥ a p')) * hk
  have hm : ∀ p, a p ≠ 0 → Real.exp (g v) ≤ s p := by
    intro p hap
    have hne : Df.Qp Bs.μ0 p ≠ ⊥ := by
      intro h
      apply hap
      have : qp p = 0 := by have := hqp p; rw [h] at this; exact (Submodule.mem_bot K).mp this
      have hv0 : Formalism.HermitianLatticesTheory.vecAt bQ v (0 : Fin (Df.dQ Bs.μ0) → K) = 0 := by funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
      simp only [a, this, Formalism.HermitianLatticesTheory.fcoord, hv0, Matrix.mulVec_zero]
    have h1 := hg v p hne
    have hpos : ∀ j, 0 < S.lam j Bs.μ0 p v := fun j => hl1c.2.2.2.1 j Bs.μ0 p v
    calc Real.exp (g v) ≤ Real.exp (∑ j, Real.log (S.lam j Bs.μ0 p v)) := Real.exp_le_exp.mpr h1
      _ = s p := by rw [Real.exp_sum]; exact Finset.prod_congr rfl fun j _ => Real.exp_log (hpos j)
  have hcore := gram_core a A s (Real.exp (g v)) hA hm
  have eq1 : Formalism.HermitianLatticesTheory.fcoord bQ (Df.XQ Bs.μ0) v q = ∑ p, a p := by rw [← hqs, fcoord_sum]
  have eq2 : Formalism.HermitianLatticesTheory.fcoord bE XE' v ((S.ι Bs.μ0).mulVec q) = ∑ p, A p := by
    rw [← hqs, Matrix.mulVec_sum, fcoord_sum]
  rw [normAt_sq_eq, normAt_sq_eq, eq1, eq2]
  exact hcore

/- English proof (translation)
Establish `hκ : ∀ v, 0 < S.κ v` using `hl1c.2.2.1`. Establish `hκi : ∀ v, 0 < (S.κ v)⁻¹` using `fun v => inv_pos.mpr (hκ v)`. Establish `hXQ : ∀ v, IsUnit (Df.XQ Bs.μ0 v).det` using `fun v => (wf.XQ_quot Bs.μ0 v).1`. Establish `hXE'` using `isUnit_scaleFrame (fun v => (S.κ v)⁻¹) hκi S.XE hXE`. Use `set bQ := Pi.basisFun K (Fin (Df.dQ Bs.μ0))`.

Use `set bE := Pi.basisFun K (Fin S.D)`. Use `set bn := Pi.basisFun K (Fin n)`. Use `set XE' := Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE`. Use `set vb := Ψ * S.ι Bs.μ0`. Establish `hΨ0 : Matrix.mulVecLin Ψ ≠ 0`.

Introduce `h`. Establish `e : Ψ.mulVec (Pi.single ⟨0, hD⟩ 1) = Ψ.mulVec 0`. Rewrite using `[Matrix.mulVec_zero]`. Conclude with `congrArg (fun f => f (Pi.single ⟨0, hD⟩ (1 : K))) h`. Use `hΨ e` as an intermediate fact.

Establish `h1` using `congrFun this ⟨0, hD⟩`. Simplify using `at h1`. Establish `hpt : ∀ v, Formalism.HN.opNormAt bE XE' bn X' v (Matrix.mulVecLin Ψ) ≤ Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * Real.exp (-(g v) / 2)`. Introduce `v`. Use `Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points bE XE' bn X' hXE' _ v _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) fun y => ?_` and prove the remaining obligations.

Take `⟨q, rfl⟩` from `(hl1c.1 Bs.μ0).2 y`. Establish `h1 : Ψ.mulVec ((S.ι Bs.μ0).mulVec q) = vb.mulVec q` using `Matrix.mulVec_mulVec _ _ _`. Establish `h2` using `Formalism.HN.PlaceOperatorNorms.normAt_map_le bQ (Df.XQ Bs.μ0) bn X' hXQ v (Matrix.mulVecLin vb) q`. Establish `h3` using `ip_point wf S hl1a hl1c hXE g hg v q`. Simplify using `only [Matrix.mulVecLin_apply] at h2 ⊢`.

Rewrite using `[h1]`. Use `set nq := Formalism.HermitianLatticesTheory.normAt bQ (Df.XQ Bs.μ0) v q`. Use `set ny := Formalism.HermitianLatticesTheory.normAt bE XE' v ((S.ι Bs.μ0).mulVec q)`. Establish `hnq : 0 ≤ nq` using `Real.sqrt_nonneg _`. Establish `hny : 0 ≤ ny` using `Real.sqrt_nonneg _`.

Establish `h4 : nq ≤ Real.exp (-(g v) / 2) * ny`. Establish `he : Real.exp (-(g v) / 2) ^ 2 * Real.exp (g v) = 1`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add, show ((2 : ℕ) : ℝ) * (-(g v) / 2) + g v = 0 by push_cast; ring, Real.exp_zero]`. Establish `h5 : nq ^ 2 ≤ (Real.exp (-(g v) / 2) * ny) ^ 2`. Use `mul_le_mul_of_nonneg_left h3 (sq_nonneg (Real.exp (-(g v) / 2)))` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `(pow_le_pow_iff_left₀ hnq (mul_nonneg (Real.exp_pos _).le hny) two_ne_zero).mp h5`. Establish `hop` using `norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X' v)⁻¹ * (LinearMap.toMatrix bQ bn (Matrix.mulVecLin vb)).map v.embedding * Df.XQ Bs.μ0 v)))`. Combine the equalities or inequalities in the displayed calculation. Establish `hlog : ∀ v, Real.log (Formalism.HN.opNormAt bE XE' bn X' v (Matrix.mulVecLin Ψ) ^ 2) ≤ Real.log (Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) ^ 2) - g v`.

Introduce `v`. Establish `hpos` using `Formalism.HN.PlaceOperatorNorms.opNormAt_pos bE XE' bn X' hXE' hX' v _ hΨ0`. Establish `hle` using `hpt v`. Establish `hvb : 0 < Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb)`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `: Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * Real.exp (-(g v) / 2) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Formalism.HN.opNormAt bE XE' bn X' v (Matrix.mulVecLin Ψ) ^ 2 ≤ (Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * Real.exp (-(g v) / 2)) ^ 2` using `pow_le_pow_left₀ hpos.le hle 2`. Establish `h3` using `Real.log_le_log (by positivity) h2`.

Rewrite `h3` using `[mul_pow, Real.log_mul (by positivity) (by positivity), ← Real.exp_nat_mul, Real.log_exp]`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `htMap`. Establish `hn : (Formalism.HN.nPl K : ℝ) ≠ 0`.

Use `Formalism.HN.twist_finrank_eq K` as an intermediate fact. Establish `h0 : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Introduce `h`. Rewrite `this` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmean : meanInf K g = (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, g v`. Unfold `meanInf`. Rewrite using `[Formalism.HN.twist_finrank_eq K]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hmean, ← mul_sub, ← Finset.sum_sub_distrib]`.

Use `mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hlog v) (by positivity)` and prove the remaining obligations.
-/
theorem ip_first [IsTotallyComplex K] (wf : Df.WF) (S : IndefData Df) (hl1a : S.BaseTypeSubspacesMapOntoBothSides) (hl1c : S.RowLatticeBoundForBasis)
    (hXE : ∀ v, IsUnit (S.XE v).det) (hD : 0 < S.D) {n : ℕ} (X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hX' : ∀ v, IsUnit (X' v).det) (Ψ : Matrix (Fin n) (Fin S.D) K) (hΨ : Function.Injective Ψ.mulVec)
    (g : InfinitePlace K → ℝ) (hg : ∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) :
    htMap (Pi.basisFun K (Fin S.D)) (Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE) (Pi.basisFun K (Fin n)) X'
        (Matrix.mulVecLin Ψ) ≤
      htMap (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin n)) X'
        (Matrix.mulVecLin (Ψ * S.ι Bs.μ0)) - meanInf K g := by
  classical
  have hκ : ∀ v, 0 < S.κ v := hl1c.2.2.1
  have hκi : ∀ v, 0 < (S.κ v)⁻¹ := fun v => inv_pos.mpr (hκ v)
  have hXQ : ∀ v, IsUnit (Df.XQ Bs.μ0 v).det := fun v => (wf.XQ_quot Bs.μ0 v).1
  have hXE' := isUnit_scaleFrame (fun v => (S.κ v)⁻¹) hκi S.XE hXE
  set bQ := Pi.basisFun K (Fin (Df.dQ Bs.μ0))
  set bE := Pi.basisFun K (Fin S.D)
  set bn := Pi.basisFun K (Fin n)
  set XE' := Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE
  set vb := Ψ * S.ι Bs.μ0
  have hΨ0 : Matrix.mulVecLin Ψ ≠ 0 := by
    intro h
    have e : Ψ.mulVec (Pi.single ⟨0, hD⟩ 1) = Ψ.mulVec 0 := by
      rw [Matrix.mulVec_zero]; exact congrArg (fun f => f (Pi.single ⟨0, hD⟩ (1 : K))) h
    have := hΨ e
    have h1 := congrFun this ⟨0, hD⟩
    simp at h1
  have hpt : ∀ v, Formalism.HN.opNormAt bE XE' bn X' v (Matrix.mulVecLin Ψ) ≤
      Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * Real.exp (-(g v) / 2) := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points bE XE' bn X' hXE' _ v _
      (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) fun y => ?_
    obtain ⟨q, rfl⟩ := (hl1c.1 Bs.μ0).2 y
    have h1 : Ψ.mulVec ((S.ι Bs.μ0).mulVec q) = vb.mulVec q := Matrix.mulVec_mulVec _ _ _
    have h2 := Formalism.HN.PlaceOperatorNorms.normAt_map_le bQ (Df.XQ Bs.μ0) bn X' hXQ v (Matrix.mulVecLin vb) q
    have h3 := ip_point wf S hl1a hl1c hXE g hg v q
    simp only [Matrix.mulVecLin_apply] at h2 ⊢
    rw [h1]
    set nq := Formalism.HermitianLatticesTheory.normAt bQ (Df.XQ Bs.μ0) v q
    set ny := Formalism.HermitianLatticesTheory.normAt bE XE' v ((S.ι Bs.μ0).mulVec q)
    have hnq : 0 ≤ nq := Real.sqrt_nonneg _
    have hny : 0 ≤ ny := Real.sqrt_nonneg _
    have h4 : nq ≤ Real.exp (-(g v) / 2) * ny := by
      have he : Real.exp (-(g v) / 2) ^ 2 * Real.exp (g v) = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add,
          show ((2 : ℕ) : ℝ) * (-(g v) / 2) + g v = 0 by push_cast; ring, Real.exp_zero]
      have h5 : nq ^ 2 ≤ (Real.exp (-(g v) / 2) * ny) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (Real.exp (-(g v) / 2)))
        nlinarith
      exact (pow_le_pow_iff_left₀ hnq (mul_nonneg (Real.exp_pos _).le hny) two_ne_zero).mp h5
    have hop := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((X' v)⁻¹ * (LinearMap.toMatrix bQ bn (Matrix.mulVecLin vb)).map v.embedding * Df.XQ Bs.μ0 v)))
    calc Formalism.HermitianLatticesTheory.normAt bn X' v (vb.mulVec q)
        ≤ Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * nq := h2
      _ ≤ Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * (Real.exp (-(g v) / 2) * ny) :=
          mul_le_mul_of_nonneg_left h4 hop
      _ = _ := by ring
  have hlog : ∀ v, Real.log (Formalism.HN.opNormAt bE XE' bn X' v (Matrix.mulVecLin Ψ) ^ 2) ≤
      Real.log (Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) ^ 2) - g v := by
    intro v
    have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos bE XE' bn X' hXE' hX' v _ hΨ0
    have hle := hpt v
    have hvb : 0 < Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) := by
      by_contra h
      push Not at h
      have : Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * Real.exp (-(g v) / 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le
      linarith
    have h2 : Formalism.HN.opNormAt bE XE' bn X' v (Matrix.mulVecLin Ψ) ^ 2 ≤
        (Formalism.HN.opNormAt bQ (Df.XQ Bs.μ0) bn X' v (Matrix.mulVecLin vb) * Real.exp (-(g v) / 2)) ^ 2 :=
      pow_le_pow_left₀ hpos.le hle 2
    have h3 := Real.log_le_log (by positivity) h2
    rw [mul_pow, Real.log_mul (by positivity) (by positivity), ← Real.exp_nat_mul, Real.log_exp] at h3
    push_cast at h3
    linarith
  unfold htMap
  have hn : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  have hmean : meanInf K g = (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, g v := by
    unfold meanInf
    rw [Formalism.HN.twist_finrank_eq K]
    field_simp
  rw [hmean, ← mul_sub, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hlog v) (by positivity)

end IPFirst

section Main

variable {Bs : DefBase K} {Df : DefSide Bs}

/- English proof (translation)
Establish `hk : LinearMap.ker (O.vmu Bs.μ0).mulVecLin = Df.U Bs.μ0` using `hker`. Introduce `x y hxy`. Take `⟨a, rfl⟩` from `hι.2 x`. Take `⟨a', rfl⟩` from `hι.2 y`. Take `⟨u, rfl⟩` from `hPq a`.

Take `⟨u', rfl⟩` from `hPq a'`. Establish `h1 : u - u' ∈ LinearMap.ker (O.vmu Bs.μ0).mulVecLin`. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, ← hc0, Matrix.mulVec_sub]`. Simplify using `only [← Matrix.mulVec_mulVec]`. Rewrite using `[hxy, sub_self]`.

Rewrite `h1` using `[hk]`. Express the relevant statement in the definitionally equal form `u - u' ∈ LinearMap.ker (Df.Pq Bs.μ0).mulVecLin at h1`. Rewrite `h1` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero]`. Rewrite using `[h1]`.
-/
theorem psi_inj (S : IndefData Df) (O : FunData K Df) (Ψ : Matrix (Fin O.n) (Fin S.D) K)
    (hc0 : Ψ * S.ι Bs.μ0 * Df.Pq Bs.μ0 = O.vmu Bs.μ0) (hker : LeafKer O)
    (hι : Function.Bijective (S.ι Bs.μ0).mulVec) (hPq : Function.Surjective (Df.Pq Bs.μ0).mulVec) :
    Function.Injective Ψ.mulVec := by
  have hk : LinearMap.ker (O.vmu Bs.μ0).mulVecLin = Df.U Bs.μ0 := hker
  intro x y hxy
  obtain ⟨a, rfl⟩ := hι.2 x
  obtain ⟨a', rfl⟩ := hι.2 y
  obtain ⟨u, rfl⟩ := hPq a
  obtain ⟨u', rfl⟩ := hPq a'
  have h1 : u - u' ∈ LinearMap.ker (O.vmu Bs.μ0).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← hc0, Matrix.mulVec_sub]
    simp only [← Matrix.mulVec_mulVec]
    rw [hxy, sub_self]
  rw [hk] at h1
  change u - u' ∈ LinearMap.ker (Df.Pq Bs.μ0).mulVecLin at h1
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero] at h1
  rw [h1]

/- English proof (translation)
Unfold `Formalism.DivisionValues.vw`. Rewrite using `[FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]`.
-/
theorem vw_one' (w : Pl K) : vw w (1 : K) = 0 := by
  unfold Formalism.DivisionValues.vw
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

/- English proof (translation)
Take `⟨hMfg, hM0, hX', hEM⟩` from `hMM`. Take `⟨Ψ, hΨ⟩` from `hCc`. Take `⟨hFPa, hFPs, hBF⟩` from `hFP`. Take `⟨hIPa, g, hg, hgm⟩` from `hIP`. Take `⟨hr0, hrr, hSe, hdd, hdN, hyy, hcc, hsq⟩` from `hSq`.

Take `⟨hSd, hN0s⟩` from `hN0`. Take `⟨hdl, hBδ, hz⟩` from `hINT`. Take `⟨-, hT, hTd⟩` from `hTHB`. Establish `hκ : ∀ v, 0 < S.κ v` using `hl1c.2.2.1`. Establish `hμ0 : ∏ ij, O.rq Bs.μ0 ij = 1` using `Finset.prod_eq_one fun ij _ => hr0 ij`.

Establish `hc0 : Ψ * S.ι Bs.μ0 * Df.Pq Bs.μ0 = O.vmu Bs.μ0`. Use `hΨ Bs.μ0 (Or.inl rfl)` as an intermediate fact. Rewrite `this` using `[hμ0, inv_one, one_smul]`. Then use the resulting hypothesis. Establish `hInj : Function.Injective Ψ.mulVec` using `psi_inj S O Ψ hc0 hKer (hl1c.1 Bs.μ0) (wf.Pq_surj Bs.μ0)`. Establish `hrne : ∀ w : Pl K, (∏ ij, O.rq (S.μ w) ij) ≠ 0` using `fun w => Finset.prod_ne_zero_iff.mpr fun ij _ => hrr w ij`.

Use `set T : Finset (Pl K) := S.Tw ∪ O.Tf with hTdef`. Use `set a : Pl K → ℤ := fun w => vw w (∏ ij, O.rq (S.μ w) ij) + O.dF w with hadef`. Establish `hloc : ∀ w : Pl K, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (S.RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K))) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (((w.asIdeal : FractionalIdeal (nonZeroDiv …` using `fun w => hence_local w S.RR (S.ι (S.μ w)) (Df.Pq (S.μ w)) (Df.Mt (S.μ w)) Ψ (O.vmu (S.μ w)) O.M _ (hrne w) (O.dF w) (hRRw w) (hΨ _ (Or.inr ⟨w, rfl⟩)) (hFPa w)`. Establish `ha0 : ∀ w : Pl K, w ∉ T → a w = 0`. Introduce `w hw`.

Establish `hw1 : w ∉ S.Tw` using `fun h => hw (Finset.mem_union_left _ h)`. Establish `hw2 : w ∉ O.Tf` using `fun h => hw (Finset.mem_union_right _ h)`. Establish `hμ : S.μ w = Bs.μ0`. Assume the negation of the conclusion as `h`. Conclude with `hw1 ((hH0.2 w).mpr h)`.

Simplify using `only [hadef, hμ, hμ0, vw_one', hFPs w hw2, add_zero]`. Establish `hincl` using `PI.local_global_inclusion' K (Fin O.n → K) (S.RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K))) O.M T a (fun w _ => hloc w) (fun w hw => by`. Use `le_trans (hloc w) (localization_mono _ ?_)` and prove the remaining obligations. Rewrite using `[ha0 w hw, neg_zero, zpow_zero]`. Conclude with `idealSmul_one_le O.M)`.

Establish `hInf : htMap (Pi.basisFun K (Fin S.D)) (Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE) (Pi.basisFun K (Fin O.n)) O.X' (Matrix.mulVecLin Ψ) ≤ O.bIP C b`. Establish `h1` using `ip_first wf S hl1a hl1c hXE hD O.X' hX' Ψ hInj g hg`. Establish `h2` using `hIPa (Ψ * S.ι Bs.μ0) hc0`. Unfold `FunData.bIP`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hBF' : ∑ w ∈ T, lw w * (O.dF w : ℝ) ≤ O.bFP C b / 2`. Establish `e : ∑ w ∈ T, lw w * (O.dF w : ℝ) = ∑ w ∈ O.Tf, lw w * (O.dF w : ℝ)`. Use `(Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm` and prove the remaining obligations. Rewrite using `[hFPs w hw]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set BB := max (O.bArch C b + 6 * O.bDel C b) (O.bTH C x b) with hBB`. Establish `hnorm : ∀ ij, HtLe (fun _ => 0) (O.zA ij) BB ∧ HtLe (fun _ => 0) (O.zA' ij) BB`. Introduce `ij`.

Take `⟨h0, h0', hv⟩` from `hz ij`. Take `⟨hA, hA'⟩` from `hARCH ij`. Use `⟨htLe_mono (Formalism.AtG.norm_height_bound K (O.zA ij) O.dl (O.bDel C b) h0 hdl (fun w => (hv w).1) hBδ) ?_, htLe_mono (Formalism.AtG.norm_height_bound K (O.zA' ij) O.dl (O.bDel C b) h0' hdl (fun w => (hv w).2) hBδ) ?_⟩` and prove the remaining obligations. Conclude with `le_trans (by linarith) (le_max_left _ _)`. Conclude with `le_trans (by linarith) (le_max_left _ _)`.

Establish `hb0 : 0 ≤ b`. Take `⟨hmfN, -⟩` from `hB5`. Establish `: (0 : ℝ) ≤ (O.m : ℝ) * O.f * (O.N : ℝ) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBN0 : 0 ≤ O.bTH C x b`.

Unfold `FunData.bTH`. Establish `: 0 ≤ Real.log b + Real.log x` using `by linarith [Real.log_nonneg hx]`. Establish `: (0 : ℝ) ≤ C` using `by linarith`. Check the signs of the components of the expression. Establish `h` using `Formalism.AtG.height_h0_index_bound K (Fin O.n → K) (Fin O.n) S.D hD S.XE S.κ (Pi.basisFun K (Fin O.n)) O.X' hXE hκ hX' S.RR O.M (Matrix.mulVecLin Ψ) T a (fun w => (O.dF w : ℝ)) (O.EMM C) (O.bIP C b) (O.bFP C b / 2) (x ^ CH) b hRR hMfg hM0 (fun x y hxy => hInj hxy) hincl hEM hInf …`.

Use `show S.muMaxRR ≤ N.hh - meanLog S.κ`. Rewrite using `[hhh]`. Unfold `IndefData.muMaxRR`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem functional_lower_bound_of_conditions [IsTotallyComplex K] (wf : Df.WF) (S : IndefData Df) (N : IndefNum Bs) (O : FunData K Df)
    (C x CH b : ℝ)
    (hD : 0 < S.D) (hH0 : S.H0) (hl1a : S.BaseTypeSubspacesMapOntoBothSides) (hl1c : S.RowLatticeBoundForBasis) (hXE : ∀ v, IsUnit (S.XE v).det)
    (hRR : Submodule.IsLattice K S.RR)
    (hRRw : ∀ w : Pl K, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))))
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hL1 : 1 ≤ Real.log b) (hLx : Real.log b + Real.log x ≤ 3 * Real.log b)
    (hhh : N.hh = x ^ CH * b)
    (hMM : LeafMM O C) (hCc : LeafC S O) (hKer : LeafKer O) (hFP : LeafFP O S.μ C b) (hIP : LeafIP S O C b)
    (hSq : LeafOneSquare O S.μ C b) (hN0 : PrimeCountingSumBound O C x b) (hINT : LeafINT O C b) (hARCH : LeafARCH O C b)
    (hTHB : LeafTHB O C x b) (hH1 : leafHypothesesConst O) (hH7 : LatticeConstantBound O b) (hB5 : DegreeAndSizeBounds O C b) (hB7 : PrimePowerModuliSumBound O C b)
    (hCS : LeafCS O b) (hWt : LeafWt O C b) (hPol : LeafPol O C x CH b) :
    S.FUN N := by
  classical
  obtain ⟨hMfg, hM0, hX', hEM⟩ := hMM
  obtain ⟨Ψ, hΨ⟩ := hCc
  obtain ⟨hFPa, hFPs, hBF⟩ := hFP
  obtain ⟨hIPa, g, hg, hgm⟩ := hIP
  obtain ⟨hr0, hrr, hSe, hdd, hdN, hyy, hcc, hsq⟩ := hSq
  obtain ⟨hSd, hN0s⟩ := hN0
  obtain ⟨hdl, hBδ, hz⟩ := hINT
  obtain ⟨-, hT, hTd⟩ := hTHB
  have hκ : ∀ v, 0 < S.κ v := hl1c.2.2.1
  have hμ0 : ∏ ij, O.rq Bs.μ0 ij = 1 := Finset.prod_eq_one fun ij _ => hr0 ij
  have hc0 : Ψ * S.ι Bs.μ0 * Df.Pq Bs.μ0 = O.vmu Bs.μ0 := by
    have := hΨ Bs.μ0 (Or.inl rfl); rwa [hμ0, inv_one, one_smul] at this
  have hInj : Function.Injective Ψ.mulVec :=
    psi_inj S O Ψ hc0 hKer (hl1c.1 Bs.μ0) (wf.Pq_surj Bs.μ0)

  have hrne : ∀ w : Pl K, (∏ ij, O.rq (S.μ w) ij) ≠ 0 := fun w => Finset.prod_ne_zero_iff.mpr fun ij _ => hrr w ij
  set T : Finset (Pl K) := S.Tw ∪ O.Tf with hTdef
  set a : Pl K → ℤ := fun w => vw w (∏ ij, O.rq (S.μ w) ij) + O.dF w with hadef
  have hloc : ∀ w : Pl K, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (S.RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) O.M) := fun w =>
    hence_local w S.RR (S.ι (S.μ w)) (Df.Pq (S.μ w)) (Df.Mt (S.μ w)) Ψ (O.vmu (S.μ w)) O.M _ (hrne w) (O.dF w)
      (hRRw w) (hΨ _ (Or.inr ⟨w, rfl⟩)) (hFPa w)
  have ha0 : ∀ w : Pl K, w ∉ T → a w = 0 := by
    intro w hw
    have hw1 : w ∉ S.Tw := fun h => hw (Finset.mem_union_left _ h)
    have hw2 : w ∉ O.Tf := fun h => hw (Finset.mem_union_right _ h)
    have hμ : S.μ w = Bs.μ0 := by
      by_contra h; exact hw1 ((hH0.2 w).mpr h)
    simp only [hadef, hμ, hμ0, vw_one', hFPs w hw2, add_zero]
  have hincl := PI.local_global_inclusion' K (Fin O.n → K) (S.RR.map ((Matrix.mulVecLin Ψ).restrictScalars (𝓞 K))) O.M
    T a (fun w _ => hloc w) (fun w hw => by
      refine le_trans (hloc w) (localization_mono _ ?_)
      rw [ha0 w hw, neg_zero, zpow_zero]
      exact idealSmul_one_le O.M)

  have hInf : htMap (Pi.basisFun K (Fin S.D)) (Formalism.DivisionValues.scaleFrame (fun v => (S.κ v)⁻¹) S.XE)
      (Pi.basisFun K (Fin O.n)) O.X' (Matrix.mulVecLin Ψ) ≤ O.bIP C b := by
    have h1 := ip_first wf S hl1a hl1c hXE hD O.X' hX' Ψ hInj g hg
    have h2 := hIPa (Ψ * S.ι Bs.μ0) hc0
    unfold FunData.bIP
    linarith

  have hBF' : ∑ w ∈ T, lw w * (O.dF w : ℝ) ≤ O.bFP C b / 2 := by
    have e : ∑ w ∈ T, lw w * (O.dF w : ℝ) = ∑ w ∈ O.Tf, lw w * (O.dF w : ℝ) := by
      refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
      rw [hFPs w hw]; simp
    rw [e]; linarith

  set BB := max (O.bArch C b + 6 * O.bDel C b) (O.bTH C x b) with hBB
  have hnorm : ∀ ij, HtLe (fun _ => 0) (O.zA ij) BB ∧ HtLe (fun _ => 0) (O.zA' ij) BB := by
    intro ij
    obtain ⟨h0, h0', hv⟩ := hz ij
    obtain ⟨hA, hA'⟩ := hARCH ij
    refine ⟨htLe_mono (Formalism.AtG.norm_height_bound K (O.zA ij) O.dl (O.bDel C b) h0 hdl (fun w => (hv w).1) hBδ) ?_,
      htLe_mono (Formalism.AtG.norm_height_bound K (O.zA' ij) O.dl (O.bDel C b) h0' hdl (fun w => (hv w).2) hBδ) ?_⟩
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_left _ _)
  have hb0 : 0 ≤ b := by
    obtain ⟨hmfN, -⟩ := hB5
    have : (0 : ℝ) ≤ (O.m : ℝ) * O.f * (O.N : ℝ) ^ 2 := by positivity
    linarith
  have hBN0 : 0 ≤ O.bTH C x b := by
    unfold FunData.bTH
    have : 0 ≤ Real.log b + Real.log x := by linarith [Real.log_nonneg hx]
    have : (0 : ℝ) ≤ C := by linarith
    positivity
  have h := Formalism.AtG.height_h0_index_bound K (Fin O.n → K) (Fin O.n) S.D hD S.XE S.κ (Pi.basisFun K (Fin O.n)) O.X' hXE hκ hX'
    S.RR O.M (Matrix.mulVecLin Ψ) T a (fun w => (O.dF w : ℝ)) (O.EMM C) (O.bIP C b) (O.bFP C b / 2) (x ^ CH) b
    hRR hMfg hM0 (fun x y hxy => hInj hxy) hincl hEM hInf hBF' O.Sq O.m O.N O.dl O.Sd O.Se O.N0
    (fun w => O.rq (S.μ w)) O.zA O.zA' O.zT O.zTd O.gT O.ch O.dd O.hd O.yy O.S0 O.cc (O.ee C b) O.qq BB (O.bTH C x b)
    (O.bDel C b) (fun w _ => by simp [hadef]) hdl hSd (fun ij s h1 h2 => (hN0s ij s h1 h2).1) hSe hrr hdd hdN
    (fun ij => by have := hyy ij; omega) hcc (fun w _ ij => hsq w ij) hnorm
    (fun ij s => htLe_mono (hT ij s) (le_max_right _ _)) (fun ij c s => htLe_mono (hTd ij c s) (le_max_right _ _))
    hBN0 (fun ij s h1 h2 => (hN0s ij s h1 h2).2) hBδ (size_le O C x CH b hC hx hL1 hLx hH1 hB5 hB7 hCS hWt hPol)
  show S.muMaxRR ≤ N.hh - meanLog S.κ
  rw [hhh]
  unfold IndefData.muMaxRR
  linarith

/- English proof (translation)
The claim follows from `functional_lower_bound_of_conditions wf S (Z.num C₀ CH) O C Z.x CH Z.b hD hH0 hl1a hl1c hXE hRR hRRw hC hx hL1 hLx rfl hMM hCc hKer hFP hIP hSq hN0 hINT hARCH hTHB hH1 hH7 hB5 hB7 hCS hWt hPol`.
-/
theorem functional_lower_bound_of_conditions_numeric [IsTotallyComplex K] (wf : Df.WF) (S : IndefData Df) (Z : IndefScale Bs) (C₀ CH : ℝ)
    (O : FunData K Df) (C : ℝ)
    (hD : 0 < S.D) (hH0 : S.H0) (hl1a : S.BaseTypeSubspacesMapOntoBothSides) (hl1c : S.RowLatticeBoundForBasis) (hXE : ∀ v, IsUnit (S.XE v).det)
    (hRR : Submodule.IsLattice K S.RR)
    (hRRw : ∀ w : Pl K, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))))
    (hC : 1 ≤ C) (hx : 1 ≤ Z.x) (hL1 : 1 ≤ Real.log Z.b) (hLx : Real.log Z.b + Real.log Z.x ≤ 3 * Real.log Z.b)
    (hMM : LeafMM O C) (hCc : LeafC S O) (hKer : LeafKer O) (hFP : LeafFP O S.μ C Z.b) (hIP : LeafIP S O C Z.b)
    (hSq : LeafOneSquare O S.μ C Z.b) (hN0 : PrimeCountingSumBound O C Z.x Z.b) (hINT : LeafINT O C Z.b)
    (hARCH : LeafARCH O C Z.b) (hTHB : LeafTHB O C Z.x Z.b) (hH1 : leafHypothesesConst O) (hH7 : LatticeConstantBound O Z.b)
    (hB5 : DegreeAndSizeBounds O C Z.b) (hB7 : PrimePowerModuliSumBound O C Z.b) (hCS : LeafCS O Z.b) (hWt : LeafWt O C Z.b)
    (hPol : LeafPol O C Z.x CH Z.b) :
    S.FUN (Z.num C₀ CH) :=
  functional_lower_bound_of_conditions wf S (Z.num C₀ CH) O C Z.x CH Z.b hD hH0 hl1a hl1c hXE hRR hRRw hC hx hL1 hLx rfl
    hMM hCc hKer hFP hIP hSq hN0 hINT hARCH hTHB hH1 hH7 hB5 hB7 hCS hWt hPol

end Main

end Formalism.L2.Indef.Tree
