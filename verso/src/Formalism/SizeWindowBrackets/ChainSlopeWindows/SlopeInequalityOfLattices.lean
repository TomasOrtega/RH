import Formalism.SizeWindowBrackets.SlopeHypothesesRounded
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

section Real

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)

/- English proof (authored)
Expand both exponent totals and distribute the factor of two across the sum over the indices. For each index the assumed place-sum identity equates the two summands. Summing gives the equality of totals.
-/
theorem exponent_transfer : BridgeEe D P := by
  intro hI u0 u
  unfold Data.Ee PData.Ee UnitWeightPartition.Ee
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (hI u0 u).2.2 j

/- English proof (authored)
The lower and upper weighted slope bounds apply to the local data. Use the place-sum identities to replace the gain, positive correction and exponent by their global counterparts. The upper bound remains valid after adding the nonnegative size allowance. For the lower bound, the local index parameter is nonnegative because twice it is a sum of nonnegative local terms. The coefficient is at least four, so four times this parameter is at most the coefficient times the global index bound. Replace the other two local losses by their size bounds and collect the error terms.
-/
theorem unit_weight_transfer : QuotientSlopeBoundsOfPlaceSums D C Xpp P := by
  intro hH hI hS u0 u
  obtain ⟨hLow, hLow2, hHigh⟩ := hH u0 u
  obtain ⟨hGa, hFo, -⟩ := hI u0 u
  obtain ⟨h4, hB, hsz⟩ := hS
  obtain ⟨hIO, hLT, hRX⟩ := hsz u0 u
  have hEe := exponent_transfer D P hI u0 u
  have lo := UnitWeightPartition.lower_bound_simplified _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLow hLow2
  have hi := UnitWeightPartition.claimHigh_valid _ _ _ _ _ _ _ _ _ _ _ hHigh
  have hIOp : 0 ≤ (P u0 u).IOp := by
    have h1 : UnitWeightPartition.IO (P u0 u).S (P u0 u).l (P u0 u).io = 2 * (P u0 u).IOp := hLow2.2.2.2.2.2.2.1
    have h2 : 0 ≤ UnitWeightPartition.IO (P u0 u).S (P u0 u).l (P u0 u).io :=
      Finset.sum_nonneg fun w hw =>
        mul_nonneg (mul_nonneg (by norm_num) (hLow.1 w hw)) (hLow.2.2.2.2.2.2.2.1 w hw)
    linarith
  rw [hGa, hFo, hEe]
  unfold PData.Ga PData.Fo PData.Ee
  constructor
  · have h0 : 0 ≤ C.cSl1 * (m : ℝ) * D.B0 := by
      rw [mul_assoc]; exact mul_nonneg (by linarith) hB
    linarith
  · unfold Lo5
    have h1 : 4 * (P u0 u).IOp ≤ C.cSl1 * D.IO u0 :=
      calc 4 * (P u0 u).IOp ≤ C.cSl1 * (P u0 u).IOp := mul_le_mul_of_nonneg_right h4 hIOp
        _ ≤ C.cSl1 * D.IO u0 := mul_le_mul_of_nonneg_left hIO (by linarith)
    linarith

end Real

section Prim

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m)

/- English proof (authored)
The degree formula bounds the normalized deficit by twice f divided by T, and the lower bound on T makes this at most one half. Apply the truncated-length estimate with this deficit, using the equality of the truncated weights with log(T). Group the local index contributions by prime to get the stated total. These supply the numerical hypotheses for the two lower-slope estimates. The upper-slope hypotheses are the given pointwise gain and slope bounds.
-/
theorem primitive_transfer : BridgePrim D Q := by
  intro h u0 u
  obtain ⟨hl, hdM, hT2, hT4, hdu, hsub, htauT, htau, hio, hG1, hT5, hlam, hlT, hsg, hRd, hmu, hmax,
    hMu, hMaxMu, hTa, hsmall, hmap, hfib, hiop⟩ := h u0 u
  obtain ⟨d1, d2, d3, d4⟩ := UnitWeightPartition.deficit_bounds f (D.T u0 u) (Q u0 u).dM (Q u0 u).du hdM hT2 hdu
  have hTpos : 0 < D.T u0 u := by linarith
  have hhalf : 2 * (f : ℝ) / D.T u0 u ≤ 1 / 2 := by
    rw [div_le_iff₀ hTpos]; linarith
  have hPT := UnitWeightPartition.truncatedLength_bound (Q u0 u).ST (Q u0 u).l (Q u0 u).len (Q u0 u).dM (Q u0 u).du
    (1 - (Q u0 u).du / (Q u0 u).dM) (Q u0 u).lam (D.T u0 u) (fun w hw => hl w (hsub hw)) hdM d2
    (le_trans d4 hhalf) d1 hlam hT5 hlT
  have hU := UnitWeightPartition.unit_weight_partition (Q u0 u).S (Q u0 u).Pr (Q u0 u).pr (Q u0 u).l (Q u0 u).io
    (Q u0 u).iop hmap hfib hiop
  exact ⟨⟨hl, hdM, d2, d3, d1, hsub, htauT, hio, hG1, hPT, hRd, hmu⟩,
    ⟨hMu, d4, hhalf, htau, hTa, hsmall, hU, le_refl _, le_refl _⟩,
    ⟨hl, hsg, hmax, hMaxMu⟩⟩

/- English proof (authored)
The logarithm of T is nonnegative under the lower bound on T. Multiply the bound on the truncation parameter by four and compare the resulting coefficient with the slope-loss coefficient times the nonnegative size factor. Multiplying by log(T) gives the required truncated-length budget. The index and rounding bounds are inherited from the assumptions.
-/
theorem primitive_transfer_sizes : BridgePrimSizes D C Xpp cT Q := by
  intro hT h
  obtain ⟨h4, hcT, hB, hab, hsz⟩ := h
  refine ⟨h4, hB, fun u0 u => ?_⟩
  obtain ⟨hIO, hlam, hRd⟩ := hsz u0 u
  refine ⟨hIO, ?_, hRd⟩
  have hlog : 0 ≤ Real.log (D.T u0 u) := Real.log_nonneg (by linarith [hT u0 u])
  have hX : 0 ≤ D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
    mul_nonneg (mul_nonneg (by unfold Data.nT; positivity) (by positivity)) hab
  have h1 : 4 * (Q u0 u).lam ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') := by
    have := mul_le_mul_of_nonneg_right hcT hX
    nlinarith
  exact mul_le_mul_of_nonneg_right h1 hlog

/- English proof (authored)
First transfer the primitive conditions to the local slope hypotheses. Transfer the size bounds as well, using the lower bound on T from the primitive conditions. The place-sum identities now allow the transfer theorem to give both quotient slope bounds.
-/
theorem unit_weight_of_primitive : QuotientSlopeBoundsOfPrimitiveData D C Xpp cT Q := by
  intro hH hI hS
  exact unit_weight_transfer D C Xpp (toP D Q) (primitive_transfer D Q hH) hI
    (primitive_transfer_sizes D C Xpp cT Q (fun u0 u => (hH u0 u).2.2.1) hS)

end Prim

section Round

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
  (Ru : ∀ u0, W u0 → ℝ)

end Round

/- English proof (authored)
Apply the lattice slope formulas expressed in local indices and lengths. The finite set S contains the supports of both integer exponent functions, and their contributions outside S vanish. On S, substitute the scaled local weight and divide the two exponents by the same positive ramification factor. This identifies the exponent sum with the weighted gain minus the threshold. The error sum is also supported on S. Substituting the normalized length and threshold identifies each local error term with its contribution to the weighted length sum. Replacing the two sums in the slope formulas yields the stated slope comparison.
-/
theorem slope_formula_transfer : LatticeSlopeComparison := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX σ τ M N β hM hM0 hN hrk hβ S eR l sg' tau len hoff he hl hsg
    htau hlen
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨-, -, h1, h2⟩ := slopeLatticeData.slope_via_lengths K V ι b X hX σ τ M N β hM hM0 hN hrk hβ
  have hd : (rkK M : ℝ) ≠ 0 := by exact_mod_cast (slopeLatticeData.rkK_pos hM0).ne'
  have hSg : slopeLatticeData.sgSum σ τ = UnitWeightPartition.Sg S l sg' tau := by
    unfold slopeLatticeData.sgSum UnitWeightPartition.Sg
    have hsub : σ.support ∪ τ.support ⊆ S := by
      intro w hw
      by_contra hS
      obtain ⟨a, b', -⟩ := hoff w hS
      rcases Finset.mem_union.1 hw with h | h
      · exact (Finsupp.mem_support_iff.1 h) a
      · exact (Finsupp.mem_support_iff.1 h) b'
    have hstep : ∑ w ∈ σ.support ∪ τ.support, 2 * slopeLatticeData.ell w * ((σ w : ℝ) - (τ w : ℝ))
        = ∑ w ∈ S, 2 * slopeLatticeData.ell w * ((σ w : ℝ) - (τ w : ℝ)) := by
      refine Finset.sum_subset hsub fun w _ hw => ?_
      rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hw
      rw [hw.1, hw.2]; simp
    refine Eq.trans ?_ (hstep.trans ?_)
    · exact Finset.sum_congr (by congr) fun _ _ => rfl
    · refine Finset.sum_congr rfl fun w hw => ?_
      have := (he w hw).ne'
      rw [hl w hw, hsg w hw, htau w hw]
      field_simp
  have hBe : ∑ᶠ w : slopeLatticeData.FinPl K, 2 * slopeLatticeData.ell w * β w = UnitWeightPartition.BeSum S l (rkK M : ℝ) len tau := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · unfold UnitWeightPartition.BeSum UnitWeightPartition.be
      refine Finset.sum_congr rfl fun w hw => ?_
      have := (he w hw).ne'
      rw [hl w hw, hlen w hw, htau w hw]
      field_simp
      ring
    · intro w hw
      by_contra hS
      rw [Function.mem_support, (hoff w hS).2.2, mul_zero] at hw
      exact hw rfl
  rw [← hSg, ← hBe]
  exact ⟨h1, h2⟩

section F

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

/- English proof (authored)
Expand the slope conclusion, the error function and its logarithmic factor. The two resulting inequalities differ only in the association of the product of four, the spread and the logarithm. Pack the seven side assumptions into their conjunction in one direction and unpack them in the other.
-/
theorem function_transfer : BridgeF D := by
  have e : ∀ a b : ℝ, 4 * a * b = 4 * (a * b) := fun a b => mul_assoc 4 a b
  unfold BridgeF Data.SlopeIneq SideF ConclFAt PhiMonotonicityLemmas.ConclF PhiMonotonicityLemmas.ErrF PhiMonotonicityLemmas.phi
  constructor
  · rintro h u0 ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have := h u0 h1 h2 h3 h4 h5 h6 h7
    rwa [e] at this
  · intro h u0 h1 h2 h3 h4 h5 h6 h7
    have := h u0 ⟨h1, h2, h3, h4, h5, h6, h7⟩
    rwa [e]

/- English proof (authored)
The identification hypotheses express the weights as ranks and the means and maximal slopes as those of the given lattices. The positive total rank lets the weighted mean identity be cleared of its denominator. Each positive-rank lattice's mean is at most its maximal slope. Subtract the height and bound that value by the maximum of all shifted maximal slopes. Zero-rank terms contribute zero to the mean, so the weighted mean is at most the shifted maximum and the spread is nonnegative. By definition that spread bounds each shifted maximal slope relative to the mean. The side conditions give the ambient minimal-slope comparison and height bound.
-/
theorem lattice_numerics (u0 : U0) {K Wd κ κ₁ : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    {V ι : W u0 → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ)
    (hId : LatIdent D u0 b' X' cc b X N)
    (hG : MatrixLatticeEstimates.LatGeom b' X' cc b X N B (D.h u0) v Y Y' Ball (D.del u0))
    (hSide : SideF D u0) :
    MatrixLatticeEstimates.LatNum b' X' cc b X N (D.h u0) (D.s u0) (D.uF u0) (D.HH u0) := by
  obtain ⟨hd, hmuN, hmuMax, hcc, hmin⟩ := hId
  obtain ⟨-, -, -, -, -, s6, s7⟩ := hSide
  have hpos : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by
    exact_mod_cast hG.2.2.2.2.2.2.2.2.1
  have hs : D.s u0 = (∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - D.h u0 i))
      / ∑ i, (Fintype.card (ι i) : ℝ) := by
    unfold Data.s wmean
    simp only [hd, hmuN]
  have hle : ∀ i, muMaxDef (b i) (X i) (N i) - D.h u0 i ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) := by
    intro i
    have := Finset.le_sup' (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) (Finset.mem_univ i)
    rw [← hmuMax i]
    exact this
  refine ⟨?_, ?_, ?_, ?_, s7.le⟩
  · rw [hs, div_mul_cancel₀ _ hpos.ne']
  · unfold Data.uF
    rw [sub_nonneg, hs, div_le_iff₀ hpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm _ (Fintype.card (ι i) : ℝ)]
    rcases Nat.eq_zero_or_pos (Fintype.card (ι i)) with h0 | h0
    · rw [h0]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 := MatrixLatticeEstimates.slope_le_max_slope (b i) (X i) (hG.2.1 i) (N i) (hG.2.2.2.2.2.2.1 i)
        (hG.2.2.2.2.2.2.2.1 i) h0
      have h2 := hle i
      linarith
  · intro i
    have h2 := hle i
    unfold Data.uF
    linarith
  · rw [← hmin]; exact s6

/- English proof (authored)
Use the lattice identifications and the side conditions to obtain the numerical lattice assumptions. Apply the ramified lattice estimate with these and the geometric and compression hypotheses. Replace the ambient slope and the error parameters by the identified quantities from the data. The error expression agrees with the stated function estimate by the conclusion transfer.
-/
theorem function_slope_transfer : BridgeFS D := by
  intro u0 K Wd κ κ₁ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B v Y Y' Ball γ ιf _ _
    Bf Vr Dstar sg η0 η1 e0 de hyp hSide
  obtain ⟨hId, hG, hγ, hBV, hV, hD, hsg, hsg20, hR, h0, h0', h1, he0, hse, hde, hde4, hcor, hS, hη,
    he⟩ := hyp
  have hN := lattice_numerics D u0 b' X' cc b X N B v Y Y' Ball hId hG hSide
  have h := MatrixLatticeEstimates.joint_a_ramified_holds K Wd κ κ₁ (W u0) V ι b' X' cc b X N B (D.h u0) v Y Y' Ball γ ιf Bf
    Vr (D.s u0) (D.uF u0) (D.HH u0) (D.del u0) Dstar sg η0 η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR
    h0 h0' h1 he0 hse hde hde4 hcor hS
  unfold ConclFAt
  rw [hId.2.2.2.1, hη, he]
  exact (MatrixLatticeEstimates.transfer_conclusion_holds _ _ _ _ _ _ _ _).1 h

end F

section SizeData₂

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (P : ∀ u0, W u0 → PData ι m)
  (Q : ∀ u0, W u0 → PPrim ι m)

end SizeData₂

namespace Model

def l0 : Fin 3 → ℝ := ![Real.log 2, Real.log 3, Real.log 211]
def gain0 : Fin 1 → Fin 3 → ℝ := fun _ => ![1, 0, 0]
def F0 : Fin 1 → Fin 3 → ℝ := fun _ _ => 1 / 2
def E0 : Fin 1 → Fin 3 → ℝ := fun _ _ => 1 / 4
def tau0 : Fin 3 → ℝ := ![1 / 2, 0, 0]
def io0 : Fin 3 → ℝ := ![1 / 10, 0, 0]
def len0 : Fin 3 → ℝ := ![3 / 5, 0, 1 / 20]
def sg0 : Fin 3 → ℝ := fun w => UnitWeightPartition.sgw Finset.univ gain0 F0 E0 w - ![1 / 10, 0, 0] w
def iop0 : ℕ → ℝ := fun p => if p = 2 then 1 / 10 else 0
def pr0 : Fin 3 → ℕ := ![2, 3, 211]
def SgV : ℝ := UnitWeightPartition.Sg Finset.univ l0 sg0 tau0
def BeV : ℝ := UnitWeightPartition.BeSum Finset.univ l0 1 len0 tau0
def RdV : ℝ := ∑ w : Fin 3, 2 * l0 w * (UnitWeightPartition.sgw Finset.univ gain0 F0 E0 w - sg0 w)
def IOV : ℝ := ∑ p ∈ ({2, 3, 211} : Finset ℕ), Real.log (p : ℝ) * iop0 p
def EeV : ℝ := 2 * ∑ w : Fin 3, l0 w * E0 0 w

def Q0 (μ0 μ1 : ℝ) : PPrim (Fin 3) 1 where
  S := Finset.univ
  ST := {2}
  l := l0
  gain := gain0
  F := F0
  E := E0
  tau := tau0
  io := io0
  len := len0
  sg' := sg0
  dM := 210 / 209
  du := 1
  muMu := μ0 - SgV + BeV
  muMaxMu := μ1 - SgV
  Rd := RdV
  lam := 1 / 20
  Pr := {2, 3, 211}
  pr := pr0
  iop := iop0

def sV (μ0 : ℝ) (h : Fin 20 → ℝ) : ℝ := wmean (fun _ : Fin 20 => (1 : ℝ)) (fun u => μ0 - h u)
def HHV (μ0 μ2 : ℝ) (h : Fin 20 → ℝ) : ℝ := |sV μ0 h - μ2| + 1
def muMV (μ0 : ℝ) : ℝ := (μ0 - SgV + BeV) + 1 * Real.log (211 - 1) / (211 - 2)
def FoV : ℝ := UnitWeightPartition.Fo Finset.univ Finset.univ l0 F0
def LaV (μ0 μ1 : ℝ) (h : Fin 20 → ℝ) : ℝ := |muMV μ0| + |μ1 - SgV| + 2 * ∑ u, |h u|
def NcV (μ0 : ℝ) (h : Fin 20 → ℝ) : ℝ := |μ0| + ∑ u, |h u| + |FoV| + 1 + Real.log 211

def D1 (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : Data Unit (fun _ => Fin 20) Unit 1 1 where
  x := HHV μ0 μ2 h
  ε := 0
  a := 1
  b := 1
  b' := 0
  k := 1
  L := Real.log 211
  La := LaV μ0 μ1 h
  B0 := |EeV|
  Nc := NcV μ0 h
  gam := 0
  LpL := 0
  v := Real.pi
  lg := 0
  logGam := 0
  aT := fun _ => 1
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 211
  muN := fun _ _ => μ0
  muMaxN := fun _ _ => μ1
  h := fun _ => h
  muM := fun _ _ => muMV μ0
  muMaxM := fun _ _ => μ1 - SgV
  EeJ := fun _ _ _ => EeV
  muCC := fun _ => μ0
  muMinCC := fun _ => μ2
  Fo := fun _ => FoV
  Ga := fun _ => UnitWeightPartition.Ga Finset.univ Finset.univ l0 gain0 tau0
  Ta := fun _ => UnitWeightPartition.Ta Finset.univ l0 tau0
  ASK := fun _ => UnitWeightPartition.Ga Finset.univ Finset.univ l0 gain0 tau0
  IO := fun _ => IOV
  HH := fun _ => HHV μ0 μ2 h
  del := fun _ => 0
  η := fun _ => 5 * (1 / 20) + 3 * Real.sqrt 0
  e := fun _ => 2 * 0
  delBar := 0
  etaBar := 1 / 4
  eBar := 0

def C2 : Consts := ⟨1, 1, 1, 1, 1, 1, 4, |IOV|, 1, 1⟩

end Model

namespace Model

/- English proof (authored)
The summand at u occurs in the full finite sum. Every other absolute-value term is nonnegative, so the full sum is at least that summand.
-/
theorem sum_abs_ge (h : Fin 20 → ℝ) (u : Fin 20) : |h u| ≤ ∑ u, |h u| :=
  Finset.single_le_sum (f := fun u => |h u|) (fun _ _ => abs_nonneg _) (Finset.mem_univ u)

/- English proof (authored)
Each summand is an absolute value and is nonnegative. Therefore their finite sum is nonnegative.
-/
theorem sum_abs_nonneg (h : Fin 20 → ℝ) : 0 ≤ ∑ u, |h u| :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/- English proof (authored)
The quantity is a sum of two absolute values and twice a sum of absolute values. All three terms are nonnegative.
-/
theorem LaV_nonneg (μ0 μ1 : ℝ) (h : Fin 20 → ℝ) : 0 ≤ LaV μ0 μ1 h := by
  have := sum_abs_nonneg h
  unfold LaV; positivity

/- English proof (authored)
The height is one plus an absolute value. Since the absolute value is nonnegative, the height is positive.
-/
theorem HHV_pos (μ0 μ2 : ℝ) (h : Fin 20 → ℝ) : 0 < HHV μ0 μ2 h := by
  unfold HHV; positivity

/- English proof (authored)
Insert the explicit model data and constants. The height is positive, the normalized weights and degree parameters are one, and the metric scale is π > 0. The normalized maximal and mean slopes satisfy the required ordering by μ₀ ≤ μ₁. The remaining parameter bounds reduce to the stated constants and zeros.
-/
theorem setting (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) (hμ : μ0 ≤ μ1) : (D1 μ0 μ1 μ2 h).HidaSetting C2 := by
  refine ⟨HHV_pos μ0 μ2 h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => hμ, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [D1, C2, Real.pi_pos]

/- English proof (authored)
In the model all window weights are one and the metric scale is π, so the logarithmic window factors vanish. Substitute the remaining definitions. Bound the model's mean parameter and the chosen height shift above by their absolute values, and bound the negative of the positive correction by its absolute value. These terms occur in the model budget, and its other error allowances are nonnegative. This gives the divisor inequality.
-/
theorem div' (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).DIV C2 := by
  intro u0 u
  have h1 := le_abs_self μ0
  have h2 := (le_abs_self (h u)).trans (sum_abs_ge h u)
  have h3 := neg_abs_le FoV
  have h4 := LaV_nonneg μ0 μ1 h
  have h5 := abs_nonneg EeV
  simp [D1, C2, Data.nT, Data.logOm, ph, Real.pi_ne_zero, NcV]
  linarith

/- English proof (authored)
After substituting the model data, the varying part of the height expression is the difference of two shifts. Its absolute value is at most the sum of their absolute values, and each is bounded by the sum over all twenty shifts. The model allowance includes twice that sum and only adds nonnegative terms, giving the height comparison.
-/
theorem hcomp (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).HComp C2 := by
  intro u0 u u'
  have h1 := sum_abs_ge h u
  have h2 := sum_abs_ge h u'
  have h3 : |h u - h u'| ≤ |h u| + |h u'| := abs_sub _ _
  have h5 := abs_nonneg EeV
  have h6 := abs_nonneg (muMV μ0)
  have h7 := abs_nonneg (μ1 - SgV)
  simp [D1, C2, Data.nT, LaV]
  linarith

/- English proof (authored)
Each word has count 211, independent of the word. In the lower bound the logarithmic weight terms vanish because the window weights are one and the scale is π, leaving a nonpositive expression bounded by log(211). The model's upper bound contains log(211) itself. The logarithmic difference between any two words is zero, so the variation bound also holds.
-/
theorem count (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : Count5 (D1 μ0 μ1 μ2 h) C2 := by
  intro u0 u
  have h4 := LaV_nonneg μ0 μ1 h
  have h5 : 0 ≤ Real.log 211 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [D1, C2, Real.pi_ne_zero]
    linarith
  · simp [D1, C2]
  · intro u'
    simp [D1, C2]

/- English proof (authored)
Substitute the model values for the two reference slopes and the slope budget. The budget includes the absolute values of the reference mean and maximal slope and a nonnegative sum of absolute shifts. The lower and upper slope comparisons follow from bounding a real number below by the negative of its absolute value and above by its absolute value.
-/
theorem slopes (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).Slopes C2 := by
  intro u0 u
  have h1 := sum_abs_nonneg h
  have h6 := neg_abs_le (muMV μ0)
  have h6' := abs_nonneg (muMV μ0)
  have h7 := le_abs_self (μ1 - SgV)
  have h7' := abs_nonneg (μ1 - SgV)
  constructor
  · simp [D1, C2, Data.nT, LaV]
    linarith
  · simp [D1, C2, Data.nT, LaV]
    linarith

/- English proof (authored)
The gain and the positive correction agree directly with the chosen local place sums. For the exponent there is only one index, so identify it with the unique index zero and substitute the defining local exponent sum.
-/
theorem ident (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) :
    PlaceSumIdentities (D1 μ0 μ1 μ2 h) (toP (D1 μ0 μ1 μ2 h) (fun _ _ => Q0 μ0 μ1)) := by
  intro u0 u
  refine ⟨rfl, rfl, fun j => ?_⟩
  have : j = 0 := Subsingleton.elim _ _
  subst this
  rfl

/- English proof (authored)
The model constants and nonnegative budget terms give the fixed size constraints by substitution. The index comparison is an equality. The truncation scale 1/20 lies below its numerical upper bound. Finally, the rounding term is at most its absolute value, which is at most four times that absolute value.
-/
theorem sizes (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) :
    SizesPrim (D1 μ0 μ1 μ2 h) C2 |RdV| 1 (fun _ _ => Q0 μ0 μ1) := by
  refine ⟨le_refl _, by norm_num [C2], by simp [D1], by simp [D1], fun u0 u => ⟨le_refl _, ?_, ?_⟩⟩
  · simp [D1, Q0, Data.nT]; norm_num
  · have h1 := le_abs_self RdV
    have h2 := abs_nonneg RdV
    show RdV ≤ 4 * |RdV|
    linarith

end Model

end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
