import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointMemEndLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLatticeScalingIndexStatement

noncomputable section

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `: (r : E) ≠ 0` using `by exact_mod_cast hr`. Simplify using `only [trProj, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_trProj (hr : r ≠ 0) (Y : Matrix (Fin r) (Fin r) E) : (trProj Y).trace = 0 := by
  have : (r : E) ≠ 0 := by exact_mod_cast hr
  simp only [trProj, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  field_simp; ring

/- English proof (translation)
Take `⟨-, -, -, -, -, -, h7, h8⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hG hd`. Rewrite using `[← h7, (h8 Z).1 hZ, trace_neg]`.
-/
theorem cc_trace_of_isSkew {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : IsSkew G Z) : cc Z.trace = -Z.trace := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [← h7, (h8 Z).1 hZ, trace_neg]

/- English proof (translation)
Take `⟨-, -, h3, h4, h5, -, -, h8⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hG hd`. Rewrite using `[h8, sub_eq_add_neg, h3, ← neg_smul, h4, h5, (h8 Z).1 hZ]`. Establish `e : cc (-c) = c` using `by simp only [cc, map_neg] at hc ⊢; rw [hc, neg_neg]`. Rewrite using `[e, neg_add, neg_smul, neg_neg]`.
-/
theorem isSkew_sub_smul {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : IsSkew G Z) {c : E} (hc : cc c = -c) : IsSkew G (Z - c • 1) := by
  obtain ⟨-, -, h3, h4, h5, -, -, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [h8, sub_eq_add_neg, h3, ← neg_smul, h4, h5, (h8 Z).1 hZ]
  have e : cc (-c) = c := by simp only [cc, map_neg] at hc ⊢; rw [hc, neg_neg]
  rw [e, neg_add, neg_smul, neg_neg]

/- English proof (translation)
Simplify using `only [cc, map_div₀, map_natCast] at h ⊢`. Rewrite using `[h, neg_div]`.
-/
theorem cc_trace_div {Z : Matrix (Fin r) (Fin r) E} (h : cc Z.trace = -Z.trace) :
    cc (Z.trace / r) = -(Z.trace / r) := by
  simp only [cc, map_div₀, map_natCast] at h ⊢
  rw [h, neg_div]

/- English proof (translation)
Use `⟨trace_trProj hr Z, isSkew_sub_smul hS.1 hS.2.1 hZ.1 (cc_trace_div (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)), fun X hX => ?_⟩` and prove the remaining obligations. Establish `h1 : (X * trProj Z).trace = (X * Z).trace`. Simplify using `only [trProj, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, hX.1, smul_zero, sub_zero]`. Rewrite using `[h1]`. Conclude with `GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hX.2.2 hZ.2)`.
-/
theorem trProj_mem_dualLie (hr : r ≠ 0) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ skewLat G Λ) : trProj Z ∈ dualLie G Λ := by
  refine ⟨trace_trProj hr Z, isSkew_sub_smul hS.1 hS.2.1 hZ.1 (cc_trace_div
    (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)), fun X hX => ?_⟩
  have h1 : (X * trProj Z).trace = (X * Z).trace := by
    simp only [trProj, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, hX.1,
      smul_zero, sub_zero]
  rw [h1]
  exact GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hX.2.2 hZ.2)

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Take `⟨-, -, h3, h4, -, -, -, -⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hG hd`. Rewrite using `[sub_eq_add_neg, h3, ← neg_one_smul E Z, h4, sub_eq_add_neg, ← neg_one_smul E (hAdj G Z)]`. Use `congr 2`. Simplify using `[cc]`.
-/
theorem hAdj_sub {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (Y Z : Matrix (Fin r) (Fin r) E) : hAdj G (Y - Z) = hAdj G Y - hAdj G Z := by
  obtain ⟨-, -, h3, h4, -, -, -, -⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [sub_eq_add_neg, h3, ← neg_one_smul E Z, h4, sub_eq_add_neg, ← neg_one_smul E (hAdj G Z)]
  congr 2
  simp [cc]

/- English proof (translation)
Take `⟨-, h2, -, -, -, -, h7, h8⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hG hd`. Establish `hY' : Y = -hAdj G Y` using `by rw [(h8 Y).1 hY, neg_neg]`. Use `conv_lhs => rw [hY']`. Rewrite using `[Matrix.neg_mul, ← h2, trace_neg, h7, trace_mul_comm W Y]`.
-/
theorem trace_mul_hAdj {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Y : Matrix (Fin r) (Fin r) E} (hY : IsSkew G Y) (W : Matrix (Fin r) (Fin r) E) :
    (Y * hAdj G W).trace = -cc (Y * W).trace := by
  obtain ⟨-, h2, -, -, -, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  have hY' : Y = -hAdj G Y := by rw [(h8 Y).1 hY, neg_neg]
  conv_lhs => rw [hY']
  rw [Matrix.neg_mul, ← h2, trace_neg, h7, trace_mul_comm W Y]

/- English proof (translation)
Take `⟨-, -, -, h4, -, h6, h7, h8⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1`. Use `GlobalTheory.T.integral_of_trace_integral_unramified E hU _ fun a ha => ?_` and prove the remaining obligations. Use `set X := a • Z - hAdj G (a • Z) with hXdef`. Establish `hX : X ∈ lieLat G Λ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[trace_sub, h7, trace_smul, hZ0, smul_zero, sub_eq_zero]`. Simplify using `[cc]`. Use `show IsSkew G X`. Rewrite using `[h8, hXdef, hAdj_sub hS.1 hS.2.1, h6, neg_sub]`. Conclude with `(endLat Λ).sub_mem (smul_mem_endLat ha hZ) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat ha hZ))`.

Establish `h` using `hY.2.2 X hX`. Rewrite `h` using `[trace_mul_comm, hXdef, Matrix.mul_sub, trace_sub, trace_mul_hAdj hS.1 hS.2.1 hY.2.1, Matrix.mul_smul, trace_smul, smul_eq_mul, sub_neg_eq_add]`. Apply the tactic sequence `convert h using 2 <;> ring_nf`.
-/
theorem isIntegral_trace_mul_of_trace_eq_zero (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) {Y : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ dualLie G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ endLat Λ) (hZ0 : Z.trace = 0) :
    IsIntegral ℤ (Y * Z).trace := by
  obtain ⟨-, -, -, h4, -, h6, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  refine GlobalTheory.T.integral_of_trace_integral_unramified E hU _ fun a ha => ?_
  set X := a • Z - hAdj G (a • Z) with hXdef
  have hX : X ∈ lieLat G Λ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [trace_sub, h7, trace_smul, hZ0, smul_zero, sub_eq_zero]; simp [cc]
    · show IsSkew G X
      rw [h8, hXdef, hAdj_sub hS.1 hS.2.1, h6, neg_sub]
    · exact (endLat Λ).sub_mem (smul_mem_endLat ha hZ) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat ha hZ))
  have h := hY.2.2 X hX
  rw [trace_mul_comm, hXdef, Matrix.mul_sub, trace_sub, trace_mul_hAdj hS.1 hS.2.1 hY.2.1,
    Matrix.mul_smul, trace_smul, smul_eq_mul, sub_neg_eq_add] at h
  convert h using 2 <;> ring_nf

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, h7, -⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hG hd`. Rewrite using `[h7, hZ]`. Simplify using `[cc]`.
-/
theorem trace_hAdj_one {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : Z.trace = 1) : (hAdj G Z).trace = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [h7, hZ]; simp [cc]

/- English proof (translation)
Take `⟨-, -, h3, h4, h5, -, h7, h8⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1`. Take `⟨Z₁, hZ₁, hZ₁1⟩` from `GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS`. Use `set c₀ := -(Y * Z₁).trace with hc₀`. Establish `hb : ∀ Z ∈ endLat Λ, IsIntegral ℤ ((Y * Z).trace + c₀ * Z.trace)`. Introduce `Z hZ`.

Establish `hZt` using `GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ`. Establish `hm : Z - Z.trace • Z₁ ∈ endLat Λ` using `(endLat Λ).sub_mem hZ (smul_mem_endLat hZt hZ₁)`. Establish `h0 : (Z - Z.trace • Z₁).trace = 0`. Rewrite using `[trace_sub, trace_smul, hZ₁1, smul_eq_mul, mul_one, sub_self]`. Use `isIntegral_trace_mul_of_trace_eq_zero hU hS hY hm h0` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_sub, Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hc₀]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : IsIntegral ℤ (c₀ + cc c₀)`.

Use `hb _ (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ Z₁ hS hZ₁)` as an intermediate fact. Rewrite `this` using `[trace_mul_hAdj hS.1 hS.2.1 hY.2.1, trace_hAdj_one hS.1 hS.2.1 hZ₁1, mul_one]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hc₀]`. Simplify using `only [cc, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht, ht1⟩` from `GlobalTheory.T.exists_integral_trace_one_unramified E hU`. Use `set s := c₀ + cc c₀ with hsdef`. Use `set c := c₀ - s * t with hcdef`. Establish `hccs : cc s = s` using `by rw [hsdef]; simp only [cc, map_add, IsCMField.complexConj_apply_apply]; ring`.

Establish `hcc : cc c = -c`. Establish `e1 : cc c = cc c₀ - s * cc t`. Rewrite using `[hcdef]`. Simplify using `only [cc, map_sub, map_mul] at hccs ⊢`. Rewrite using `[hccs]`.

Rewrite using `[e1, hcdef]`. Establish `e2 : cc t = 1 - t` using `by rw [← ht1]; ring`. Rewrite using `[e2, hsdef]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Y + c • 1, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[h8, h3, h4, h5, (h8 Y).1 hY.2.1, hcc, neg_add, neg_smul]`. Use `GlobalTheory.T.mem_end_lattice_of_trace_dual E r G Λ _ hS fun Z hZ => ?_` and prove the remaining obligations. Establish `e : ((Y + c • 1) * Z).trace = ((Y * Z).trace + c₀ * Z.trace) - s * t * Z.trace`. Rewrite using `[Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, hcdef]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `(hb Z hZ).sub ((hs.mul ht).mul (GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ))`. Establish `hrE : (r : E) ≠ 0` using `by exact_mod_cast hr`. Simplify using `only [trProj, trace_add, hY.1, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, zero_add]`. Rewrite using `[mul_div_assoc, div_self hrE, mul_one, add_sub_cancel_right]`.
-/
theorem exists_skewLat_trProj_eq (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) {Y : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ dualLie G Λ) : ∃ Z ∈ skewLat G Λ, trProj Z = Y := by
  obtain ⟨-, -, h3, h4, h5, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
  set c₀ := -(Y * Z₁).trace with hc₀

  have hb : ∀ Z ∈ endLat Λ, IsIntegral ℤ ((Y * Z).trace + c₀ * Z.trace) := by
    intro Z hZ
    have hZt := GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ
    have hm : Z - Z.trace • Z₁ ∈ endLat Λ := (endLat Λ).sub_mem hZ (smul_mem_endLat hZt hZ₁)
    have h0 : (Z - Z.trace • Z₁).trace = 0 := by
      rw [trace_sub, trace_smul, hZ₁1, smul_eq_mul, mul_one, sub_self]
    have := isIntegral_trace_mul_of_trace_eq_zero hU hS hY hm h0
    rw [Matrix.mul_sub, Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul] at this
    convert this using 1; rw [hc₀]; ring

  have hs : IsIntegral ℤ (c₀ + cc c₀) := by
    have := hb _ (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ Z₁ hS hZ₁)
    rw [trace_mul_hAdj hS.1 hS.2.1 hY.2.1, trace_hAdj_one hS.1 hS.2.1 hZ₁1, mul_one] at this
    convert this using 1
    rw [hc₀]; simp only [cc, map_neg]; ring
  obtain ⟨t, ht, ht1⟩ := GlobalTheory.T.exists_integral_trace_one_unramified E hU
  set s := c₀ + cc c₀ with hsdef
  set c := c₀ - s * t with hcdef
  have hccs : cc s = s := by rw [hsdef]; simp only [cc, map_add, IsCMField.complexConj_apply_apply]; ring
  have hcc : cc c = -c := by
    have e1 : cc c = cc c₀ - s * cc t := by
      rw [hcdef]; simp only [cc, map_sub, map_mul] at hccs ⊢; rw [hccs]
    rw [e1, hcdef]
    have e2 : cc t = 1 - t := by rw [← ht1]; ring
    rw [e2, hsdef]; ring
  refine ⟨Y + c • 1, ⟨?_, ?_⟩, ?_⟩
  · rw [h8, h3, h4, h5, (h8 Y).1 hY.2.1, hcc, neg_add, neg_smul]
  · refine GlobalTheory.T.mem_end_lattice_of_trace_dual E r G Λ _ hS fun Z hZ => ?_
    have e : ((Y + c • 1) * Z).trace = ((Y * Z).trace + c₀ * Z.trace) - s * t * Z.trace := by
      rw [Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, hcdef]; ring
    rw [e]
    exact (hb Z hZ).sub ((hs.mul ht).mul (GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ))
  · have hrE : (r : E) ≠ 0 := by exact_mod_cast hr
    simp only [trProj, trace_add, hY.1, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, zero_add]
    rw [mul_div_assoc, div_self hrE, mul_one, add_sub_cancel_right]

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def trProjHom (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    skewLat G Λ →+ Matrix (Fin r) (Fin r) E where
  toFun Z := trProj (Z : Matrix (Fin r) (Fin r) E)
  map_zero' := by simp [trProj]
  map_add' Y Z := by
    simp only [trProj, AddSubgroup.coe_add, trace_add, add_div, add_smul]; abel

def traceHom (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : skewLat G Λ →+ E where
  toFun Z := (Z : Matrix (Fin r) (Fin r) E).trace
  map_zero' := by simp
  map_add' Y Z := by simp [trace_add]

/- English proof (translation)
Establish `hrE : (r : E) ≠ 0` using `by exact_mod_cast hr`. Establish `hD` using `trProj_mem_dualLie hr hS hZ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hm : (Z.trace / r) • (1 : Matrix (Fin r) (Fin r) E) ∈ endLat Λ`.

Use `(endLat Λ).sub_mem hZ.2 h.2.2` as an intermediate fact. Simplify `this` using `[trProj]`. Take `⟨Z₁, hZ₁, hZ₁1⟩` from `GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS`. Establish `hi : IsIntegral ℤ (Z.trace / r)`. Use `GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hm hZ₁)` as an intermediate fact.

Rewrite `this` using `[Matrix.smul_mul, Matrix.one_mul, trace_smul, hZ₁1, smul_eq_mul, mul_one]`. Then use the resulting hypothesis. Use `⟨Z.trace / r, ⟨hi, cc_trace_div (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [AddMonoidHom.coe_mulLeft]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨b, hb, hbe⟩`.

Simplify using `only [AddMonoidHom.coe_mulLeft] at hbe`. Establish `e : trProj Z = Z - b • (1 : Matrix (Fin r) (Fin r) E)`. Rewrite using `[trProj, ← hbe, mul_div_cancel_left₀ _ hrE]`. Use `⟨hD.1, hD.2.1, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `(endLat Λ).sub_mem hZ.2 (smul_mem_endLat hb.1 one_mem_endLat)`.
-/
theorem trProj_mem_lieLat_iff (hr : r ≠ 0) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ skewLat G Λ) :
    trProj Z ∈ lieLat G Λ ↔ Z.trace ∈ AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E) := by
  have hrE : (r : E) ≠ 0 := by exact_mod_cast hr
  have hD := trProj_mem_dualLie hr hS hZ
  constructor
  · intro h
    have hm : (Z.trace / r) • (1 : Matrix (Fin r) (Fin r) E) ∈ endLat Λ := by
      have := (endLat Λ).sub_mem hZ.2 h.2.2
      simpa [trProj] using this
    obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
    have hi : IsIntegral ℤ (Z.trace / r) := by
      have := GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hm hZ₁)
      rwa [Matrix.smul_mul, Matrix.one_mul, trace_smul, hZ₁1, smul_eq_mul, mul_one] at this
    refine ⟨Z.trace / r, ⟨hi, cc_trace_div (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft]
    field_simp
  · rintro ⟨b, hb, hbe⟩
    simp only [AddMonoidHom.coe_mulLeft] at hbe
    have e : trProj Z = Z - b • (1 : Matrix (Fin r) (Fin r) E) := by
      rw [trProj, ← hbe, mul_div_cancel_left₀ _ hrE]
    refine ⟨hD.1, hD.2.1, ?_⟩
    rw [e]
    exact (endLat Λ).sub_mem hZ.2 (smul_mem_endLat hb.1 one_mem_endLat)

/- English proof (translation)
Take `⟨-, -, -, -, -, h6, h7, h8⟩` from `GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1`. Take `⟨Z₁, hZ₁, hZ₁1⟩` from `GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS`. Take `⟨t, ht, ht1⟩` from `GlobalTheory.T.exists_integral_trace_one_unramified E hU`. Establish `hbt : IsIntegral ℤ (b * t)` using `hb.1.mul ht`. Use `⟨(b * t) • Z₁ - hAdj G ((b * t) • Z₁), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[h8, hAdj_sub hS.1 hS.2.1, h6, neg_sub]`. Conclude with `(endLat Λ).sub_mem (smul_mem_endLat hbt hZ₁) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat hbt hZ₁))`. Rewrite using `[trace_sub, h7, trace_smul, hZ₁1, smul_eq_mul, mul_one]`. Establish `hb2` using `hb.2`. Simplify using `only [cc, map_mul] at hb2 ⊢`.

Rewrite using `[hb2]`. Establish `e2 : IsCMField.complexConj E t = 1 - t`. Use `ht1` as an intermediate fact. Simplify using `only [cc] at this`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem traceHom_surj (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {b : E} (hb : b ∈ imLat E) : ∃ Z ∈ skewLat G Λ, Z.trace = b := by
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
  obtain ⟨t, ht, ht1⟩ := GlobalTheory.T.exists_integral_trace_one_unramified E hU
  have hbt : IsIntegral ℤ (b * t) := hb.1.mul ht
  refine ⟨(b * t) • Z₁ - hAdj G ((b * t) • Z₁), ⟨?_, ?_⟩, ?_⟩
  · rw [h8, hAdj_sub hS.1 hS.2.1, h6, neg_sub]
  · exact (endLat Λ).sub_mem (smul_mem_endLat hbt hZ₁) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat hbt hZ₁))
  · rw [trace_sub, h7, trace_smul, hZ₁1, smul_eq_mul, mul_one]
    have hb2 := hb.2
    simp only [cc, map_mul] at hb2 ⊢
    rw [hb2]
    have e2 : IsCMField.complexConj E t = 1 - t := by
      have := ht1; simp only [cc] at this; rw [← this]; ring
    rw [e2]; ring

/- English proof (translation)
Set `f : skewLat G Λ →+ dualLie G Λ` to `(trProjHom G Λ).codRestrict (dualLie G Λ) fun Z => trProj_mem_dualLie hr hS Z.2`. Set `g : skewLat G Λ →+ imLat E` to `(traceHom G Λ).codRestrict (imLat E) fun Z => ⟨GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS Z.2.2, cc_trace_of_isSkew hS.1 hS.2.1 Z.2.1⟩`. Establish `hf : Function.Surjective f`. Introduce and unpack `⟨Y, hY⟩`. Take `⟨Z, hZ, e⟩` from `exists_skewLat_trProj_eq hr hU hS hY`.

Conclude with `⟨⟨Z, hZ⟩, Subtype.ext e⟩`. Establish `hg : Function.Surjective g`. Introduce and unpack `⟨b, hb⟩`. Take `⟨Z, hZ, e⟩` from `traceHom_surj hr hU hS hb`. Conclude with `⟨⟨Z, hZ⟩, Subtype.ext e⟩`.

Unfold `AddSubgroup.relIndex`. Rewrite using `[← AddSubgroup.index_comap_of_surjective _ hf, ← AddSubgroup.index_comap_of_surjective _ hg]`. Use `congr 1`. Use extensionality with `Z`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]`.

Conclude with `trProj_mem_lieLat_iff hr hS Z.2`.
-/
theorem relIndex_lieLat_dualLie (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) :
    (lieLat G Λ).relIndex (dualLie G Λ) =
      (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) := by
  let f : skewLat G Λ →+ dualLie G Λ :=
    (trProjHom G Λ).codRestrict (dualLie G Λ) fun Z => trProj_mem_dualLie hr hS Z.2
  let g : skewLat G Λ →+ imLat E :=
    (traceHom G Λ).codRestrict (imLat E) fun Z =>
      ⟨GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS Z.2.2, cc_trace_of_isSkew hS.1 hS.2.1 Z.2.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨Z, hZ, e⟩ := exists_skewLat_trProj_eq hr hU hS hY
    exact ⟨⟨Z, hZ⟩, Subtype.ext e⟩
  have hg : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨Z, hZ, e⟩ := traceHom_surj hr hU hS hb
    exact ⟨⟨Z, hZ⟩, Subtype.ext e⟩
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ hf, ← AddSubgroup.index_comap_of_surjective _ hg]
  congr 1
  ext Z
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
  exact trProj_mem_lieLat_iff hr hS Z.2

end GlobalTheory.LieDisc

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

/- English proof (translation)
Introduce `E _ _ _ r G Λ hr hU hS`. Establish `hr0 : r ≠ 0` using `by omega`. Rewrite using `[LieDisc.closure_dualLie, LieDisc.relIndex_lieLat_dualLie hr0 hU hS]`. Conclude with `GlobalTheory.T.imaginary_lattice_scaling_index E r hU (by omega)`.
-/
theorem lieLat_relIndex_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ →
    (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
      ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  intro E _ _ _ r G Λ hr hU hS
  have hr0 : r ≠ 0 := by omega
  rw [LieDisc.closure_dualLie, LieDisc.relIndex_lieLat_dualLie hr0 hU hS]
  exact GlobalTheory.T.imaginary_lattice_scaling_index E r hU (by omega)

end GlobalTheory
