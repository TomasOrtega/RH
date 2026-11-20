import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianPairingOntoInverseIdealAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

def SameAt (v : GlobalTheory.FinPl.Pl D) (𝔞 𝔟 : FI D) : Prop := ∀ s ∈ idAt D (· = v), s ∈ idV 𝔞 v ↔ s ∈ idV 𝔟 v

/- English proof (translation)
Establish `h3` using `(GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.2.1 𝔞 1 one_ne_zero s`. Rewrite `h3` using `[FractionalIdeal.spanSingleton_one, one_mul]`. Conclude with `(h3.1 hs).2`.
-/
theorem mem_idAt_of_idV {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔞 : FI D}
    {s : AE D} (hs : s ∈ idV 𝔞 v) : s ∈ idAt D (· = v) := by
  have h3 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.2.1 𝔞 1 one_ne_zero s
  rw [FractionalIdeal.spanSingleton_one, one_mul] at h3
  exact (h3.1 hs).2

/- English proof (translation)
Introduce `s hs`. Establish `h2` using `(GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1`. Rewrite using `[← h2 _ _ ha hb s hs, ← h2 _ _ ha' hb' s hs]`. Prove the components needed by the constructor for the conclusion. Introduce `h a haV`.

Establish `haA` using `mem_idAt_of_idV hψ haV`. Conclude with `(h𝔟 _ (Ideal.mul_mem_left _ s haA)).1 (h a ((h𝔞 a haA).2 haV))`. Introduce `h a haV`. Establish `haA` using `mem_idAt_of_idV hψ haV`. Conclude with `(h𝔟 _ (Ideal.mul_mem_left _ s haA)).2 (h a ((h𝔞 a haA).1 haV))`.
-/
theorem sameAt_div {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔞 𝔞' 𝔟 𝔟' : FI D}
    (ha : 𝔞 ≠ 0) (ha' : 𝔞' ≠ 0) (hb : 𝔟 ≠ 0) (hb' : 𝔟' ≠ 0) (h𝔞 : SameAt v 𝔞 𝔞') (h𝔟 : SameAt v 𝔟 𝔟') :
    SameAt v (𝔟 * 𝔞⁻¹) (𝔟' * 𝔞'⁻¹) := by
  intro s hs
  have h2 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1
  rw [← h2 _ _ ha hb s hs, ← h2 _ _ ha' hb' s hs]
  constructor
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    exact (h𝔟 _ (Ideal.mul_mem_left _ s haA)).1 (h a ((h𝔞 a haA).2 haV))
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    exact (h𝔟 _ (Ideal.mul_mem_left _ s haA)).2 (h a ((h𝔞 a haA).1 haV))

/- English proof (translation)
Introduce `s hs` and use `(h1 s hs).trans (h2 s hs)`.
-/
theorem sameAt_trans {v : GlobalTheory.FinPl.Pl D} {𝔞 𝔟 𝔠 : FI D} (h1 : SameAt v 𝔞 𝔟) (h2 : SameAt v 𝔟 𝔠) : SameAt v 𝔞 𝔠 :=
  fun s hs => (h1 s hs).trans (h2 s hs)

/- English proof (translation)
Introduce `_ _` and use `Iff.rfl`.
-/
theorem sameAt_refl (v : GlobalTheory.FinPl.Pl D) (𝔞 : FI D) : SameAt v 𝔞 𝔞 := fun _ _ => Iff.rfl

/- English proof (translation)
Establish `h1 : SameAt v (1 * 1⁻¹) (1 * 𝔫⁻¹)` using `sameAt_div hψ one_ne_zero hn one_ne_zero one_ne_zero h (sameAt_refl v 1)`. Establish `h2` using `sameAt_div hψ (by simp) (by simpa using hn) hc hc h1 (sameAt_refl v 𝔠)`. Simplify using `using h2`.
-/
theorem sameAt_mul_of_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔠 𝔫 : FI D}
    (hc : 𝔠 ≠ 0) (hn : 𝔫 ≠ 0) (h : SameAt v 1 𝔫) : SameAt v 𝔠 (𝔠 * 𝔫) := by
  have h1 : SameAt v (1 * 1⁻¹) (1 * 𝔫⁻¹) :=
    sameAt_div hψ one_ne_zero hn one_ne_zero one_ne_zero h (sameAt_refl v 1)
  have h2 := sameAt_div hψ (by simp) (by simpa using hn) hc hc h1 (sameAt_refl v 𝔠)
  simpa using h2

def col {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : Fin S.rank → D.host.E := fun k => d.e k i

/- English proof (translation)
Use function extensionality and compare the values at `k`. Both sides reduce to the same expression.
-/
theorem colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    colMul d.jX i a = a • ratV (col d i) := by
  funext k
  rfl

/- English proof (translation)
Introduce `h`. Establish `h' : ∀ k, d.e k i = 0` using `fun k => congrFun h k`. Use `congrFun (congrFun d.e'e i) i` as an intermediate fact. Simplify using `[Matrix.mul_apply, h'] at this`.
-/
theorem col_ne_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : col d i ≠ 0 := by
  intro h
  have h' : ∀ k, d.e k i = 0 := fun k => congrFun h k
  have := congrFun (congrFun d.e'e i) i
  simp [Matrix.mul_apply, h'] at this

/- English proof (translation)
Introduce `h`. Apply `hζ.2` to reduce the goal to its premises. Rewrite using `[← o.isoB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `: o.iB *ᵥ ζ = 0` using `h`. Rewrite using `[this, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]`.
-/
theorem vecB_ne_zero {S₀ A L : HSp D} (o : OrthDec S₀ A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) :
    vecB o ζ ≠ 0 := by
  intro h
  apply hζ.2
  rw [← o.isoB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have : o.iB *ᵥ ζ = 0 := h
  rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem smul_colMul' {m n : ℕ} (x : Mx D m n) (i : Fin n) (s t : AE D) : s • colMul x i t = colMul x i (s * t) := by
  funext k
  simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Introduce `a ha`. Take `⟨-, h2, -, -, -, -, h7⟩` from `GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v`. Establish `hAA : (D.host.AA : FI D) ≠ 0` using `GlobalTheory.CuspCharLattice.host_AA_ne_zero _`. Rewrite using `[← h𝔢 a ha, ← colMul_jX, hG.cols i a ha, h7]`. Establish `e : 𝔟 * (D.host.AA : FI D) = 𝔟 * ((D.host.AA : FI D)⁻¹)⁻¹` using `by rw [inv_inv]`.

Rewrite using `[e, ← h2 _ _ (inv_ne_zero hAA) h𝔟0 a ha]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ t ht`. Establish `htA` using `mem_idAt_of_idV hψ ht`. Establish `h'` using `h t ht`.

Rewrite `h'` using `[smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha)]`. Rewrite using `[mul_comm]`. Conclude with `h'`. Introduce `h`. Use `⟨fun k => Ideal.mul_mem_right _ _ ha, fun t ht => ?_⟩` and prove the remaining obligations.

Establish `htA` using `mem_idAt_of_idV hψ ht`. Rewrite using `[smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha), mul_comm]`. Conclude with `h t ht`.
-/
theorem cols_sameAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : GlobalTheory.FinPl.Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (i : Fin ρ) {𝔢 𝔟 : FI D} (h𝔟0 : 𝔟 ≠ 0)
    (h𝔢 : ∀ a ∈ idAt D (· = v), a • ratV (col B.d i) ∈ latV B.V LV (· = v) ↔ a ∈ idV 𝔢 v)
    (h𝔟 : ∀ a ∈ idAt D (· = v), a • ratV (col J.d i) ∈ latV J.W LW (· = v) ↔ a ∈ idV 𝔟 v) :
    SameAt v 𝔢 (𝔟 * (D.host.AA : FI D)) := by
  intro a ha
  obtain ⟨-, h2, -, -, -, -, h7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hAA : (D.host.AA : FI D) ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  rw [← h𝔢 a ha, ← colMul_jX, hG.cols i a ha, h7]
  have e : 𝔟 * (D.host.AA : FI D) = 𝔟 * ((D.host.AA : FI D)⁻¹)⁻¹ := by rw [inv_inv]
  rw [e, ← h2 _ _ (inv_ne_zero hAA) h𝔟0 a ha]
  constructor
  · rintro ⟨-, h⟩ t ht
    have htA := mem_idAt_of_idV hψ ht
    have h' := h t ht
    rw [smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha)] at h'
    rw [mul_comm]; exact h'
  · intro h
    refine ⟨fun k => Ideal.mul_mem_right _ _ ha, fun t ht => ?_⟩
    have htA := mem_idAt_of_idV hψ ht
    rw [smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha), mul_comm]
    exact h t ht

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

open GlobalTheory.SeeSaw.LastPrim in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨h1, h2, h3, -, -, -, -⟩` from `GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v`. Take `⟨n, hn⟩` from `i`. Simplify using `only at hi`. Take `rfl : n = ρ - 1` from `by omega`. Use `set i : Fin ρ := ⟨ρ - 1, hn⟩ with hi_def`.

Establish `hρ : 0 < ρ` using `by omega`. Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero`. Establish `hAAb : (D.host.AAbar : FI D) ≠ 0` using `GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D`. Establish `hL` using `colMul_jY_mem_latA_iff D ψ hψ J.W J.W₀ ρ J.d LW (𝔟 i) v i h𝔟0 (GlobalTheory.T.dualIsotropicLine_mem_completion_iff D ψ hψ J.W J.W₀ ρ J.d LW LW₀ 𝔟 v hG.sdW hmono i h𝔟0)`. Use `set 𝔑 : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) with h𝔑`.

Establish `h𝔑0 : 𝔑 ≠ 0` using `mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ) (mul_ne_zero hAAb (inv_ne_zero h𝔟0))`. Establish `e : (D.host.AAbar : FI D) * (𝔟 i)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔑`. Rewrite using `[h𝔑, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ, FractionalIdeal.spanSingleton_one, one_mul]`. Establish `e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1`. Rewrite using `[← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]`.

Establish `key : ∀ a ∈ idAt D (· = v), ∀ y ∈ latV B.V₀ LV₀ (· = v), (Matrix.mulVec (show Matrix (Fin J.W.rank) (Fin B.V₀.rank) (AE D) from J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ))) y ∈ GlobalTheory.FinPl.latA J.W LW (· = v) ↔ a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B …`. Introduce `a ha y hy`. Establish `hzi : (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idAt D (· = v)` using `sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)`. Rewrite using `[incAdj_yZero_mulVec D ρ B J hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, cA_cA, GlobalTheory.DualPairCheck.cA_incA, e, h3 _ _ (inv_ne_zero hξ)]`. Establish `e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) = -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l))`.

Rewrite using `[← mul_assoc, ← mul_assoc, e3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4, neg_mem_iff]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩`. Introduce `a ha`.

Establish `e5 : 𝔑 * 𝔷 = 𝔑 * 𝔷⁻¹⁻¹` using `by rw [inv_inv]`. Rewrite using `[h1, ← hG.last hρ a ha, GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW, e5, ← h2 _ _ (inv_ne_zero h𝔷0) h𝔑0 a ha]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hu⟩ g hg`. Take `⟨y, hy, hyg⟩` from `GlobalTheory.T.hermitianPairing_onto_inverseIdeal_at_place D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 g hg`.

Rewrite using `[← hyg]`. Conclude with `(key a ha y hy).1 (hu y hy)`. Introduce `h`. Establish `hcA : cA D a ∈ idAt D (· = v)` using `cA_mem_idAt'' ha`. Use `⟨fun k l => ?_, fun y hy => (key a ha y hy).2 (h _ (GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 y hy))⟩` and prove the remaining obligations.

Establish `e6` using `congrFun (incAdj_yZero_mulVec D ρ B J hρ a (Pi.single l 1)) k`. Rewrite `e6` using `[Matrix.mulVec_single_one]`. Use `(congrArg (· ∈ idAt D (· = v)) e6).mpr ?_` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))`.
-/
theorem last_sameAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : GlobalTheory.FinPl.Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (i : Fin ρ) (hi : i.1 + 1 = ρ) {𝔷 : FI D} {𝔟 : ℕ → FI D}
    (h𝔷0 : 𝔷 ≠ 0) (h𝔷 : GlobalTheory.SeeSaw.LineId B.o B.ζ LV₀ 𝔷 v) (h𝔟0 : 𝔟 i ≠ 0) (hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v) :
    SameAt v 1 (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷) := by
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  obtain ⟨n, hn⟩ := i
  simp only at hi
  obtain rfl : n = ρ - 1 := by omega
  set i : Fin ρ := ⟨ρ - 1, hn⟩ with hi_def
  have hρ : 0 < ρ := by omega
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hL := colMul_jY_mem_latA_iff D ψ hψ J.W J.W₀ ρ J.d LW (𝔟 i) v i h𝔟0
    (GlobalTheory.T.dualIsotropicLine_mem_completion_iff D ψ hψ J.W J.W₀ ρ J.d LW LW₀ 𝔟 v hG.sdW hmono i h𝔟0)
  set 𝔑 : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) with h𝔑
  have h𝔑0 : 𝔑 ≠ 0 := mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ)
    (mul_ne_zero hAAb (inv_ne_zero h𝔟0))
  have e : (D.host.AAbar : FI D) * (𝔟 i)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔑 := by
    rw [h𝔑, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  have e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1 := by
    rw [← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]
  have key : ∀ a ∈ idAt D (· = v), ∀ y ∈ latV B.V₀ LV₀ (· = v),
      (Matrix.mulVec (show Matrix (Fin J.W.rank) (Fin B.V₀.rank) (AE D) from
        J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ))) y ∈ GlobalTheory.FinPl.latA J.W LW (· = v) ↔
        a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idV 𝔑 v) := by
    intro a ha y hy
    have hzi : (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idAt D (· = v) :=
      sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)
    rw [incAdj_yZero_mulVec D ρ B J hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, cA_cA,
      GlobalTheory.DualPairCheck.cA_incA, e, h3 _ _ (inv_ne_zero hξ)]
    have e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a *
        cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) =
        -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) := by
      rw [← mul_assoc, ← mul_assoc, e3]; ring
    rw [e4, neg_mem_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩
  intro a ha
  have e5 : 𝔑 * 𝔷 = 𝔑 * 𝔷⁻¹⁻¹ := by rw [inv_inv]
  rw [h1, ← hG.last hρ a ha, GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW, e5,
    ← h2 _ _ (inv_ne_zero h𝔷0) h𝔑0 a ha]
  constructor
  · rintro ⟨-, hu⟩ g hg
    obtain ⟨y, hy, hyg⟩ := GlobalTheory.T.hermitianPairing_onto_inverseIdeal_at_place D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 g hg
    rw [← hyg]
    exact (key a ha y hy).1 (hu y hy)
  · intro h
    have hcA : cA D a ∈ idAt D (· = v) := cA_mem_idAt'' ha
    refine ⟨fun k l => ?_, fun y hy => (key a ha y hy).2 (h _ (GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 y hy))⟩
    have e6 := congrFun (incAdj_yZero_mulVec D ρ B J hρ a (Pi.single l 1)) k
    rw [Matrix.mulVec_single_one] at e6
    refine (congrArg (· ∈ idAt D (· = v)) e6).mpr ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem ideal_eq (𝔟 𝔷 : FI D) (h𝔟0 : 𝔟 ≠ 0) (h𝔷0 : 𝔷 ≠ 0) :
    𝔟 * (D.host.AA : FI D) * 𝔷⁻¹ *
      (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * 𝔟⁻¹) * 𝔷) = GlobalTheory.SeeSaw.dI D := by
  calc 𝔟 * (D.host.AA : FI D) * 𝔷⁻¹ *
        (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * 𝔟⁻¹) * 𝔷)
      = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA : FI D) * (D.host.AAbar : FI D) * (𝔟 * 𝔟⁻¹) *
          (𝔷 * 𝔷⁻¹) := by ring
    _ = GlobalTheory.SeeSaw.dI D := by rw [mul_inv_cancel₀ h𝔟0, mul_inv_cancel₀ h𝔷0, mul_one, mul_one]; rfl

end GlobalTheory.Core.Mi.ChainLast

open GlobalTheory.Core.Mi.ChainLast in

/- English proof (translation)
Introduce `D ψ hψ ρ B J LV LV₀ LW LW₀ v hG i hi s hs`. Take `⟨-, h2, -, -, h5, -, -⟩` from `GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v`. Take `⟨𝔢, h𝔢0, -, h𝔢⟩` from `GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D B.V LV (col B.d i) hG.sdV (col_ne_zero _ _)`. Take `⟨𝔷, h𝔷0, -, h𝔷⟩` from `GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D B.V₀ LV₀ (vecB B.o B.ζ) hG.sdV₀ (vecB_ne_zero B.o B.line)`. Set `𝔟 : ℕ → FI D` to `fun n => if h : n < ρ then Classical.choose (GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D J.W LW (col J.d ⟨n, h⟩) hG.sdW (col_ne_zero _ _)) else 1`.

Establish `h𝔟 : ∀ j : Fin ρ, 𝔟 j ≠ 0 ∧ ∀ a ∈ idAt D (· = v), a • ratV (col J.d j) ∈ latV J.W LW (· = v) ↔ a ∈ idV (𝔟 j) v`. Introduce `j`. Establish `hs` using `Classical.choose_spec (GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D J.W LW (col J.d j) hG.sdW (col_ne_zero _ _))`. Simplify using `only [𝔟, dif_pos j.2, Fin.eta]`. Conclude with `⟨hs.1, hs.2.2 v⟩`.

Establish `hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v` using `⟨hG.monoW, fun j a ha => by rw [colMul_jX]; exact (h𝔟 j).2 a ha⟩`. Establish `hA` using `cols_sameAt hψ hG i (h𝔟 i).1 (h𝔢 v) (h𝔟 i).2`. Establish `hB` using `last_sameAt hψ hG i hi h𝔷0 (h𝔷 v) (h𝔟 i).1 hmono`. Establish `hAA : (D.host.AA : FI D) ≠ 0` using `GlobalTheory.CuspCharLattice.host_AA_ne_zero _`. Establish `hAAb : (D.host.AAbar : FI D) ≠ 0` using `GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D`.

Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero`. Establish `hb0 : 𝔟 i * (D.host.AA : FI D) ≠ 0` using `mul_ne_zero (h𝔟 i).1 hAA`. Establish `hN0 : FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷 ≠ 0` using `mul_ne_zero (mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ) (mul_ne_zero hAAb (inv_ne_zero (h𝔟 i).1))) h𝔷0`. Establish `hC` using `sameAt_div hψ h𝔷0 h𝔷0 h𝔢0 hb0 (sameAt_refl v 𝔷) hA`. Establish `hD` using `sameAt_mul_of_one hψ (mul_ne_zero hb0 (inv_ne_zero h𝔷0)) hN0 hB`.

Rewrite `hD` using `[ideal_eq (𝔟 i) 𝔷 (h𝔟 i).1 h𝔷0]`. Rewrite using `[← h5 s hs, ← sameAt_trans hC hD s hs, ← h2 𝔷 𝔢 h𝔷0 h𝔢0 s hs]`. Prove the components needed by the constructor for the conclusion. Introduce `h a haV`. Establish `haA` using `mem_idAt_of_idV hψ haV`.

Establish `h'` using `h a haA ((h𝔷 v a haA).2 haV)`. Rewrite `h'` using `[colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)]`. Then use the resulting hypothesis. Introduce `h a haA haz`. Rewrite using `[colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)]`. Conclude with `h a ((h𝔷 v a haA).1 haz)`.
-/
theorem GlobalTheory.Core.Mi.LatMatch.lastAt_of_goodBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : GlobalTheory.FinPl.Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → LastAt ψ B.d (vecB B.o B.ζ) LV LV₀ v := by
  intro D ψ hψ ρ B J LV LV₀ LW LW₀ v hG i hi s hs
  obtain ⟨-, h2, -, -, h5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  obtain ⟨𝔢, h𝔢0, -, h𝔢⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D B.V LV (col B.d i) hG.sdV (col_ne_zero _ _)
  obtain ⟨𝔷, h𝔷0, -, h𝔷⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D B.V₀ LV₀ (vecB B.o B.ζ) hG.sdV₀ (vecB_ne_zero B.o B.line)
  let 𝔟 : ℕ → FI D := fun n => if h : n < ρ then
    Classical.choose (GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D J.W LW (col J.d ⟨n, h⟩) hG.sdW (col_ne_zero _ _)) else 1
  have h𝔟 : ∀ j : Fin ρ, 𝔟 j ≠ 0 ∧
      ∀ a ∈ idAt D (· = v), a • ratV (col J.d j) ∈ latV J.W LW (· = v) ↔ a ∈ idV (𝔟 j) v := by
    intro j
    have hs := Classical.choose_spec (GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D J.W LW (col J.d j) hG.sdW (col_ne_zero _ _))
    simp only [𝔟, dif_pos j.2, Fin.eta]
    exact ⟨hs.1, hs.2.2 v⟩
  have hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v :=
    ⟨hG.monoW, fun j a ha => by rw [colMul_jX]; exact (h𝔟 j).2 a ha⟩
  have hA := cols_sameAt hψ hG i (h𝔟 i).1 (h𝔢 v) (h𝔟 i).2
  have hB := last_sameAt hψ hG i hi h𝔷0 (h𝔷 v) (h𝔟 i).1 hmono
  have hAA : (D.host.AA : FI D) ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hb0 : 𝔟 i * (D.host.AA : FI D) ≠ 0 := mul_ne_zero (h𝔟 i).1 hAA
  have hN0 : FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ)
      (mul_ne_zero hAAb (inv_ne_zero (h𝔟 i).1))) h𝔷0
  have hC := sameAt_div hψ h𝔷0 h𝔷0 h𝔢0 hb0 (sameAt_refl v 𝔷) hA
  have hD := sameAt_mul_of_one hψ (mul_ne_zero hb0 (inv_ne_zero h𝔷0)) hN0 hB
  rw [ideal_eq (𝔟 i) 𝔷 (h𝔟 i).1 h𝔷0] at hD
  rw [← h5 s hs, ← sameAt_trans hC hD s hs, ← h2 𝔷 𝔢 h𝔷0 h𝔢0 s hs]
  constructor
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    have h' := h a haA ((h𝔷 v a haA).2 haV)
    rwa [colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)] at h'
  · intro h a haA haz
    rw [colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)]
    exact h a ((h𝔷 v a haA).1 haz)
