import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

section Gen

variable {F : Type} [Field F] [NumberField F]

def mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  ⟨g, Filter.Eventually.of_forall hg⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf g hg) = g v := rfl

/- English proof (translation)
Introduce `v` and use `by rw [evalV_mkAf]; exact hg v`.
-/
theorem mkAf_mem (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : mkAf g hg ∈ intAf F := fun v => by
  rw [evalV_mkAf]; exact hg v

/- English proof (translation)
Use `le_antisymm ha ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_eq_one_of_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hab : Valued.v (a * b) = 1) : Valued.v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v a * Valued.v b := by rw [← map_mul, hab]
    _ ≤ Valued.v a * 1 := mul_le_mul_right hb (Valued.v a)
    _ = Valued.v a := mul_one _

/- English proof (translation)
The claim follows from `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha`.
-/
theorem val_le_one {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : a ∈ v.adicCompletionIntegers F) : Valued.v a ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha

/- English proof (translation)
The claim follows from `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 ha`.
-/
theorem mem_of_val {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) : a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 ha

/- English proof (translation)
The claim follows from `val_le_one (natCast_mem (HeightOneSpectrum.adicCompletionIntegers F v) k)`.
-/
theorem val_natCast_le (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Valued.v (k : v.adicCompletion F) ≤ 1 :=
  val_le_one (natCast_mem (HeightOneSpectrum.adicCompletionIntegers F v) k)

/- English proof (translation)
Use `set M : v.adicCompletion F := ((2 * k + 1 : ℕ) : v.adicCompletion F) with hM`. Establish `hk : Valued.v (k : v.adicCompletion F) ≤ 1` using `val_natCast_le v k`. Establish `h2k : Valued.v (2 * (k : v.adicCompletion F)) = 1`. Establish `e : 2 * (k : v.adicCompletion F) = -1 + M` using `by rw [hM]; push_cast; ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, map_one]; exact hm), Valuation.map_neg, map_one]`.

Establish `hsq : (2 * (k : v.adicCompletion F)) ^ 2 = (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) + M * ((k : v.adicCompletion F) ^ 2 * r)`. Take the linear combination `(k : v.adicCompletion F) ^ 2 * h4`. Establish `hsmall : Valued.v (M * ((k : v.adicCompletion F) ^ 2 * r)) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ zero_le' hk`. Use `_ = 1 := one_mul 1`.

Use `_ < 1 := by rw [mul_one]; exact hm`. Establish `hprod : Valued.v ((-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q)) = 1`. Establish `e : (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) = (2 * (k : v.adicCompletion F)) ^ 2 + -(M * ((k : v.adicCompletion F) ^ 2 * r))`. Rewrite using `[hsq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hv1 : Valued.v ((2 * (k : v.adicCompletion F)) ^ 2) = 1` using `by rw [map_pow, h2k, one_pow]`. Rewrite using `[e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, hv1]; exact hsmall), hv1]`. Use `val_eq_one_of_mul v ?_ ?_ hprod` and prove the remaining obligations. Rewrite using `[map_mul, Valuation.map_neg]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_mul, Valuation.map_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_unit_of_rel (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {t q r : v.adicCompletion F}
    (hm : Valued.v (((2 * k + 1 : ℕ) : v.adicCompletion F)) < 1)
    (ht : Valued.v t ≤ 1) (hq : Valued.v q ≤ 1) (hr : Valued.v r ≤ 1)
    (h4 : (4 : v.adicCompletion F) = t * q + ((2 * k + 1 : ℕ) : v.adicCompletion F) * r) :
    Valued.v (-(k : v.adicCompletion F) * t) = 1 := by
  set M : v.adicCompletion F := ((2 * k + 1 : ℕ) : v.adicCompletion F) with hM
  have hk : Valued.v (k : v.adicCompletion F) ≤ 1 := val_natCast_le v k
  have h2k : Valued.v (2 * (k : v.adicCompletion F)) = 1 := by
    have e : 2 * (k : v.adicCompletion F) = -1 + M := by rw [hM]; push_cast; ring
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, map_one]; exact hm),
      Valuation.map_neg, map_one]
  have hsq : (2 * (k : v.adicCompletion F)) ^ 2 = (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) +
      M * ((k : v.adicCompletion F) ^ 2 * r) := by
    linear_combination (k : v.adicCompletion F) ^ 2 * h4
  have hsmall : Valued.v (M * ((k : v.adicCompletion F) ^ 2 * r)) < 1 := by
    rw [map_mul]
    calc Valued.v M * Valued.v ((k : v.adicCompletion F) ^ 2 * r) ≤ Valued.v M * 1 := by
          refine mul_le_mul_right ?_ _
          rw [map_mul, map_pow]
          calc Valued.v (k : v.adicCompletion F) ^ 2 * Valued.v r ≤ 1 * 1 := by
                gcongr
                exact pow_le_one₀ zero_le' hk
            _ = 1 := one_mul 1
      _ < 1 := by rw [mul_one]; exact hm
  have hprod : Valued.v ((-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q)) = 1 := by
    have e : (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) =
        (2 * (k : v.adicCompletion F)) ^ 2 + -(M * ((k : v.adicCompletion F) ^ 2 * r)) := by
      rw [hsq]; ring
    have hv1 : Valued.v ((2 * (k : v.adicCompletion F)) ^ 2) = 1 := by rw [map_pow, h2k, one_pow]
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, hv1]; exact hsmall), hv1]
  refine val_eq_one_of_mul v ?_ ?_ hprod
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v t ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v q ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

end Gen

end GlobalTheory.UnitRootCong

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D m hm z y hyI hyiI hyz hzw`. Take `⟨w, hwI, hw⟩` from `hzw`. Take `⟨k, rfl⟩` from `hm`. Establish `hE` using `GlobalTheory.AdelicU.isCMExt_host D`. Use `set M : ℕ := 2 * k + 1 with hMdef`.

Use `set yv : Af D.host.F ⊗[D.host.F] D.host.E := (y : Af D.host.F ⊗[D.host.F] D.host.E) with hyv`. Use `set yi : Af D.host.F ⊗[D.host.F] D.host.E := ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) with hyi`. Establish `hyy : yv * yi = 1` using `y.mul_inv`. Use `set s := sigR (Af D.host.F) D.sp.cm.sig yv with hs`. Establish `hsI : s ∈ intAE D` using `GlobalTheory.PlaceIdem.sig_mem D hyI`.

Use `set T := Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hT`. Use `set ι := algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hι`. Establish `ht : yv + s = ι (T yv)` using `GlobalTheory.GaussMean.OneVec.add_sigR _ hE yv`. Establish `hw' : (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * w`. Rewrite using `[hw, nsmul_eq_mul]`.

Establish `E3 : 2 * yv = ι (T yv) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)`. Take the linear combination `ht + hyz + s * hw'`. Establish `hιI : ∀ a ∈ intAf D.host.F, ι a ∈ intAE D` using `fun a ha => AddSubgroup.subset_closure ⟨a, ha, 1, by simp [hι, Algebra.TensorProduct.algebraMap_apply]⟩`. Establish `hmulI : ∀ {a b}, a ∈ intAE D → b ∈ intAE D → a * b ∈ intAE D` using `fun ha hb => GlobalTheory.HostAdeleIso.intAE_mul_mem D ha hb`. Establish `hoI : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D`.

Simplify using `using hιI 1 GlobalTheory.SplitHeckeLabel.one_mem_intAf`. Establish `hnI : ∀ n : ℕ, (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D` using `fun n => by`. Rewrite using `[← nsmul_one]`. Conclude with `nsmul_mem hoI n`. Establish `hrI : w * s * yi ∈ intAE D` using `hmulI (hmulI hwI hsI) hyiI`.

Establish `hTl : ∀ (a : Af D.host.F) x, T (ι a * x) = a * T x` using `fun a x => by`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`. Establish `hT2 : T (ι 2) = 4`. Establish `h1` using `GlobalTheory.GaussMean.OneVec.half_trace (Af D.host.F) hE (2 : Af D.host.F)`. Establish `h2` using `GlobalTheory.GaussMean.OneVec.half_two (F := D.host.F) (Af D.host.F)`.

Take the linear combination `2 * h1 - T (ι 2) * h2`. Establish `R1 : (4 : Af D.host.F) = T yv * T yi + (M : Af D.host.F) * T (w * s * yi)`. Establish `e : ι 2 = ι (T yv) * yi + ι (M : Af D.host.F) * (w * s * yi)`. Rewrite using `[map_ofNat, map_natCast]`. Take the linear combination `yi * E3 - 2 * hyy`.

Rewrite using `[← hT2, e, map_add, hTl, hTl]`. Set `P : HeightOneSpectrum (𝓞 D.host.F) → Prop` to `fun v => Valued.v ((M : v.adicCompletion D.host.F)) < 1`. Establish `hunit : ∀ v, P v → Valued.v (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv)) = 1` using `fun v hv => by`. Use `val_unit_of_rel v k hv (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyI v)) (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyiI v)) (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hrI v)) ?_` and prove the remaining obligations. Use `congrArg (evalV D.host.F v) R1` as an intermediate fact.

Simplify using `only [map_add, map_mul, map_natCast, map_ofNat] at this`. Conclude with `this`. Establish `hMone : ∀ v, ¬ P v → Valued.v ((M : v.adicCompletion D.host.F)) = 1` using `fun v hv => le_antisymm (val_natCast_le v M) (not_lt.1 hv)`. Establish `hMne : ∀ v, ¬ P v → (M : v.adicCompletion D.host.F) ≠ 0` using `fun v hv h => by`. Use `hMone v hv` as an intermediate fact.

Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Set `eg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F` to `fun v => if P v then 1 else 0`. Set `fg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F` to `fun v => if P v then 0 else (M : v.adicCompletion D.host.F)⁻¹`. Set `cg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F` to `fun v => if P v then -(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv) else 1`.

Set `dg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F` to `fun v => if P v then (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv))⁻¹ else 1`. Establish `heg : ∀ v, eg v ∈ v.adicCompletionIntegers D.host.F` using `fun v => by`. Apply the tactic sequence `by_cases hv : P v <;> simp only [eg, hv, if_true, if_false] <;> [exact one_mem _; exact zero_mem _]`. Establish `hfg : ∀ v, fg v ∈ v.adicCompletionIntegers D.host.F` using `fun v => by`. Apply the tactic sequence `by_cases hv : P v <;> simp only [fg, hv, if_true, if_false]`.

Conclude with `zero_mem _`. Conclude with `mem_of_val (by rw [map_inv₀, hMone v hv, inv_one])`. Establish `hcg : ∀ v, cg v ∈ v.adicCompletionIntegers D.host.F` using `fun v => by`. Apply the tactic sequence `by_cases hv : P v <;> simp only [cg, hv, if_true, if_false]`. Conclude with `mem_of_val (hunit v hv).le`.

Conclude with `one_mem _`. Establish `hdg : ∀ v, dg v ∈ v.adicCompletionIntegers D.host.F` using `fun v => by`. Apply the tactic sequence `by_cases hv : P v <;> simp only [dg, hv, if_true, if_false]`. Conclude with `mem_of_val (by rw [map_inv₀, hunit v hv, inv_one])`. Conclude with `one_mem _`.

Use `set e := mkAf eg heg`. Use `set f := mkAf fg hfg`. Use `set c := mkAf cg hcg`. Use `set d := mkAf dg hdg`. Establish `hcd : c * d = 1` using `GlobalTheory.SplitHeckeLabel.af_ext fun v => by`.

Rewrite using `[map_mul, map_one, evalV_mkAf, evalV_mkAf]`. Apply the tactic sequence `by_cases hv : P v <;> simp only [cg, dg, hv, if_true, if_false, mul_one]`. Use `mul_inv_cancel₀ fun h0 => ?_` and prove the remaining obligations. Use `hunit v hv` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`.

Conclude with `zero_ne_one this`. Establish `hef : e + (M : Af D.host.F) * f = 1` using `GlobalTheory.SplitHeckeLabel.af_ext fun v => by`. Rewrite using `[map_add, map_mul, map_one, map_natCast, evalV_mkAf, evalV_mkAf]`. Apply the tactic sequence `by_cases hv : P v <;> simp only [eg, fg, hv, if_true, if_false, mul_zero, add_zero, zero_add]`. Conclude with `mul_inv_cancel₀ (hMne v hv)`.

Establish `hce : c = e * (-(k : Af D.host.F) * T yv) + (M : Af D.host.F) * f` using `GlobalTheory.SplitHeckeLabel.af_ext fun v => by`. Rewrite using `[map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast, evalV_mkAf, evalV_mkAf, evalV_mkAf]`. Apply the tactic sequence `by_cases hv : P v <;> simp only [eg, fg, cg, hv, if_true, if_false, mul_zero, add_zero, zero_add, one_mul, zero_mul]`. Conclude with `(mul_inv_cancel₀ (hMne v hv)).symm`. Establish `E1 : ι e + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f = 1`.

Use `congrArg ι hef` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, map_natCast, map_one]`. Then use the resulting hypothesis. Establish `E2 : ι c = ι e * (-(k : Af D.host.F ⊗[D.host.F] D.host.E) * ι (T yv)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f`. Rewrite using `[hce, map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast]`. Establish `E4 : ι c * ι d = 1` using `by rw [← map_mul, hcd, map_one]`.

Use `set W := ι e * (yv - (k : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)) + ι f * (yv - 1) with hW`. Establish `hmain : yv - ι c = (M : Af D.host.F ⊗[D.host.F] D.host.E) * W`. Establish `hM : (M : Af D.host.F ⊗[D.host.F] D.host.E) = 2 * (k : Af D.host.F ⊗[D.host.F] D.host.E) + 1`. Rewrite using `[hMdef]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hW]`. Take the linear combination `(-1 : Af D.host.F ⊗[D.host.F] D.host.E) * E2 - yv * E1 - (k : Af D.host.F ⊗[D.host.F] D.host.E) * ι e * E3 - ι e * yv * hM`. Establish `hWI : W ∈ intAE D`. Rewrite using `[hW]`.

Use `add_mem (hmulI (hιI _ (mkAf_mem eg heg)) (sub_mem hyI (hmulI (hnI k) (hmulI hwI hsI)))) (hmulI (hιI _ (mkAf_mem fg hfg)) (sub_mem hyI hoI))` and prove the remaining obligations. Set `b : (Af D.host.F)ˣ` to `⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩`. Use `⟨b, y * Units.map ι.toMonoidHom b, ?_, ?_, ?_, W * ι d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.coe_map]`. Both sides reduce to the same expression.

Conclude with `hmulI hyI (hιI _ (mkAf_mem dg hdg))`. Rewrite using `[mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map]`. Conclude with `hmulI (hιI _ (mkAf_mem cg hcg)) hyiI`. Conclude with `hmulI hWI (hιI _ (mkAf_mem dg hdg))`. Rewrite using `[Units.val_mul, Units.coe_map, nsmul_eq_mul] show yv * ι d - 1 = _`.

Take the linear combination `ι d * hmain + E4`.
-/
theorem exists_adele_unit_congr_one : ∀ (D : D7) (m : ℕ), Odd m → ∀ (z y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) → (∃ w ∈ intAE D, (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w) → ∃ (b : (Af D.host.F)ˣ) (y' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y' : Af D.host.F ⊗[D.host.F] D.host.E) = (y : Af D.host.F ⊗[D.host.F] D.host.E) * ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) ∧ (y' : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ((y'⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ∃ w ∈ intAE D, (y' : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w := by
  classical
  intro D m hm z y hyI hyiI hyz hzw
  obtain ⟨w, hwI, hw⟩ := hzw
  obtain ⟨k, rfl⟩ := hm
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  set M : ℕ := 2 * k + 1 with hMdef
  set yv : Af D.host.F ⊗[D.host.F] D.host.E := (y : Af D.host.F ⊗[D.host.F] D.host.E) with hyv
  set yi : Af D.host.F ⊗[D.host.F] D.host.E := ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) with hyi
  have hyy : yv * yi = 1 := y.mul_inv
  set s := sigR (Af D.host.F) D.sp.cm.sig yv with hs
  have hsI : s ∈ intAE D := GlobalTheory.PlaceIdem.sig_mem D hyI
  set T := Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hT
  set ι := algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hι
  have ht : yv + s = ι (T yv) := GlobalTheory.GaussMean.OneVec.add_sigR _ hE yv
  have hw' : (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    rw [hw, nsmul_eq_mul]
  have E3 : 2 * yv = ι (T yv) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s) := by
    linear_combination ht + hyz + s * hw'

  have hιI : ∀ a ∈ intAf D.host.F, ι a ∈ intAE D := fun a ha =>
    AddSubgroup.subset_closure ⟨a, ha, 1, by simp [hι, Algebra.TensorProduct.algebraMap_apply]⟩
  have hmulI : ∀ {a b}, a ∈ intAE D → b ∈ intAE D → a * b ∈ intAE D := fun ha hb =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D ha hb
  have hoI : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    simpa using hιI 1 GlobalTheory.SplitHeckeLabel.one_mem_intAf
  have hnI : ∀ n : ℕ, (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := fun n => by
    rw [← nsmul_one]; exact nsmul_mem hoI n
  have hrI : w * s * yi ∈ intAE D := hmulI (hmulI hwI hsI) hyiI

  have hTl : ∀ (a : Af D.host.F) x, T (ι a * x) = a * T x := fun a x => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hT2 : T (ι 2) = 4 := by
    have h1 := GlobalTheory.GaussMean.OneVec.half_trace (Af D.host.F) hE (2 : Af D.host.F)
    have h2 := GlobalTheory.GaussMean.OneVec.half_two (F := D.host.F) (Af D.host.F)
    linear_combination 2 * h1 - T (ι 2) * h2
  have R1 : (4 : Af D.host.F) = T yv * T yi + (M : Af D.host.F) * T (w * s * yi) := by
    have e : ι 2 = ι (T yv) * yi + ι (M : Af D.host.F) * (w * s * yi) := by
      rw [map_ofNat, map_natCast]
      linear_combination yi * E3 - 2 * hyy
    rw [← hT2, e, map_add, hTl, hTl]

  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun v => Valued.v ((M : v.adicCompletion D.host.F)) < 1
  have hunit : ∀ v, P v → Valued.v (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv)) = 1 := fun v hv => by
    refine val_unit_of_rel v k hv (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyiI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hrI v)) ?_
    have := congrArg (evalV D.host.F v) R1
    simp only [map_add, map_mul, map_natCast, map_ofNat] at this
    exact this
  have hMone : ∀ v, ¬ P v → Valued.v ((M : v.adicCompletion D.host.F)) = 1 := fun v hv =>
    le_antisymm (val_natCast_le v M) (not_lt.1 hv)
  have hMne : ∀ v, ¬ P v → (M : v.adicCompletion D.host.F) ≠ 0 := fun v hv h => by
    have := hMone v hv; rw [h, map_zero] at this; exact zero_ne_one this
  let eg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F := fun v => if P v then 1 else 0
  let fg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then 0 else (M : v.adicCompletion D.host.F)⁻¹
  let cg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then -(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv) else 1
  let dg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv))⁻¹ else 1
  have heg : ∀ v, eg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [eg, hv, if_true, if_false] <;> [exact one_mem _; exact zero_mem _]
  have hfg : ∀ v, fg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [fg, hv, if_true, if_false]
    · exact zero_mem _
    · exact mem_of_val (by rw [map_inv₀, hMone v hv, inv_one])
  have hcg : ∀ v, cg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [cg, hv, if_true, if_false]
    · exact mem_of_val (hunit v hv).le
    · exact one_mem _
  have hdg : ∀ v, dg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [dg, hv, if_true, if_false]
    · exact mem_of_val (by rw [map_inv₀, hunit v hv, inv_one])
    · exact one_mem _
  set e := mkAf eg heg
  set f := mkAf fg hfg
  set c := mkAf cg hcg
  set d := mkAf dg hdg
  have hcd : c * d = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_mul, map_one, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [cg, dg, hv, if_true, if_false, mul_one]
    refine mul_inv_cancel₀ fun h0 => ?_
    have := hunit v hv; rw [h0, map_zero] at this; exact zero_ne_one this
  have hef : e + (M : Af D.host.F) * f = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add, map_mul, map_one, map_natCast, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, hv, if_true, if_false, mul_zero, add_zero, zero_add]
    exact mul_inv_cancel₀ (hMne v hv)
  have hce : c = e * (-(k : Af D.host.F) * T yv) + (M : Af D.host.F) * f := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast, evalV_mkAf, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, cg, hv, if_true, if_false, mul_zero, add_zero, zero_add, one_mul, zero_mul]
    exact (mul_inv_cancel₀ (hMne v hv)).symm
  have E1 : ι e + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f = 1 := by
    have := congrArg ι hef; rwa [map_add, map_mul, map_natCast, map_one] at this
  have E2 : ι c = ι e * (-(k : Af D.host.F ⊗[D.host.F] D.host.E) * ι (T yv)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f := by
    rw [hce, map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast]
  have E4 : ι c * ι d = 1 := by rw [← map_mul, hcd, map_one]
  set W := ι e * (yv - (k : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)) + ι f * (yv - 1) with hW
  have hmain : yv - ι c = (M : Af D.host.F ⊗[D.host.F] D.host.E) * W := by
    have hM : (M : Af D.host.F ⊗[D.host.F] D.host.E) = 2 * (k : Af D.host.F ⊗[D.host.F] D.host.E) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [hW]
    linear_combination (-1 : Af D.host.F ⊗[D.host.F] D.host.E) * E2 - yv * E1 - (k : Af D.host.F ⊗[D.host.F] D.host.E) * ι e * E3 - ι e * yv * hM
  have hWI : W ∈ intAE D := by
    rw [hW]
    refine add_mem (hmulI (hιI _ (mkAf_mem eg heg)) (sub_mem hyI (hmulI (hnI k) (hmulI hwI hsI))))
      (hmulI (hιI _ (mkAf_mem fg hfg)) (sub_mem hyI hoI))
  let b : (Af D.host.F)ˣ := ⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩
  refine ⟨b, y * Units.map ι.toMonoidHom b, ?_, ?_, ?_, W * ι d, ?_, ?_⟩
  · rw [Units.val_mul, Units.coe_map]
    rfl
  · exact hmulI hyI (hιI _ (mkAf_mem dg hdg))
  · rw [mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map]
    exact hmulI (hιI _ (mkAf_mem cg hcg)) hyiI
  · exact hmulI hWI (hιI _ (mkAf_mem dg hdg))
  · rw [Units.val_mul, Units.coe_map, nsmul_eq_mul]
    show yv * ι d - 1 = _
    linear_combination ι d * hmain + E4

end GlobalTheory.UnitRootCong
