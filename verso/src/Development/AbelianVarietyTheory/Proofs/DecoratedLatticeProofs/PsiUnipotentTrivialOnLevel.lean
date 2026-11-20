import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.FinPlLoc Filter Topology
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PsiUnit

variable {D : D7}

open Formalism.IndefR.Fin.LevelGroupLemmas in

/- English proof (translation)
Establish `h1 : ∀ A : Finset (Pl D), ψ (idemS A * t) = 1`. Introduce `A`. Proceed by induction on `A using Finset.induction_on with`. Consider the case `empty => rw [idemS_empty, zero_mul, AddChar.map_zero_eq_one]`. Consider the case `insert v A hv ih`.

Establish `e : idemS (insert v A) = idemS A + pairA D.host.F 0 (ePl D (· = v))`. Unfold `idemS`. Rewrite using `[← pairA_add]`. Use `congr 1`. Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `evalV D.host.F w (sglS (insert v A)) = evalV D.host.F w (sglS A + ePl D (· = v))`. Rewrite using `[map_add, evalV_sglS, evalV_sglS, evalV_ePl]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `[hv]`.

Simplify using `[hw]`. Rewrite using `[e, add_mul, AddChar.map_add_eq_mul, ih, h, one_mul]`. Establish `h2` using `(hψ.tendsto 0).comp (tendsto_AF t ht)`. Rewrite `h2` using `[AddChar.map_zero_eq_one]`. Use `tendsto_nhds_unique tendsto_const_nhds (h2.congr fun A => ?_)` and prove the remaining obligations.

Establish `e : t = idemS A * t + (1 - idemS A) * t` using `by ring`. Express the relevant statement in the definitionally equal form `ψ ((1 - idemS A) * t) = ψ t`. Use `conv_rhs => rw [e, AddChar.map_add_eq_mul, h1, one_mul]`.
-/
theorem char_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (t : AF D.host.F)
    (ht : fstA D.host.F t = 0) (h : ∀ v : Pl D, ψ (pairA D.host.F 0 (ePl D (· = v)) * t) = 1) : ψ t = 1 := by
  classical
  have h1 : ∀ A : Finset (Pl D), ψ (idemS A * t) = 1 := by
    intro A
    induction A using Finset.induction_on with
    | empty => rw [idemS_empty, zero_mul, AddChar.map_zero_eq_one]
    | insert v A hv ih =>
      have e : idemS (insert v A) = idemS A + pairA D.host.F 0 (ePl D (· = v)) := by
        unfold idemS
        rw [← pairA_add]
        congr 1
        refine RestrictedProduct.ext _ _ fun w => ?_
        change evalV D.host.F w (sglS (insert v A)) = evalV D.host.F w (sglS A + ePl D (· = v))
        rw [map_add, evalV_sglS, evalV_sglS, evalV_ePl]
        by_cases hw : w = v
        · subst hw; simp [hv]
        · simp [hw]
      rw [e, add_mul, AddChar.map_add_eq_mul, ih, h, one_mul]
  have h2 := (hψ.tendsto 0).comp (tendsto_AF t ht)
  rw [AddChar.map_zero_eq_one] at h2
  refine tendsto_nhds_unique tendsto_const_nhds (h2.congr fun A => ?_)
  have e : t = idemS A * t + (1 - idemS A) * t := by ring
  change ψ ((1 - idemS A) * t) = ψ t
  conv_rhs => rw [e, AddChar.map_add_eq_mul, h1, one_mul]

/- English proof (translation)
Rewrite using `[← smul_eq_mul (pairA D.host.F 0 (ePl D Q)), ← map_smul, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem trace_idem (Q : Pl D → Prop) (s : AE D) : Algebra.trace (AF D.host.F) (AE D) (idem D Q * s) =
    pairA D.host.F 0 (ePl D Q) * Algebra.trace (AF D.host.F) (AE D) s := by
  rw [← smul_eq_mul (pairA D.host.F 0 (ePl D Q)), ← map_smul, Algebra.smul_def]
  rfl

/- English proof (translation)
Use `char_eq_one_of_local ψ hψ _ ?_ fun v => ?_` and prove the remaining obligations. Rewrite using `[← (mem_idAt_iff P s).1 hs, trace_idem, map_mul]`. Conclude with `zero_mul _`. Rewrite using `[← trace_idem]`. Distinguish the cases in `hv : P v`.

Conclude with `h v hv`. Establish `h0 : idem D (· = v) * s = 0`. Use `(mem_idOff_iff _ s).1 ((Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_)` and prove the remaining obligations. Conclude with `compAt_of_idAt hs (by rw [w.2]; exact hv)`. Rewrite using `[h0]`.

Conclude with `psiE_zero ψ`.
-/
theorem psiE_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) {P : Pl D → Prop} {s : AE D}
    (hs : s ∈ idAt D P) (h : ∀ v, P v → psiE ψ (idem D (· = v) * s) = 1) : psiE ψ s = 1 := by
  refine char_eq_one_of_local ψ hψ _ ?_ fun v => ?_
  · rw [← (mem_idAt_iff P s).1 hs, trace_idem, map_mul]
    exact zero_mul _
  · rw [← trace_idem]
    by_cases hv : P v
    · exact h v hv
    · have h0 : idem D (· = v) * s = 0 := by
        refine (mem_idOff_iff _ s).1 ((Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_)
        exact compAt_of_idAt hs (by rw [w.2]; exact hv)
      rw [h0]
      exact psiE_zero ψ

/- English proof (translation)
Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `y ⟨α, h1, h2, h3⟩`. Conclude with `⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), h3⟩`.
-/
theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) : latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, h1, h2, h3⟩
  exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), h3⟩

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem mulVec_colMul {l m n : ℕ} (A : Mx D l m) (x : Mx D m n) (i : Fin n) (a : AE D) :
    A *ᵥ colMul x i a = colMul (A ⬝ x) i a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `h1` using `latV_mono hv ha`. Establish `h2` using `smul_latV v (idem_mem_intAt (· = v)) ((ht.2 _ (latV_idAt h1)).1 h1)`. Establish `h3` using `((hm _).1 h2).1 i`. Rewrite `h3` using `[Matrix.mulVec_smul, mulVec_colMul, mulVec_colMul, dV.levi_jX, ← Matrix.mul_assoc, dV.pX_jX, Matrix.one_mul]`. Use `h3 using 2` and compare the differences between its conclusion and the goal.

Rewrite using `[Pi.smul_apply, smul_eq_mul, colMul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem entry_line {V V₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) {LV : Lat V} {LV₀ : Lat V₀} {P : Pl D → Prop} {v : Pl D}
    (hv : P v) (hm : MonoAt dV LV LV₀ v) {t : GL (Fin ρ) (AE D)} (ht : InK V LV P (dV.levi t)) (i j : Fin ρ) (a : AE D)
    (ha : colMul dV.jX j a ∈ latV V LV (· = v)) : colMul dV.jX i (idem D (· = v) * t.1 i j * a) ∈ latV V LV (· = v) := by
  have h1 := latV_mono hv ha
  have h2 := smul_latV v (idem_mem_intAt (· = v)) ((ht.2 _ (latV_idAt h1)).1 h1)
  have h3 := ((hm _).1 h2).1 i
  rw [Matrix.mulVec_smul, mulVec_colMul, mulVec_colMul, dV.levi_jX, ← Matrix.mul_assoc, dV.pX_jX, Matrix.one_mul] at h3
  convert h3 using 2
  rw [Pi.smul_apply, smul_eq_mul, colMul]
  ring

/- English proof (translation)
Introduce `D ψ V V₀ ρ dV LV LV₀ P hψ _ hP u hu hK`. Establish `key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE ψ (u.1.1 i j) = 1` using `fun i j hij => by`. Establish `hne : i ≠ j` using `fun e => by rw [e] at hij; omega`. Establish `hs : u.1.1 i j ∈ idAt D P`. Use `hu i j` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]`. Then use the resulting hypothesis. Use `psiE_eq_one_of_local ψ hψ.1.1 hs fun v hv => ?_` and prove the remaining obligations. Establish `h` using `((hP v hv).2 i j hij _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1 (entry_line dV hv (hP v hv).1 hK i j) _ (idem_mem_intAt _)`. Rewrite `h` using `[mul_right_comm, idem_mul_self]`. Then use the resulting hypothesis. Unfold `psiUni upSum`.

Use `Finset.sum_induction _ (fun x => psiE ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul]) (psiE_zero ψ) fun i _ => ?_` and prove the remaining obligations. Use `Finset.sum_induction _ (fun x => psiE ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul]) (psiE_zero ψ) fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `key i j h`. Conclude with `psiE_zero ψ`.
-/
theorem psiUni_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (LV : Lat V)
    (LV₀ : Lat V₀) (P : Pl D → Prop), IsStdChar D ψ (-1) → IsSelfDualC V LV →
    (∀ v, P v → MonoAt dV LV LV₀ v ∧ PrimAt ψ dV LV v) → ∀ u : UX D ρ, MxAt P (u.1.1 - 1) → InK V LV P (dV.levi u.1) →
    psiUni ψ u.1 = 1 := by
  intro D ψ V V₀ ρ dV LV LV₀ P hψ _ hP u hu hK
  have key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have hs : u.1.1 i j ∈ idAt D P := by
      have := hu i j
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    refine psiE_eq_one_of_local ψ hψ.1.1 hs fun v hv => ?_
    have h := ((hP v hv).2 i j hij _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1
      (entry_line dV hv (hP v hv).1 hK i j) _ (idem_mem_intAt _)
    rwa [mul_right_comm, idem_mul_self] at h
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero ψ) fun j _ => ?_
  split_ifs with h
  · exact key i j h
  · exact psiE_zero ψ

end GlobalTheory.FinPl.PsiUnit

end
