import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CTZeroCut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Complex.exp (u * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = _`. Rewrite using `[GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx]`.
-/
theorem absC_loc (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n)) :
    (((Model.absC E u).loc w x : ℂˣ) : ℂ) = Complex.exp (u * (-(n * Real.log (Ideal.absNorm w.asIdeal : ℕ)) : ℝ)) := by
  change Complex.exp (u * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx]

/- English proof (translation)
Introduce `x hx`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[absC_loc u w x 0 (by rw [hx]; simp)]`. Simplify using the standard rewrite rules.
-/
theorem absC_unrAt (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E u).UnrAt w := by
  intro x hx
  apply Units.ext
  rw [absC_loc u w x 0 (by rw [hx]; simp)]
  simp

/- English proof (translation)
Establish `hu : Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-(1 : ℤ))` using `unif_spec w`. Establish `h` using `absC_loc u w (atFin w (unif w)) 1 hu`. Express the relevant statement in the definitionally equal form `(((Model.absC E u).loc w (atFin w (unif w)) : ℂˣ) : ℂ) = _`. Rewrite using `[h, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 (qV_ne_zero w))]`. Establish `e : Complex.log ((qV E w : ℕ) : ℂ) = ((Real.log (Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem absC_val (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((Model.absC E u).val w : ℂˣ) : ℂ) = ((qV E w : ℕ) : ℂ) ^ (-u) := by
  have hu : Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-(1 : ℤ)) :=
    unif_spec w
  have h := absC_loc u w (atFin w (unif w)) 1 hu
  change (((Model.absC E u).loc w (atFin w (unif w)) : ℂˣ) : ℂ) = _
  rw [h, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 (qV_ne_zero w))]
  have e : Complex.log ((qV E w : ℕ) : ℂ) = ((Real.log (Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]; rfl
  rw [e]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `E _ _ _ m σ u`. Use `⟨σ.twist (Model.absC E (-u)), Filter.Eventually.of_forall fun w B hB => ?_⟩` and prove the remaining obligations. Use `⟨B.map (· * (Model.absC E (-u)).val w), GlobalTheory.SphGal.hasSatGL_twist E m σ _ w B (absC_unrAt (-u) w) hB, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`. Unfold `sclQ`.

Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Units.val_mul, absC_val, neg_neg]`.
-/
theorem twistSat_holds : TwistSat := by
  intro E _ _ _ m σ u
  refine ⟨σ.twist (Model.absC E (-u)), Filter.Eventually.of_forall fun w B hB => ?_⟩
  refine ⟨B.map (· * (Model.absC E (-u)).val w),
    GlobalTheory.SphGal.hasSatGL_twist E m σ _ w B (absC_unrAt (-u) w) hB, ?_⟩
  rw [Multiset.map_map]
  unfold sclQ
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, absC_val, neg_neg]

end DiscreteGroups.T1.G

end
