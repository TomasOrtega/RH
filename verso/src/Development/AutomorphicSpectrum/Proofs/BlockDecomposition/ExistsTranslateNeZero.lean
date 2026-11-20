import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponentStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def IsFix (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (v : π.V) : Prop :=
  ∀ k ∈ KGL w a, π.locRep w k v = v

def sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ {φ | ∃ (g : GL (Fin a) (w.adicCompletion E)) (v : π.V), IsFix π w v ∧ φ = (π.locRep w g v).1}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locRep_val (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) (v : π.V) :
    (π.locRep w g v).1 = finRep E a (locGL E a w g) v.1 := rfl

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨g, v, hv, rfl⟩`.
-/
theorem mem_sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) {v : π.V}
    (hv : IsFix π w v) : (π.locRep w g v).1 ∈ sphSpan π w :=
  Submodule.subset_span ⟨g, v, hv, rfl⟩

/- English proof (translation)
Introduce `k hk` and use `by refine Subtype.ext ?_ rw [locRep_val, CuspSub.op_val] have e := LinearMap.congr_fun (hc k) v.1 simp only [Module.End.mul_apply] at e rw [← e, ← locRep_val, hv k hk]`.
-/
theorem isFix_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a)
    (hc : ∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) {v : π.V} (hv : IsFix π w v) :
    IsFix π w (π.op o v) := fun k hk => by
  refine Subtype.ext ?_
  rw [locRep_val, CuspSub.op_val]
  have e := LinearMap.congr_fun (hc k) v.1
  simp only [Module.End.mul_apply] at e
  rw [← e, ← locRep_val, hv k hk]

/- English proof (translation)
Establish `e` using `LinearMap.congr_fun (hc g) v.1`. Simplify using `only [Module.End.mul_apply] at e`. Rewrite using `[locRep_val, e]`. Conclude with `mem_sphSpan π w g (isFix_op π w o hc hv)`.
-/
theorem act_translate (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a)
    (hc : ∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o)
    (g : GL (Fin a) (w.adicCompletion E)) {v : π.V} (hv : IsFix π w v) :
    act o (π.locRep w g v).1 ∈ sphSpan π w := by
  have e := LinearMap.congr_fun (hc g) v.1
  simp only [Module.End.mul_apply] at e
  rw [locRep_val, e]
  exact mem_sphSpan π w g (isFix_op π w o hc hv)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `rt E a _ * rt E a _ = rt E a _ * rt E a _`. Rewrite using `[← map_mul, ← map_mul]`. Conclude with `congrArg (rt E a) (infGL_comm _ _)`.
-/
theorem cpt_comm (y : Kinf E a) (k : GL (Fin a) (Af E)) :
    act (.cpt y : Op E a) * finRep E a k = finRep E a k * act (.cpt y : Op E a) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg (rt E a) (infGL_comm _ _)

/- English proof (translation)
The claim follows from `lie_rt_fin X k`.
-/
theorem lie_comm' (X : Lie E a) (k : GL (Fin a) (Af E)) :
    act (.lie X : Op E a) * finRep E a k = finRep E a k * act (.lie X : Op E a) :=
  lie_rt_fin X k

/- English proof (translation)
Take `⟨h, gw, e, hc⟩` from `GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w (finGL E a (k * locGL E a w g))`. Take `⟨h', hh'⟩ : ∃ h' : GL (Fin a) (Af E), h' = k * locGL E a w g * (locGL E a w gw)⁻¹` from `⟨_, rfl⟩`. Establish `hh : h = finGL E a h'`. Rewrite using `[hh', map_mul, map_inv, e, mul_inv_cancel_right]`. Establish `hcomm : ∀ u, finRep E a h' * finRep E a (locGL E a w u) = finRep E a (locGL E a w u) * finRep E a h'` using `fun u => by`.

Establish `h2` using `congrArg (rt E a) (hc u)`. Rewrite `h2` using `[hh, map_mul, map_mul]`. Conclude with `h2`. Establish `hfix : IsFix π w (π.op (.fin h') v)` using `isFix_op π w (.fin h') (fun u => hcomm u) hv`. Establish `e2 : finRep E a k (π.locRep w g v).1 = (π.locRep w gw (π.op (.fin h') v)).1`.

Rewrite using `[locRep_val, locRep_val, CuspSub.op_val]`. Express the relevant statement in the definitionally equal form `(finRep E a k * finRep E a (locGL E a w g)) v.1 = (finRep E a (locGL E a w gw) * finRep E a h') v.1`. Rewrite using `[← hcomm, ← map_mul, ← map_mul, hh', inv_mul_cancel_right]`. Rewrite using `[e2]`. Conclude with `mem_sphSpan π w gw hfix`.
-/
theorem fin_translate (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (g : GL (Fin a) (w.adicCompletion E)) {v : π.V} (hv : IsFix π w v) :
    finRep E a k (π.locRep w g v).1 ∈ sphSpan π w := by
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w (finGL E a (k * locGL E a w g))
  obtain ⟨h', hh'⟩ : ∃ h' : GL (Fin a) (Af E), h' = k * locGL E a w g * (locGL E a w gw)⁻¹ := ⟨_, rfl⟩
  have hh : h = finGL E a h' := by
    rw [hh', map_mul, map_inv, e, mul_inv_cancel_right]
  have hcomm : ∀ u, finRep E a h' * finRep E a (locGL E a w u) = finRep E a (locGL E a w u) * finRep E a h' := fun u => by
    have h2 := congrArg (rt E a) (hc u)
    rw [hh, map_mul, map_mul] at h2
    exact h2
  have hfix : IsFix π w (π.op (.fin h') v) := isFix_op π w (.fin h') (fun u => hcomm u) hv
  have e2 : finRep E a k (π.locRep w g v).1 = (π.locRep w gw (π.op (.fin h') v)).1 := by
    rw [locRep_val, locRep_val, CuspSub.op_val]
    change (finRep E a k * finRep E a (locGL E a w g)) v.1 = (finRep E a (locGL E a w gw) * finRep E a h') v.1
    rw [← hcomm, ← map_mul, ← map_mul, hh', inv_mul_cancel_right]
  rw [e2]
  exact mem_sphSpan π w gw hfix

/- English proof (translation)
Introduce `o φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, v, hv, rfl⟩` from `hx`. Consider the cases of `o with`.

Consider the case `fin k => exact fin_translate π w k g hv`. Consider the case `cpt y => exact act_translate π w _ (fun u => cpt_comm y _) g hv`. Consider the case `lie X => exact act_translate π w _ (fun u => lie_comm' X _) g hv`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem isStable_sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : IsStable (sphSpan π w) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, v, hv, rfl⟩ := hx
    cases o with
    | fin k => exact fin_translate π w k g hv
    | cpt y => exact act_translate π w _ (fun u => cpt_comm y _) g hv
    | lie X => exact act_translate π w _ (fun u => lie_comm' X _) g hv
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
The claim follows from `Submodule.span_le.2 fun _ ⟨g, v, _, e⟩ => e ▸ (π.locRep w g v).2`.
-/
theorem sphSpan_le (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : sphSpan π w ≤ π.V :=
  Submodule.span_le.2 fun _ ⟨g, v, _, e⟩ => e ▸ (π.locRep w g v).2

/- English proof (translation)
Introduce `E _ _ _ a π w B hB l hl`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨x, hx⟩` from `hB.exists_vec`. Establish `hfix : ∀ v : π.V, IsFix π w v → v ≠ 0 → IsSatVecGL w (π.locRep w) v B` using `fun v hv h0 => hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0`.

Establish `hxf : IsFix π w x` using `GlobalTheory.LGrp.mem_fixed.1 hx.2.1`. Establish `hker : sphSpan π w ≤ (LinearMap.ker l).map π.V.subtype`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, v, hv, rfl⟩`. Use `⟨π.locRep w g v, ?_, rfl⟩` and prove the remaining obligations.

Distinguish the cases in `h0 : v = 0`. Simplify using `[h0]`. Conclude with `hcon v g (hfix v hv h0)`. Break down `π.irred _ (sphSpan_le π w) (isStable_sphSpan π w) with h | h` into its components or cases. Establish `h1` using `mem_sphSpan π w 1 hxf`.

Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hx.1 (Subtype.ext (by simpa using h1))`. Use `hl (LinearMap.ext fun u => ?_)` and prove the remaining obligations. Establish `h1 : u.1 ∈ sphSpan π w` using `by rw [h]; exact u.2`. Take `⟨y, hy, e⟩` from `hker h1`.

Rewrite using `[LinearMap.zero_apply, ← Subtype.ext (a1 := y) (a2 := u) e]`. Conclude with `hy`.
-/
theorem exists_translate_ne_zero : G2 := by
  intro E _ _ _ a π w B hB l hl
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hfix : ∀ v : π.V, IsFix π w v → v ≠ 0 → IsSatVecGL w (π.locRep w) v B := fun v hv h0 =>
    hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0
  have hxf : IsFix π w x := GlobalTheory.LGrp.mem_fixed.1 hx.2.1
  have hker : sphSpan π w ≤ (LinearMap.ker l).map π.V.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, v, hv, rfl⟩
    refine ⟨π.locRep w g v, ?_, rfl⟩
    by_cases h0 : v = 0
    · simp [h0]
    · exact hcon v g (hfix v hv h0)
  rcases π.irred _ (sphSpan_le π w) (isStable_sphSpan π w) with h | h
  · have h1 := mem_sphSpan π w 1 hxf
    rw [h, Submodule.mem_bot] at h1
    exact hx.1 (Subtype.ext (by simpa using h1))
  · refine hl (LinearMap.ext fun u => ?_)
    have h1 : u.1 ∈ sphSpan π w := by rw [h]; exact u.2
    obtain ⟨y, hy, e⟩ := hker h1
    rw [LinearMap.zero_apply, ← Subtype.ext (a1 := y) (a2 := u) e]
    exact hy

end GlobalTheory.CompanionTheory.SatakeBound

end
