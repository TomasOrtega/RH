import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp

open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal

/- English proof (translation)
Introduce `F L _ _ _ _ _ h2 w w' hne hunder`. Use `set v := HeightOneSpectrum.under (𝓞 F) w with hv`. Use `haveI hw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩`. Use `haveI hw' : w'.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hunder).symm⟩`. Establish `hsum` using `sum_ramificationIdx_mul_inertiaDeg L v`.

Rewrite `hsum` using `[h2]`. Establish `hpos : ∀ u : PlacesOver L v, 1 ≤ (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) * (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F)` using `fun u => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)`. Set `a : PlacesOver L v` to `⟨w, hw⟩`. Set `b : PlacesOver L v` to `⟨w', hw'⟩`. Establish `hab : a ≠ b` using `fun h => hne (congrArg Subtype.val h).symm`.

Establish `hle` using `Finset.add_le_sum (s := Finset.univ) (f := fun u : PlacesOver L v => (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) * (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) hab`. Establish `hle2` using `hle.trans_eq hsum`. Establish `ha1` using `hpos a`. Establish `hb1` using `hpos b`. Establish `h1 : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1`.

Express the relevant statement in the definitionally equal form `_ + _ ≤ 2 at hle2`. Express the relevant statement in the definitionally equal form `1 ≤ w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) at ha1`. Express the relevant statement in the definitionally equal form `1 ≤ w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) at hb1`. Express the relevant statement in the definitionally equal form `w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) + w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle2`. Use linear arithmetic over natural numbers and integers.

Establish `he : w.asIdeal.ramificationIdx (𝓞 F) = 1` using `Nat.eq_one_of_mul_eq_one_right h1`. Establish `hfin : Module.finrank (v.adicCompletion F) (w.adicCompletion L) = 1`. Rewrite using `[finrank_eq_ramificationIdx_mul_inertiaDeg L v w, h1]`. Establish `hbij : Function.Bijective (completionMap v w)` using `Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin`. Set `e` to `RingEquiv.ofBijective (completionMap v w) hbij`.

Use `⟨(e.symm : w.adicCompletion L →+* v.adicCompletion F), ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.DenseCompl.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective L w) _ ?_` and prove the remaining obligations. Introduce `y`. Take `⟨x, rfl⟩` from `hbij.2 y`. Establish `hx : (e.symm : w.adicCompletion L →+* v.adicCompletion F) (completionMap v w x) = x` using `e.symm_apply_apply x`.

Rewrite using `[hx, valued_completionMap, he, pow_one]`. Introduce `x`. Conclude with `e.symm_apply_apply x`.
-/
theorem UpperTheory.V.Af.Tw.splitIso :
    UpperTheory.V.Af.Tw.SplitIso := by
  intro F L _ _ _ _ _ h2 w w' hne hunder
  classical
  set v := HeightOneSpectrum.under (𝓞 F) w with hv
  haveI hw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  haveI hw' : w'.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hunder).symm⟩
  have hsum := sum_ramificationIdx_mul_inertiaDeg L v
  rw [h2] at hsum
  have hpos : ∀ u : PlacesOver L v, 1 ≤ (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F) := fun u =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  let a : PlacesOver L v := ⟨w, hw⟩
  let b : PlacesOver L v := ⟨w', hw'⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h).symm
  have hle := Finset.add_le_sum (s := Finset.univ)
    (f := fun u : PlacesOver L v => (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) hab
  have hle2 := hle.trans_eq hsum
  have ha1 := hpos a
  have hb1 := hpos b
  have h1 : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    change _ + _ ≤ 2 at hle2
    change 1 ≤ w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) at ha1
    change 1 ≤ w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) at hb1
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) +
      w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle2
    omega
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hfin : Module.finrank (v.adicCompletion F) (w.adicCompletion L) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w, h1]
  have hbij : Function.Bijective (completionMap v w) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
  let e := RingEquiv.ofBijective (completionMap v w) hbij
  refine ⟨(e.symm : w.adicCompletion L →+* v.adicCompletion F), ?_, ?_⟩
  · refine GlobalTheory.DenseCompl.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective L w) _ ?_
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    have hx : (e.symm : w.adicCompletion L →+* v.adicCompletion F) (completionMap v w x) = x :=
      e.symm_apply_apply x
    rw [hx, valued_completionMap, he, pow_one]
  · intro x
    exact e.symm_apply_apply x
