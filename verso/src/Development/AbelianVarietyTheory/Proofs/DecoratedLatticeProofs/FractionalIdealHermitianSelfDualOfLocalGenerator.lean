import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FinPl.SelfDualIdeal

variable {D : D7}
open GlobalTheory.FinPlLoc

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg₁ {R : Type} [CommRing R] {u u' w w' e : R} (hU : u' * u = 1) (hC : w' * w = 1) (he : e * e = e)
    (c d h : R) : e * (c * d * h) = u * w * h * (u' * (e * d) * (w' * (e * c))) := by
  calc _ = (u' * u) * (w' * w) * (e * e) * (c * d * h) := by rw [hU, hC, he, one_mul, one_mul]
    _ = _ := by ring

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg₂ {R : Type} [CommRing R] {u u' : R} (hU : u' * u = 1) (w e d h : R) :
    u * w * h * (u' * (e * d)) = d * h * (w * e) := by
  calc _ = (u' * u) * (d * h * (w * e)) := by ring
    _ = _ := by rw [hU, one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg₃ {R : Type} [CommRing R] {u u' e : R} (hU : u' * u = 1) (he : e * e = e) (d y : R) :
    e * (d * y) = u' * (e * d) * (y * (u * e)) := by
  calc _ = (u' * u) * (e * e) * (d * y) := by rw [hU, he, one_mul]
    _ = _ := by ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨Ideal.mul_mem_right _ _ ha.1, by rw [RingHom.map_mul (finPart D) a b]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩`.
-/
theorem intAt_mul {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [RingHom.map_mul (finPart D) a b]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

/- English proof (translation)
Use `⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩` and prove the remaining obligations. Establish `h` using `congrArg (cA D) ((mem_idAt_iff _ a).1 ha.1)`. Rewrite `h` using `[RingHom.map_mul (cA D), cA_idem]`. Conclude with `(mem_idAt_iff _ _).2 h`.
-/
theorem cA_mem_intAt {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := congrArg (cA D) ((mem_idAt_iff _ a).1 ha.1)
  rw [RingHom.map_mul (cA D), cA_idem] at h
  exact (mem_idAt_iff _ _).2 h

/- English proof (translation)
Rewrite using `[mul_comm, idem, GlobalTheory.IdVGen.incA_mul_tmul, mul_one]`.
-/
theorem idem_mul_incA (P : Pl D → Prop) (y : D.host.E) :
    idem D P * incA D y = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] y := by
  rw [mul_comm, idem, GlobalTheory.IdVGen.incA_mul_tmul, mul_one]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg hw], c, hc, idem_mul_incA _ c⟩`.
-/
theorem idem_mul_incA_mem {𝔞 : FI D} {c : D.host.E} (hc : c ∈ 𝔞) (v : Pl D) : idem D (· = v) * incA D c ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg hw], c, hc,
    idem_mul_incA _ c⟩

/- English proof (translation)
Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨α, hα, h0, c, hc, rfl⟩` from `hz`. Take `⟨b, hb⟩` from `hy c hc`. Rewrite using `[GlobalTheory.IdVGen.incA_mul_tmul, ← hb]`.

Conclude with `GlobalTheory.IdVGen.gen_mem_intAt hα h0 b`. Consider the case `zero => rw [mul_zero]`. Conclude with `GlobalTheory.IdVGen.intAt_zero' v`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `GlobalTheory.IdVGen.intAt_add' ha hb`.

Consider the case `neg a _ ha => rw [mul_neg]`. Conclude with `GlobalTheory.IdVGen.intAt_neg' ha`.
-/
theorem mul_incA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    rw [GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

/- English proof (translation)
Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨α, hα, h0, c, hc, rfl⟩` from `hz`. Take `⟨b, hb⟩` from `hy c hc`. Establish `e : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star c` using `rfl`.

Rewrite using `[e, GlobalTheory.IdVGen.incA_mul_tmul, ← hb]`. Conclude with `GlobalTheory.IdVGen.gen_mem_intAt hα h0 b`. Consider the case `zero => rw [RingHom.map_zero, mul_zero]`. Conclude with `GlobalTheory.IdVGen.intAt_zero' v`. Consider the case `add a b _ _ ha hb => rw [RingHom.map_add, mul_add]`.

Conclude with `GlobalTheory.IdVGen.intAt_add' ha hb`. Consider the case `neg a _ ha => rw [RingHom.map_neg, mul_neg]`. Conclude with `GlobalTheory.IdVGen.intAt_neg' ha`.
-/
theorem mul_cA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * star c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * cA D s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    have e : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star c := rfl
    rw [e, GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [RingHom.map_zero, mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [RingHom.map_add, mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [RingHom.map_neg, mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

/- English proof (translation)
Take `⟨m, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (Rₘ := ℚ) y (Algebra.IsIntegral.isIntegral y)`. Use `⟨((m : ℤ) : 𝓞 D.host.F), Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero m), ⟨m • y, hm⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m : ℤ) • y = _`. Simplify using `[zsmul_eq_mul]`.
-/
theorem exists_int_mul (y : D.host.E) : ∃ t : 𝓞 D.host.F, t ≠ 0 ∧ ∃ b : 𝓞 D.host.E,
    (b : D.host.E) = algebraMap D.host.F D.host.E (t : D.host.F) * y := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (Rₘ := ℚ) y
    (Algebra.IsIntegral.isIntegral y)
  refine ⟨((m : ℤ) : 𝓞 D.host.F), Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero m), ⟨m • y, hm⟩, ?_⟩
  change (m : ℤ) • y = _
  simp [zsmul_eq_mul]

/- English proof (translation)
Establish `key : ∀ w, evalV D.host.F w (1 : Af D.host.F) = evalV D.host.F w (∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T))`. Introduce `w`. Rewrite using `[map_one, map_add, map_sum]`. Simplify using `only [evalV_ePl]`. Apply the tactic sequence `by_cases hw : w ∈ T <;> simp [hw]`.

Conclude with `RestrictedProduct.ext _ _ fun w => key w`.
-/
theorem one_eq_sum (T : Finset (Pl D)) :
    (1 : Af D.host.F) = ∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T) := by
  classical
  have key : ∀ w, evalV D.host.F w (1 : Af D.host.F) =
      evalV D.host.F w (∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T)) := by
    intro w
    rw [map_one, map_add, map_sum]
    simp only [evalV_ePl]
    by_cases hw : w ∈ T <;> simp [hw]
  exact RestrictedProduct.ext _ _ fun w => key w

/- English proof (translation)
Take `⟨t, ht0, b, hb⟩` from `exists_int_mul y`. Establish `hF : (t : D.host.F) ≠ 0` using `by exact_mod_cast ht0`. Establish `hfin` using `Ideal.finite_factors (I := Ideal.span {t}) (by simpa using ht0)`. Establish `h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] y ∈ intAE D`. Rewrite using `[one_eq_sum hfin.toFinset, TensorProduct.add_tmul, TensorProduct.sum_tmul]`.

Use `add_mem (sum_mem fun v _ => ?_) ?_` and prove the remaining obligations. Use `(h v).2` as an intermediate fact. Rewrite `this` using `[idem_mul_incA, finPart_pair]`. Then use the resulting hypothesis. Use `AddSubgroup.subset_closure ⟨(t : D.host.F)⁻¹ • ePl D (· ∉ hfin.toFinset), fun w => ?_, b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, evalV_ePl]`.

Distinguish the cases in `hw : w ∈ hfin.toFinset`. Rewrite using `[if_neg (not_not.2 hw), smul_zero]`. Conclude with `zero_mem _`. Rewrite using `[if_pos hw, Algebra.smul_def, mul_one]`. Use `GlobalTheory.IdVGen.inv_mem_integers fun hm => hw ?_` and prove the remaining obligations.

Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]`. Conclude with `hm`. Rewrite using `[hb, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hF, one_smul]`. Establish `h2 : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F ((1 : FI D) : Set D.host.E)`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, y, rfl⟩`. Conclude with `GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)`. Conclude with `(FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 y).1 (h2 h1))`.
-/
theorem exists_integer_of_forall (y : D.host.E) (h : ∀ v : Pl D, idem D (· = v) * incA D y ∈ intAt D (· = v)) :
    ∃ b : 𝓞 D.host.E, (b : D.host.E) = y := by
  classical
  obtain ⟨t, ht0, b, hb⟩ := exists_int_mul y
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hfin := Ideal.finite_factors (I := Ideal.span {t}) (by simpa using ht0)
  have h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] y ∈ intAE D := by
    rw [one_eq_sum hfin.toFinset, TensorProduct.add_tmul, TensorProduct.sum_tmul]
    refine add_mem (sum_mem fun v _ => ?_) ?_
    · have := (h v).2
      rwa [idem_mul_incA, finPart_pair] at this
    · refine AddSubgroup.subset_closure ⟨(t : D.host.F)⁻¹ • ePl D (· ∉ hfin.toFinset), fun w => ?_, b, ?_⟩
      · rw [map_smul, evalV_ePl]
        by_cases hw : w ∈ hfin.toFinset
        · rw [if_neg (not_not.2 hw), smul_zero]; exact zero_mem _
        · rw [if_pos hw, Algebra.smul_def, mul_one]
          refine GlobalTheory.IdVGen.inv_mem_integers fun hm => hw ?_
          rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
          exact hm
      · rw [hb, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hF, one_smul]
  have h2 : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F ((1 : FI D) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 y).1 (h2 h1))

/- English proof (translation)
Introduce `h`. Use `compAt_idem (· = v) v` as an intermediate fact. Rewrite `this` using `[h, if_pos rfl, RingHom.map_zero]`. Conclude with `zero_ne_one this`.
-/
theorem idem_ne_zero (v : Pl D) : idem D (· = v) ≠ 0 := by
  intro h
  have := compAt_idem (· = v) v
  rw [h, if_pos rfl, RingHom.map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Introduce `D h 𝔞 u H1 H2 d`. Establish `hU : ((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) = 1` using `u.inv_mul`. Establish `hC : cA D ((u⁻¹ : (AE D)ˣ) : AE D) * cA D (u : AE D) = 1`. Rewrite using `[← RingHom.map_mul (cA D), hU, RingHom.map_one]`. Generalize the expression as in `((u⁻¹ : (AE D)ˣ) : AE D) = u' at H1 hU hC`.

Generalize the expression as in `(u : AE D) = u at H2 hU hC`. Establish `hue : ∀ v, u * idem D (· = v) ∈ idV 𝔞 v` using `fun v => (H1 v _ (Ideal.mul_mem_left _ _ (idem_mem_idAt _))).2 (by rw [← mul_assoc, hU, one_mul]; exact idem_mem_intAt _)`. Establish `loc : ∀ v, ∀ x ∈ 𝔞, u' * (idem D (· = v) * incA D x) ∈ intAt D (· = v)` using `fun v x hx => (H1 v _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1 (idem_mul_incA_mem hx v)`. Prove the components needed by the constructor for the conclusion. Introduce `hd c hc`.

Use `exists_integer_of_forall _ fun v => ?_` and prove the remaining obligations. Establish `h3` using `intAt_mul (loc v d hd) (cA_mem_intAt (loc v c hc))`. Establish `h4` using `(H2 v _ h3.1).1 h3`. Establish `he` using `idem_mul_self (D := D) (· = v)`. Rewrite `h4` using `[RingHom.map_mul (cA D), RingHom.map_mul (cA D), cA_idem, GlobalTheory.FinPl.FrameLat.cA_incA]`.

Rewrite using `[RingHom.map_mul (incA D), RingHom.map_mul (incA D), alg₁ hU hC he]`. Conclude with `h4`. Introduce `hd`. Establish `h𝔞 : 𝔞 ≠ 0`. Introduce and unpack `rfl`.

Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 D.host.F)`. Set `v : Pl D` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩`. Establish `h0` using `hue v`. Rewrite `h0` using `[idV_zero, AddSubgroup.mem_bot]`. Apply `idem_ne_zero v` to reduce the goal to its premises.

Rewrite using `[← one_mul (idem D (· = v)), ← hU, mul_assoc, h0, mul_zero]`. Establish `s1 : ∀ v, u' * (idem D (· = v) * incA D d) ∈ intAt D (· = v)`. Introduce `v`. Establish `hc` using `mul_cA_mem (y := d * h) (fun c hc => by`. Take `⟨b, hb⟩` from `hd c hc`.

Conclude with `⟨b, by rw [hb]; ring⟩) (hue v)`. Use `(H2 v _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _)))).2 ?_` and prove the remaining obligations. Rewrite `hc` using `[RingHom.map_mul (cA D), cA_idem, RingHom.map_mul (incA D)]`. Rewrite using `[alg₂ hU]`. Conclude with `hc`.

Rewrite using `[← inv_inv 𝔞, FractionalIdeal.mem_inv_iff (inv_ne_zero h𝔞)]`. Introduce `y hy`. Use `(FractionalIdeal.mem_one_iff _).2 (exists_integer_of_forall _ fun v => ?_)` and prove the remaining obligations. Establish `t` using `mul_incA_mem (y := y) (fun c hc => (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff h𝔞).1 hy c hc)) (hue v)`. Establish `h5` using `intAt_mul (s1 v) t`.

Establish `he` using `idem_mul_self (D := D) (· = v)`. Rewrite using `[RingHom.map_mul (incA D), alg₃ hU he]`. Conclude with `h5`.
-/
theorem selfDual_of_local : ∀ (D : D7) (h : D.host.E) (𝔞 : FI D) (u : (AE D)ˣ), (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) → (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (u : AE D) * cA D (u : AE D) * incA D h * a ∈ intAt D (· = x)) → ∀ d : D.host.E, d ∈ 𝔞 ↔ ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * h := by
  intro D h 𝔞 u H1 H2 d
  have hU : ((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) = 1 := u.inv_mul
  have hC : cA D ((u⁻¹ : (AE D)ˣ) : AE D) * cA D (u : AE D) = 1 := by
    rw [← RingHom.map_mul (cA D), hU, RingHom.map_one]
  generalize ((u⁻¹ : (AE D)ˣ) : AE D) = u' at H1 hU hC
  generalize (u : AE D) = u at H2 hU hC
  have hue : ∀ v, u * idem D (· = v) ∈ idV 𝔞 v := fun v =>
    (H1 v _ (Ideal.mul_mem_left _ _ (idem_mem_idAt _))).2 (by rw [← mul_assoc, hU, one_mul]; exact idem_mem_intAt _)
  have loc : ∀ v, ∀ x ∈ 𝔞, u' * (idem D (· = v) * incA D x) ∈ intAt D (· = v) := fun v x hx =>
    (H1 v _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1 (idem_mul_incA_mem hx v)
  constructor
  · intro hd c hc
    refine exists_integer_of_forall _ fun v => ?_
    have h3 := intAt_mul (loc v d hd) (cA_mem_intAt (loc v c hc))
    have h4 := (H2 v _ h3.1).1 h3
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (cA D), RingHom.map_mul (cA D), cA_idem, GlobalTheory.FinPl.FrameLat.cA_incA] at h4
    rw [RingHom.map_mul (incA D), RingHom.map_mul (incA D), alg₁ hU hC he]
    exact h4
  · intro hd
    have h𝔞 : 𝔞 ≠ 0 := by
      rintro rfl
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : Pl D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      have h0 := hue v
      rw [idV_zero, AddSubgroup.mem_bot] at h0
      apply idem_ne_zero v
      rw [← one_mul (idem D (· = v)), ← hU, mul_assoc, h0, mul_zero]
    have s1 : ∀ v, u' * (idem D (· = v) * incA D d) ∈ intAt D (· = v) := by
      intro v
      have hc := mul_cA_mem (y := d * h) (fun c hc => by
        obtain ⟨b, hb⟩ := hd c hc
        exact ⟨b, by rw [hb]; ring⟩) (hue v)
      refine (H2 v _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _)))).2 ?_
      rw [RingHom.map_mul (cA D), cA_idem, RingHom.map_mul (incA D)] at hc
      rw [alg₂ hU]; exact hc
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff (inv_ne_zero h𝔞)]
    intro y hy
    refine (FractionalIdeal.mem_one_iff _).2 (exists_integer_of_forall _ fun v => ?_)
    have t := mul_incA_mem (y := y) (fun c hc =>
      (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff h𝔞).1 hy c hc)) (hue v)
    have h5 := intAt_mul (s1 v) t
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (incA D), alg₃ hU he]
    exact h5

end GlobalTheory.FinPl.SelfDualIdeal

end
