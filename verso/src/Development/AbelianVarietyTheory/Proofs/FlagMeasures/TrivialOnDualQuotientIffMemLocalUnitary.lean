import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemDualSetOfMemSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualOfDualFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOneStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FunFix

section Abstract

variable {A : Type} [CommRing A] {k : ℕ} (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A)

/- English proof (translation)
Simplify using `only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hform_sub_left (x x' y : Fin k → A) : hform τ J (x - x') y = hform τ J x y - hform τ J x' y := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hform_sub_right (x y y' : Fin k → A) : hform τ J x (y - y') = hform τ J x y - hform τ J x y' := by
  simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, map_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_swap (c : A) (x y : Fin k → A) : hform τ J x (τ c • y) = hform τ J (c • x) y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `h : cT τ g.1 * J * g.1 = J` using `hg`. Rewrite using `[GlobalTheory.DualFrame.hform_mulVec, mulVec_mulVec, h, GlobalTheory.DualFrame.hform_eq_dot]`.
-/
theorem hform_unitary {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform τ J x y := by
  have h : cT τ g.1 * J * g.1 = J := hg
  rw [GlobalTheory.DualFrame.hform_mulVec, mulVec_mulVec, h, GlobalTheory.DualFrame.hform_eq_dot]

/- English proof (translation)
Rewrite using `[← hform_unitary τ J hg ((g⁻¹).1 *ᵥ x) y, mulVec_mulVec, Units.mul_inv, one_mulVec]`.
-/
theorem hform_move {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J x (g.1 *ᵥ y) = hform τ J ((g⁻¹).1 *ᵥ x) y := by
  rw [← hform_unitary τ J hg ((g⁻¹).1 *ᵥ x) y, mulVec_mulVec, Units.mul_inv, one_mulVec]

variable {τ J} {O : Subring A} {L D : Submodule O (Fin k → A)}

/- English proof (translation)
Take `⟨hu, hs⟩` from `hg`. Introduce `y`. Rewrite using `[hD, hD]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Rewrite using `[hform_move τ J hu]`. Conclude with `h _ (((stabGL L).inv_mem hs x).1 hx)`. Introduce `h x hx`. Rewrite using `[← hform_unitary τ J hu]`. Conclude with `h _ ((hs x).1 hx)`.
-/
theorem stab_dual (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O) {g : GL (Fin k) A}
    (hg : g ∈ level τ J L) : g ∈ stabGL D := by
  obtain ⟨hu, hs⟩ := hg
  intro y
  rw [hD, hD]
  constructor
  · intro h x hx
    rw [hform_move τ J hu]
    exact h _ (((stabGL L).inv_mem hs x).1 hx)
  · intro h x hx
    rw [← hform_unitary τ J hu]
    exact h _ ((hs x).1 hx)

/- English proof (translation)
Establish `hgD` using `stab_dual hD hg`. Establish `hval : ∀ (x : D) (a : O), x.1 - a.1 • d ∈ L → f x = a • f ⟨d, hd⟩`. Introduce `x a h`. Rewrite using `[← map_smul, ← sub_eq_zero, ← map_sub]`. Conclude with `hfL _ h`.

Establish `hfd : f ⟨d, hd⟩ ≠ 0`. Introduce `h`. Apply `hf0` to reduce the goal to its premises. Use extensionality with `x`. Take `⟨a, ha, hx⟩` from `hgen x.1 x.2`.

Rewrite using `[hval x ⟨a, ha⟩ hx, h, smul_zero]`. Both sides reduce to the same expression. Establish `hker : ∀ x : D, f x = 0 → e • x.1 ∈ L`. Introduce `x hx0`. Take `⟨a, ha, hx⟩` from `hgen x.1 x.2`.

Break down `hfield ⟨a, ha⟩ with ⟨b, hb⟩ | h` into its components or cases. It suffices to derive a contradiction. Apply `hfd` to reduce the goal to its premises. Rewrite using `[← hact (f ⟨d, hd⟩), ← hb, mul_smul, hact, mul_smul, ← hval x ⟨a, ha⟩ hx, hx0, smul_zero]`. Establish `h1` using `L.add_mem (L.smul_mem e hx) (h d hd)`.

Establish `h2 : e • (x.1 - a • d) + (e * ⟨a, ha⟩) • d = e • x.1`. Rewrite using `[smul_sub, mul_smul]`. Conclude with `sub_add_cancel _ _`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Establish `hhalf : ∀ g' ∈ stabFun D f, ∀ x ∈ D, e • (g'.1 *ᵥ x - x) ∈ L`.

Introduce and unpack `g' ⟨h1, h2⟩ x hx`. Use `hker (⟨g'.1 *ᵥ x, (h1 x).1 hx⟩ - ⟨x, hx⟩) ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `h2 ⟨x, hx⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨hgD, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← map_sub]`. Use `hfL _ ?_` and prove the remaining obligations. Use `h x.1 x.2` as an intermediate fact.

Rewrite `this` using `[sub_mulVec, one_mulVec]`. Then use the resulting hypothesis. Introduce `h x hx`. Rewrite using `[sub_mulVec, one_mulVec]`. Establish `h1` using `hhalf g h x hx`. Establish `h2 : τ e • (g.1 *ᵥ x - x) ∈ L`.

Rewrite using `[hL]`. Introduce `z hz`. Rewrite using `[hform_smul_swap, hform_sub_right, hform_move τ J hg.1, ← hform_sub_left, mulVec_smul, ← smul_sub]`. Conclude with `(hD x).1 hx _ (hhalf g⁻¹ ((stabFun D f).inv_mem h) z hz)`. Establish `h3` using `L.add_mem h1 h2`.

Establish `h4 : e • (g.1 *ᵥ x - x) + τ e • (g.1 *ᵥ x - x) = g.1 *ᵥ x - x`. Rewrite using `[hτe, sub_smul, one_smul]`. Conclude with `add_sub_cancel _ _`. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis.
-/
theorem triv_iff_stabFun (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ D, hform τ J x y ∈ O)
    {M : Type} [AddCommGroup M] [Module O M] (f : D →ₗ[O] M) (hf0 : f ≠ 0)
    (hfL : ∀ x : D, x.1 ∈ L → f x = 0) (e : O) (hτe : τ e = 1 - e) (hact : ∀ m : M, e • m = m)
    (hfield : ∀ a : O, (∃ b : O, b * a * e = e) ∨ ∀ x ∈ D, (e * a) • x ∈ L)
    (d : Fin k → A) (hd : d ∈ D) (hgen : ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ L)
    {g : GL (Fin k) A} (hg : g ∈ level τ J L) :
    (∀ x ∈ D, (g.1 - 1) *ᵥ x ∈ L) ↔ g ∈ stabFun D f := by
  have hgD := stab_dual hD hg
  have hval : ∀ (x : D) (a : O), x.1 - a.1 • d ∈ L → f x = a • f ⟨d, hd⟩ := by
    intro x a h
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact hfL _ h
  have hfd : f ⟨d, hd⟩ ≠ 0 := by
    intro h
    apply hf0
    ext x
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rw [hval x ⟨a, ha⟩ hx, h, smul_zero]
    rfl
  have hker : ∀ x : D, f x = 0 → e • x.1 ∈ L := by
    intro x hx0
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rcases hfield ⟨a, ha⟩ with ⟨b, hb⟩ | h
    · exfalso
      apply hfd
      rw [← hact (f ⟨d, hd⟩), ← hb, mul_smul, hact, mul_smul, ← hval x ⟨a, ha⟩ hx, hx0, smul_zero]
    · have h1 := L.add_mem (L.smul_mem e hx) (h d hd)
      have h2 : e • (x.1 - a • d) + (e * ⟨a, ha⟩) • d = e • x.1 := by
        rw [smul_sub, mul_smul]
        exact sub_add_cancel _ _
      rwa [h2] at h1
  have hhalf : ∀ g' ∈ stabFun D f, ∀ x ∈ D, e • (g'.1 *ᵥ x - x) ∈ L := by
    rintro g' ⟨h1, h2⟩ x hx
    refine hker (⟨g'.1 *ᵥ x, (h1 x).1 hx⟩ - ⟨x, hx⟩) ?_
    rw [map_sub, sub_eq_zero]
    exact h2 ⟨x, hx⟩
  constructor
  · intro h
    refine ⟨hgD, fun x => ?_⟩
    rw [← sub_eq_zero, ← map_sub]
    refine hfL _ ?_
    have := h x.1 x.2
    rwa [sub_mulVec, one_mulVec] at this
  · intro h x hx
    rw [sub_mulVec, one_mulVec]
    have h1 := hhalf g h x hx
    have h2 : τ e • (g.1 *ᵥ x - x) ∈ L := by
      rw [hL]
      intro z hz
      rw [hform_smul_swap, hform_sub_right, hform_move τ J hg.1, ← hform_sub_left, mulVec_smul, ← smul_sub]
      exact (hD x).1 hx _ (hhalf g⁻¹ ((stabFun D f).inv_mem h) z hz)
    have h3 := L.add_mem h1 h2
    have h4 : e • (g.1 *ᵥ x - x) + τ e • (g.1 *ᵥ x - x) = g.1 *ᵥ x - x := by
      rw [hτe, sub_smul, one_smul]
      exact add_sub_cancel _ _
    rwa [h4] at h3

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Use `isSimpleAddGroup_of_prime_card hG` as an intermediate fact. Break down `IsSimpleAddGroup.eq_bot_or_eq_top_of_normal (DistribSMul.toAddMonoidHom G e).range inferInstance with h | h` into its components or cases. Use `left`. Introduce `y`.

Conclude with `AddSubgroup.mem_bot.1 (h ▸ ⟨y, rfl⟩)`. Use `right`. Introduce `y`. Establish `hy : y ∈ (DistribSMul.toAddMonoidHom G e).range` using `by rw [h]; exact AddSubgroup.mem_top y`. Take `⟨z, hz⟩` from `AddMonoidHom.mem_range.1 hy`.

Rewrite using `[← hz]`. Use `show e • e • z = e • z`. Rewrite using `[smul_smul, he]`.
-/
theorem idem_act {R : Type} [Ring R] {G : Type} [AddCommGroup G] [Module R G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : R} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  have : Fact p.Prime := ⟨hp⟩
  have := isSimpleAddGroup_of_prime_card hG
  rcases IsSimpleAddGroup.eq_bot_or_eq_top_of_normal (DistribSMul.toAddMonoidHom G e).range inferInstance
    with h | h
  · left
    intro y
    exact AddSubgroup.mem_bot.1 (h ▸ ⟨y, rfl⟩)
  · right
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [h]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

/- English proof (translation)
Establish `ha` using `((hint a).1 a.2).1`. Establish `hm : ∀ c : V, sp.symm (c, 0) ∈ O` using `fun c => by`. Rewrite using `[hint, sp.apply_symm_apply]`. Conclude with `⟨c.2, zero_mem _⟩`. Distinguish the cases in `hu : IsUnit (⟨_, ha⟩ : V)`.

Take `⟨b, hb⟩` from `hu.exists_left_inv`. Establish `hb' : (b : K) * (sp a).1 = 1` using `congrArg Subtype.val hb`. Use `Or.inl ⟨⟨_, hm b⟩, Subtype.ext (sp.injective ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `sp (sp.symm (b, 0) * a * e) = sp e`. Rewrite using `[map_mul, map_mul, sp.apply_symm_apply, he]`.

Apply the tactic sequence `ext <;> simp [hb']`. Establish `h1 : (⟨_, ha⟩ : V) ∈ IsLocalRing.maximalIdeal V` using `hu`. Rewrite `h1` using `[hmax, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `h1`. Establish `hc' : (c : K) * T = (sp a).1` using `by simpa using congrArg Subtype.val hc`.

Use `Or.inr ⟨⟨_, hm c⟩, Subtype.ext (sp.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, map_mul, map_mul, sp.apply_symm_apply, he, map_natCast]`. Apply the tactic sequence `ext <;> simp [hc']`.
-/
theorem unit_or_dvd {K : Type} [Field K] (V : ValuationSubring K) (T : ℕ)
    (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(T : V)}) (sp : A ≃+* K × K)
    (hint : ∀ x, x ∈ O ↔ (sp x).1 ∈ V ∧ (sp x).2 ∈ V) (e : O) (he : sp e = (1, 0)) (a : O) :
    (∃ b : O, b * a * e = e) ∨ ∃ c : O, e * a = c * T := by
  have ha := ((hint a).1 a.2).1
  have hm : ∀ c : V, sp.symm (c, 0) ∈ O := fun c => by
    rw [hint, sp.apply_symm_apply]; exact ⟨c.2, zero_mem _⟩
  by_cases hu : IsUnit (⟨_, ha⟩ : V)
  · obtain ⟨b, hb⟩ := hu.exists_left_inv
    have hb' : (b : K) * (sp a).1 = 1 := congrArg Subtype.val hb
    refine Or.inl ⟨⟨_, hm b⟩, Subtype.ext (sp.injective ?_)⟩
    change sp (sp.symm (b, 0) * a * e) = sp e
    rw [map_mul, map_mul, sp.apply_symm_apply, he]
    ext <;> simp [hb']
  · have h1 : (⟨_, ha⟩ : V) ∈ IsLocalRing.maximalIdeal V := hu
    rw [hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' : (c : K) * T = (sp a).1 := by simpa using congrArg Subtype.val hc
    refine Or.inr ⟨⟨_, hm c⟩, Subtype.ext (sp.injective ?_)⟩
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, map_mul, map_mul, sp.apply_symm_apply, he, map_natCast]
    ext <;> simp [hc']

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish `: intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F))`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨_, (⟨σ a, (a.isIntegral_coe).map (σ.restrictScalars ℤ)⟩ : 𝓞 E), rfl⟩, rfl⟩)`. Use `show (σ 1) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v`.

Rewrite using `[map_one]`. Conclude with `Subring.subset_closure (Or.inr ⟨a, rfl⟩)`. Conclude with `this`.
-/
theorem sigR_mem (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ a ∈ intV E v, sigR σ (v.adicCompletion F) a ∈ intV E v := by
  have : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨_, (⟨σ a, (a.isIntegral_coe).map (σ.restrictScalars ℤ)⟩ : 𝓞 E), rfl⟩, rfl⟩)
    · show (σ 1) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  exact this

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨_, h y hy, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [Nat.cast_smul_eq_nsmul, Pi.smul_apply, map_nsmul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul a b _ hb => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hb`.
-/
theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L L' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ L', (T : E) • x ∈ L) : ∀ x ∈ loc v L', (T : intV E v) • x ∈ loc v L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h y hy, ?_⟩
    funext i
    simp only [Nat.cast_smul_eq_nsmul, Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

end Local

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm n J hJ hdet T f bad S hT hsp hdeg v hv y hy`. Take `⟨-, d, hd, hgen⟩` from `GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one F E cm n J hJ hdet T f S.Lb hT hsp hdeg (stepLevel_tLat F E n cm.sig J T f bad S) v hv`. Take `⟨-, hmax, sp, hsig, hdiag⟩` from `(GlobalTheory.T.cmField_splitCompletely_place_structure F E cm T hT hsp).2 v hv`. Establish `hint : ∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F` using `split_integral_local F E v sp hdiag`. Take `⟨B, C, hBC, hB, hC⟩` from `GlobalTheory.DualFrame.exists_dual_frames F E cm.sig n J (isUnit_iff_ne_zero.2 hdet) S.Lb S.Lb_fin S.Lb_span v`.

Take `⟨hD, hL, -⟩` from `GlobalTheory.DualFrames.dual_of_dual_frames _ (intV E v) (sigR cm.sig (v.adicCompletion F)) (fun a => sp.injective (by rw [hsig, hsig]; rfl)) (sigR_mem _ v) n _ (by ext i j; exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j)) B C _ _ hBC hB hC`. Establish `hTD` using `nsmul_mem_loc v T S.Lb (dualL cm.sig J S.Lb) fun x hx => S.Lb_dual x (GlobalTheory.DualFrame.mem_dualSet_of_mem_span _ _ _ hx)`. Establish `key : ∀ (sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, x ∈ intV E v ↔ (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F) → ∀ e : intV E v, sp' e = (1, 0) → sigR cm.sig (v.adicCompletion F) e = 1 - e → (∀ m : S.fM …`. Introduce `sp' hint' e he hτe hact`. Use `triv_iff_stabFun hD hL (S.fT v hv) (S.fT_ne v hv) (S.fT_L v hv) e hτe hact (fun a => ?_) d hd hgen hy` and prove the remaining obligations.

Use `(unit_or_dvd _ T hmax sp' hint' e he a).imp id ?_` and prove the remaining obligations. Introduce and unpack `⟨c, hc⟩ x hx`. Rewrite using `[hc, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hTD x hx)`. Establish `he : sp.symm (1, 0) ∈ intV E v`.

Rewrite using `[hint, sp.apply_symm_apply]`. Conclude with `⟨one_mem _, zero_mem _⟩`. Establish `hτ : sigR cm.sig (v.adicCompletion F) (sp.symm (1, 0)) = 1 - sp.symm (1, 0)`. Apply `sp.injective` to reduce the goal to its premises. Rewrite using `[hsig, map_sub, map_one, sp.apply_symm_apply]`.

Apply the tactic sequence `ext <;> simp [swapR]`. Establish `hee : (⟨_, he⟩ : intV E v) * ⟨_, he⟩ = ⟨_, he⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `sp.symm (1, 0) * sp.symm (1, 0) = sp.symm (1, 0)`. Rewrite using `[← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[S.UlocAlt v hv, Subgroup.mem_inf, and_iff_right hy]`. Break down `idem_act hT (S.fM_card v hv) hee with h0 | h1` into its components or cases. Use `key (sp.trans RingEquiv.prodComm) (fun x => (hint x).trans and_comm) (1 - ⟨_, he⟩) ?_ ?_ fun m => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RingEquiv.prodComm (sp (1 - sp.symm (1, 0))) = _`.

Rewrite using `[map_sub sp, map_one, sp.apply_symm_apply]`. Apply the tactic sequence `ext <;> simp`. Express the relevant statement in the definitionally equal form `sigR cm.sig (v.adicCompletion F) (1 - sp.symm (1, 0)) = 1 - (1 - sp.symm (1, 0))`. Rewrite using `[map_sub, map_one, hτ]`. Rewrite using `[sub_smul, one_smul, h0, sub_zero]`.

Conclude with `key sp hint ⟨_, he⟩ (sp.apply_symm_apply _) hτ h1`.
-/
theorem trivial_iff_mem_Uloc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f bad S hT hsp hdeg v hv y hy
  obtain ⟨-, d, hd, hgen⟩ := GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one F E cm n J hJ hdet T f S.Lb hT hsp hdeg
    (stepLevel_tLat F E n cm.sig J T f bad S) v hv
  obtain ⟨-, hmax, sp, hsig, hdiag⟩ := (GlobalTheory.T.cmField_splitCompletely_place_structure F E cm T hT hsp).2 v hv
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag
  obtain ⟨B, C, hBC, hB, hC⟩ := GlobalTheory.DualFrame.exists_dual_frames F E cm.sig n J (isUnit_iff_ne_zero.2 hdet) S.Lb
    S.Lb_fin S.Lb_span v
  obtain ⟨hD, hL, -⟩ := GlobalTheory.DualFrames.dual_of_dual_frames _ (intV E v) (sigR cm.sig (v.adicCompletion F))
    (fun a => sp.injective (by rw [hsig, hsig]; rfl)) (sigR_mem _ v) n _
    (by ext i j; exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j))
    B C _ _ hBC hB hC
  have hTD := nsmul_mem_loc v T S.Lb (dualL cm.sig J S.Lb)
    fun x hx => S.Lb_dual x (GlobalTheory.DualFrame.mem_dualSet_of_mem_span _ _ _ hx)
  have key : ∀ (sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
      (∀ x, x ∈ intV E v ↔
        (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F) →
      ∀ e : intV E v, sp' e = (1, 0) → sigR cm.sig (v.adicCompletion F) e = 1 - e →
      (∀ m : S.fM v hv, e • m = m) →
      ((∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ stabFun _ (S.fT v hv)) := by
    intro sp' hint' e he hτe hact
    refine triv_iff_stabFun hD hL (S.fT v hv) (S.fT_ne v hv) (S.fT_L v hv) e hτe hact (fun a => ?_) d hd hgen hy
    refine (unit_or_dvd _ T hmax sp' hint' e he a).imp id ?_
    rintro ⟨c, hc⟩ x hx
    rw [hc, mul_smul]
    exact Submodule.smul_mem _ _ (hTD x hx)
  have he : sp.symm (1, 0) ∈ intV E v := by
    rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
  have hτ : sigR cm.sig (v.adicCompletion F) (sp.symm (1, 0)) = 1 - sp.symm (1, 0) := by
    apply sp.injective
    rw [hsig, map_sub, map_one, sp.apply_symm_apply]
    ext <;> simp [swapR]
  have hee : (⟨_, he⟩ : intV E v) * ⟨_, he⟩ = ⟨_, he⟩ := by
    apply Subtype.ext
    change sp.symm (1, 0) * sp.symm (1, 0) = sp.symm (1, 0)
    rw [← map_mul]
    simp
  rw [S.UlocAlt v hv, Subgroup.mem_inf, and_iff_right hy]
  rcases idem_act hT (S.fM_card v hv) hee with h0 | h1
  · refine key (sp.trans RingEquiv.prodComm) (fun x => (hint x).trans and_comm) (1 - ⟨_, he⟩) ?_ ?_ fun m => ?_
    · change RingEquiv.prodComm (sp (1 - sp.symm (1, 0))) = _
      rw [map_sub sp, map_one, sp.apply_symm_apply]
      ext <;> simp
    · change sigR cm.sig (v.adicCompletion F) (1 - sp.symm (1, 0)) = 1 - (1 - sp.symm (1, 0))
      rw [map_sub, map_one, hτ]
    · rw [sub_smul, one_smul, h0, sub_zero]
  · exact key sp hint ⟨_, he⟩ (sp.apply_symm_apply _) hτ h1

end GlobalTheory.St.G.FunFix
