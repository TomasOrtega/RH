import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmLieAddPSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDivisionStepDecompositionStatement

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogBasis

section Gen

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
  (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)

/- English proof (translation)
Simplify using `only [up, constantCoeff_map, h, map_zero]`.
-/
theorem up_const (h : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp only [up, constantCoeff_map, h, map_zero]

def cobL (h : ∀ i, constantCoeff (μ i) = 0) :
    MvPowerSeries (Fin d) E →ₗ[E] MvPowerSeries (Fin d ⊕ Fin d) E where
  toFun := cob1 (up E μ)
  map_add' := formalCoboundary_add (up_const μ h)
  map_smul' := formalCoboundary_smul (up_const μ h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cobL_apply (h : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) :
    cobL μ h f = cob1 (up E μ) f := rfl

variable {μ}

/- English proof (translation)
Introduce `α` and use `by obtain ⟨a, -, ha⟩ := hf α obtain ⟨b, -, hb⟩ := hg α exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩`.
-/
theorem in_top_add {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f + g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩

/- English proof (translation)
Introduce `α` and use `by obtain ⟨a, -, ha⟩ := hf α obtain ⟨b, -, hb⟩ := hg α exact ⟨a - b, trivial, by rw [map_sub, ha, hb, map_sub]⟩`.
-/
theorem in_top_sub {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f - g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a - b, trivial, by rw [map_sub, ha, hb, map_sub]⟩

/- English proof (translation)
Introduce `α` and use `by obtain ⟨b, -, hb⟩ := hf α exact ⟨a * b, trivial, by rw [map_smul, hb, smul_eq_mul, map_mul]⟩`.
-/
theorem in_top_smul {σ : Type} {f : MvPowerSeries σ E} (a : O) (hf : In (⊤ : Ideal O) f) :
    In (⊤ : Ideal O) (algebraMap O E a • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨a * b, trivial, by rw [map_smul, hb, smul_eq_mul, map_mul]⟩

/- English proof (translation)
Establish `hf' : ∀ α, ∃ b : O, coeff α f = algebraMap O E b` using `fun α => by`. Take `⟨b, -, hb⟩` from `hf α`. Conclude with `⟨b, hb⟩`. Use `choose s hs using hf'`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Use extensionality with `α`. Conclude with `(hs α).trans (coeff_map (algebraMap O E) α s).symm`.
-/
theorem in_top_map {σ : Type} {f : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, f = map (algebraMap O E) s := by
  have hf' : ∀ α, ∃ b : O, coeff α f = algebraMap O E b := fun α => by
    obtain ⟨b, -, hb⟩ := hf α
    exact ⟨b, hb⟩
  choose s hs using hf'
  refine ⟨s, ?_⟩
  ext α
  exact (hs α).trans (coeff_map (algebraMap O E) α s).symm

/- English proof (translation)
Use `⟨map_zero _, fun i => ⟨0, trivial, by simp [lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← cobL_apply μ h, map_zero, map_zero, map_zero]`.
-/
theorem ql_zero (h : ∀ i, constantCoeff (μ i) = 0) : QL μ (⊤ : Ideal O) (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, trivial, by simp [lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩
  rw [← cobL_apply μ h, map_zero, map_zero, map_zero]

/- English proof (translation)
Use `⟨?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hf.1`. Establish `h2` using `hg.1`. Rewrite `h1`, `h2`, the goal using `[← coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[map_add, map_smul, h1, h2, smul_zero, add_zero]`.

Take `⟨a1, -, h1⟩` from `hf.2.1 i`. Take `⟨a2, -, h2⟩` from `hg.2.1 i`. Use `⟨a1 + a * a2, trivial, ?_⟩` and prove the remaining obligations. Simplify using `only [lin] at h1 h2 ⊢`. Rewrite using `[map_add, map_smul, h1, h2, smul_eq_mul, map_add, map_mul]`.

Rewrite using `[← cobL_apply μ h, map_add, map_smul, cobL_apply, cobL_apply]`. Conclude with `in_top_add hf.2.2 (in_top_smul a hg.2.2)`.
-/
theorem ql_add_smul (h : ∀ i, constantCoeff (μ i) = 0) {f g : MvPowerSeries (Fin d) E}
    (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) : QL μ ⊤ (f + algebraMap O E a • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · have h1 := hf.1
    have h2 := hg.1
    rw [← coeff_zero_eq_constantCoeff_apply] at h1 h2 ⊢
    rw [map_add, map_smul, h1, h2, smul_zero, add_zero]
  · obtain ⟨a1, -, h1⟩ := hf.2.1 i
    obtain ⟨a2, -, h2⟩ := hg.2.1 i
    refine ⟨a1 + a * a2, trivial, ?_⟩
    simp only [lin] at h1 h2 ⊢
    rw [map_add, map_smul, h1, h2, smul_eq_mul, map_add, map_mul]
  · rw [← cobL_apply μ h, map_add, map_smul, cobL_apply, cobL_apply]
    exact in_top_add hf.2.2 (in_top_smul a hg.2.2)

/- English proof (translation)
Unfold `comb`. Proceed by induction on `(Finset.univ : Finset ι) using Finset.induction_on with`. Consider the case `empty => simpa using ql_zero h`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, add_comm]`.

Conclude with `ql_add_smul h ih (he a) (b a)`.
-/
theorem ql_comb (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι]
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, QL μ ⊤ (e i)) (b : ι → O) :
    QL μ ⊤ (comb b e) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using ql_zero h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, add_comm]
    exact ql_add_smul h ih (he a) (b a)

/- English proof (translation)
Simplify using `only [comb, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem comb_sub {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (b b' : ι → O) :
    comb (b - b') e = comb b e - comb b' e := by
  simp only [comb, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

end Gen

section Chart

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
  {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {E : Type} [CommRing E] [Algebra O E]
  (hE : IsFrame p E (RingHom.id O))
include hv hE

/- English proof (translation)
The claim follows from `(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f g l l' a hl hl').1 hf hg`.
-/
theorem isLie_add {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (hf : QL c.μ ⊤ f)
    (hg : QL c.μ ⊤ g) (hl : c.IsLie f l) (hl' : c.IsLie g l') (a : O) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f g l l' a hl hl').1 hf hg

/- English proof (translation)
The claim follows from `(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.1 hs`.
-/
theorem isLie_int {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (hs : ∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) : l = 0 :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.1 hs

/- English proof (translation)
The claim follows from `(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.2 h`.
-/
theorem isLie_log {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (h : cob1 (up E c.μ) f = 0) : l = 0 :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.2 h

/- English proof (translation)
Take `⟨l, hl, -⟩` from `GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE 0 (ql_zero c.isLaw.const)`. Rewrite `hl` using `[isLie_int hv c hE hl ⟨0, (map_zero _).symm⟩]`. Then use the resulting hypothesis.
-/
theorem isLie_zero : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE 0 (ql_zero c.isLaw.const)
  rwa [isLie_int hv c hE hl ⟨0, (map_zero _).symm⟩] at hl

/- English proof (translation)
Establish `h0` using `c.isLaw.const`. It suffices to establish `∀ s : Finset ι, QL c.μ ⊤ (∑ i ∈ s, algebraMap O E (b i) • e i) ∧ c.IsLie (∑ i ∈ s, algebraMap O E (b i) • e i) (∑ i ∈ s, b i • L i) from (this Finset.univ).2`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ⟨ql_zero (E := E) h0, isLie_zero hv c hE⟩`.

Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • L a)]`. Conclude with `⟨ql_add_smul h0 ih.1 (he a) (b a), isLie_add hv c hE ih.1 (he a) ih.2 (hL a) (b a)⟩`.
-/
theorem isLie_comb {ι : Type} [Fintype ι] {e : ι → MvPowerSeries (Fin d) E} {L : ι → G.dual.Lie}
    (he : ∀ i, QL c.μ ⊤ (e i)) (hL : ∀ i, c.IsLie (e i) (L i)) (b : ι → O) :
    c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  have h0 := c.isLaw.const
  suffices ∀ s : Finset ι, QL c.μ ⊤ (∑ i ∈ s, algebraMap O E (b i) • e i) ∧
      c.IsLie (∑ i ∈ s, algebraMap O E (b i) • e i) (∑ i ∈ s, b i • L i) from
    (this Finset.univ).2
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using ⟨ql_zero (E := E) h0, isLie_zero hv c hE⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • L a)]
    exact ⟨ql_add_smul h0 ih.1 (he a) (b a), isLie_add hv c hE ih.1 (he a) ih.2 (hL a) (b a)⟩

/- English proof (translation)
Establish `h0` using `c.isLaw.const`. Set `M : Submodule O G.dual.Lie` to `{ carrier := {l | ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l} add_mem' := by`. Introduce and unpack `l1 l2 ⟨f1, hf1, hl1⟩ ⟨f2, hf2, hl2⟩`. Use `⟨f1 + algebraMap O E 1 • f2, ql_add_smul h0 hf1 hf2 1, ?_⟩` and prove the remaining obligations. Use `isLie_add hv c hE hf1 hf2 hl1 hl2 1` as an intermediate fact.

Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Use the proof step `zero_mem' := ⟨0, ql_zero (E := E) h0, isLie_zero hv c hE⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a l ⟨f, hf, hl⟩`. Use `⟨0 + algebraMap O E a • f, ql_add_smul h0 (ql_zero (E := E) h0) hf a, ?_⟩` and prove the remaining obligations.

Use `isLie_add hv c hE (ql_zero (E := E) h0) hf (isLie_zero hv c hE) hl a` as an intermediate fact. Simplify `this }` using `only [zero_add]`. Establish `hom` using `GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual`. Use `haveI := hom.1`. Use `haveI := hom.2`.

Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Establish `hp : Ideal.span {(p : O)} ≤ (⊥ : Ideal O).jacobson` using `((Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2 (Fact.out : ¬IsUnit (p : O)))).trans (IsLocalRing.maximalIdeal_le_jacobson _)`. Establish `htop : (⊤ : Submodule O G.dual.Lie) ≤ M`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hp fun x _ => ?_` and prove the remaining obligations. Take `⟨f, l', l'', hf, hl', rfl⟩` from `GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul p C v O hv G d c E hE x`.

Conclude with `Submodule.add_mem_sup ⟨f, hf, hl'⟩ (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)`. Conclude with `htop Submodule.mem_top`.
-/
theorem exists_isLie (l : G.dual.Lie) : ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l := by
  have h0 := c.isLaw.const
  let M : Submodule O G.dual.Lie :=
    { carrier := {l | ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l}
      add_mem' := by
        rintro l1 l2 ⟨f1, hf1, hl1⟩ ⟨f2, hf2, hl2⟩
        refine ⟨f1 + algebraMap O E 1 • f2, ql_add_smul h0 hf1 hf2 1, ?_⟩
        have := isLie_add hv c hE hf1 hf2 hl1 hl2 1
        rwa [one_smul] at this
      zero_mem' := ⟨0, ql_zero (E := E) h0, isLie_zero hv c hE⟩
      smul_mem' := by
        rintro a l ⟨f, hf, hl⟩
        refine ⟨0 + algebraMap O E a • f, ql_add_smul h0 (ql_zero (E := E) h0) hf a, ?_⟩
        have := isLie_add hv c hE (ql_zero (E := E) h0) hf (isLie_zero hv c hE) hl a
        simpa only [zero_add] using this }
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp : Ideal.span {(p : O)} ≤ (⊥ : Ideal O).jacobson :=
    ((Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (Fact.out : ¬IsUnit (p : O)))).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have htop : (⊤ : Submodule O G.dual.Lie) ≤ M := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hp fun x _ => ?_
    obtain ⟨f, l', l'', hf, hl', rfl⟩ := GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul p C v O hv G d c E hE x
    exact Submodule.add_mem_sup ⟨f, hf, hl'⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  exact htop Submodule.mem_top

end Chart

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hE`. Establish `h0` using `c.isLaw.const`. Establish `hom` using `GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual`. Use `haveI := hom.1`. Use `haveI := hom.2`.

Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing`. Set `lb` to `Module.finBasis O G.dual.Lie`. Use `choose F hF using fun j => exists_isLie hv c hE (lb j)`. Use `choose large₂ hLg using fun i : Fin d => GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hE d c.μ c.isLaw (Pi.single i 1)`.

Establish `hlin : ∀ i, lin (large₂ i) = Pi.single i 1` using `fun i => funext fun i' => by`. Rewrite using `[(hLg i).2.1 i', Pi.single_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Set `e : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → MvPowerSeries (Fin d) E` to `Sum.elim large₂ F`. Establish `hQ : ∀ i, QL c.μ ⊤ (e i)`.

Introduce and unpack `(i | j)`. Use `⟨(hLg i).1, fun i' => ⟨_, trivial, (hLg i).2.1 i'⟩, fun α => ⟨0, trivial, ?_⟩⟩ show coeff α (cob1 (up E c.μ) (large₂ i)) = _` and prove the remaining obligations. Rewrite using `[(hLg i).2.2, map_zero, map_zero]`. Conclude with `(hF j).1`. Establish `hcob : ∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0` using `fun i => (hLg i).2.2`.

Establish `hlin' : ∀ i, lin (e (Sum.inl i)) = Pi.single i 1` using `hlin`. Establish `hlie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j)` using `fun j => (hF j).2`. Set `L : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → G.dual.Lie` to `Sum.elim 0 lb`. Establish `hL : ∀ i, c.IsLie (e i) (L i)`. Introduce and unpack `(i | j)`.

Take `⟨l, hl, -⟩` from `GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE _ (hQ (Sum.inl i))`. Rewrite `hl` using `[isLie_log hv c hE hl (hcob i)]`. Conclude with `hl`. Conclude with `hlie j`. Establish `huniq : ∀ b : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → O, In (⊤ : Ideal O) (comb b e) → b = 0`.

Introduce `b hb`. Take `⟨s, hs⟩` from `in_top_map hb`. Establish `hl0 : ∑ i, b i • L i = 0` using `isLie_int hv c hE (isLie_comb hv c hE hQ hL b) ⟨s, hs⟩`. Establish `hr : ∀ j, b (Sum.inr j) = 0`. Establish `: ∑ j, b (Sum.inr j) • lb j = 0` using `by simpa [Fintype.sum_sum_type, L] using hl0`.

Conclude with `Fintype.linearIndependent_iff.1 lb.linearIndependent _ this`. Establish `hc : cob1 (up E c.μ) (map (algebraMap O E) s) = 0`. Rewrite using `[← hs, ← cobL_apply c.μ h0]`. Simplify using `[comb, map_sum, map_smul, Fintype.sum_sum_type, cobL_apply, hcob, hr]`. Establish `hs0` using `GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero p C v O hv G d c E hE s hc`.

Establish `hc0 : comb b e = 0` using `by rw [hs, hs0, map_zero]`. Establish `hl : ∀ i, b (Sum.inl i) = 0` using `fun i => by`. Establish `h1` using `congrArg (coeff (Finsupp.single i 1)) hc0`. Establish `hco : ∀ i', coeff (Finsupp.single i 1) (e (Sum.inl i')) = (Pi.single i' (1 : E) : Fin d → E) i` using `fun i' => congrFun (hlin' i') i`. Simplify using `[comb, map_sum, Fintype.sum_sum_type, hr, hco, Pi.single_apply] at h1`.

Conclude with `hE.inj (by rw [map_zero]; simpa [Algebra.smul_def] using h1)`. Use function extensionality and compare the values at `x`. Consider the cases of `x with`. Consider the case `inl i => exact hl i`. Consider the case `inr j => exact hr j`.

Use `⟨Module.finrank O G.dual.Lie, e, lb, ⟨hQ, fun f hf => ?_⟩, fun i => ⟨fun α => ⟨0, (RingHom.mem_ker).2 (map_zero _), by rw [hcob i, map_zero, map_zero]⟩, hlin' i⟩, hcob, hlie⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic p O E hE d c.μ c.isLaw _ e hQ (GlobalTheory.T.quasiLogarithm_division_step_decomposition p C v O hv G d c E hE _ e lb hQ hcob hlin' hlie) f hf`. Use `⟨b, hb, fun b' hb' => ?_⟩` and prove the remaining obligations. Establish `h1 : In (⊤ : Ideal O) (comb (b' - b) e)`. Rewrite using `[comb_sub]`.

Use `in_top_sub hb hb'` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Conclude with `sub_eq_zero.1 (huniq _ h1)`.
-/
theorem adapted_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hE
  have h0 := c.isLaw.const
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  let lb := Module.finBasis O G.dual.Lie
  choose F hF using fun j => exists_isLie hv c hE (lb j)
  choose large₂ hLg using fun i : Fin d => GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hE d c.μ c.isLaw (Pi.single i 1)
  have hlin : ∀ i, lin (large₂ i) = Pi.single i 1 := fun i => funext fun i' => by
    rw [(hLg i).2.1 i', Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  let e : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → MvPowerSeries (Fin d) E := Sum.elim large₂ F
  have hQ : ∀ i, QL c.μ ⊤ (e i) := by
    rintro (i | j)
    · refine ⟨(hLg i).1, fun i' => ⟨_, trivial, (hLg i).2.1 i'⟩, fun α => ⟨0, trivial, ?_⟩⟩
      show coeff α (cob1 (up E c.μ) (large₂ i)) = _
      rw [(hLg i).2.2, map_zero, map_zero]
    · exact (hF j).1
  have hcob : ∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0 := fun i => (hLg i).2.2
  have hlin' : ∀ i, lin (e (Sum.inl i)) = Pi.single i 1 := hlin
  have hlie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := fun j => (hF j).2
  let L : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → G.dual.Lie := Sum.elim 0 lb
  have hL : ∀ i, c.IsLie (e i) (L i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE _ (hQ (Sum.inl i))
      rw [isLie_log hv c hE hl (hcob i)] at hl
      exact hl
    · exact hlie j
  have huniq : ∀ b : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → O, In (⊤ : Ideal O) (comb b e) → b = 0 := by
    intro b hb
    obtain ⟨s, hs⟩ := in_top_map hb
    have hl0 : ∑ i, b i • L i = 0 := isLie_int hv c hE (isLie_comb hv c hE hQ hL b) ⟨s, hs⟩
    have hr : ∀ j, b (Sum.inr j) = 0 := by
      have : ∑ j, b (Sum.inr j) • lb j = 0 := by simpa [Fintype.sum_sum_type, L] using hl0
      exact Fintype.linearIndependent_iff.1 lb.linearIndependent _ this
    have hc : cob1 (up E c.μ) (map (algebraMap O E) s) = 0 := by
      rw [← hs, ← cobL_apply c.μ h0]
      simp [comb, map_sum, map_smul, Fintype.sum_sum_type, cobL_apply, hcob, hr]
    have hs0 := GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero p C v O hv G d c E hE s hc
    have hc0 : comb b e = 0 := by rw [hs, hs0, map_zero]
    have hl : ∀ i, b (Sum.inl i) = 0 := fun i => by
      have h1 := congrArg (coeff (Finsupp.single i 1)) hc0
      have hco : ∀ i', coeff (Finsupp.single i 1) (e (Sum.inl i')) = (Pi.single i' (1 : E) : Fin d → E) i :=
        fun i' => congrFun (hlin' i') i
      simp [comb, map_sum, Fintype.sum_sum_type, hr, hco, Pi.single_apply] at h1
      exact hE.inj (by rw [map_zero]; simpa [Algebra.smul_def] using h1)
    funext x
    cases x with
    | inl i => exact hl i
    | inr j => exact hr j
  refine ⟨Module.finrank O G.dual.Lie, e, lb, ⟨hQ, fun f hf => ?_⟩,
    fun i => ⟨fun α => ⟨0, (RingHom.mem_ker).2 (map_zero _), by rw [hcob i, map_zero, map_zero]⟩,
      hlin' i⟩, hcob, hlie⟩
  obtain ⟨b, hb⟩ := GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic p O E hE d c.μ c.isLaw _ e hQ
    (GlobalTheory.T.quasiLogarithm_division_step_decomposition p C v O hv G d c E hE _ e lb hQ hcob hlin' hlie) f hf
  refine ⟨b, hb, fun b' hb' => ?_⟩
  have h1 : In (⊤ : Ideal O) (comb (b' - b) e) := by
    rw [comb_sub]
    have := in_top_sub hb hb'
    rwa [sub_sub_sub_cancel_left] at this
  exact sub_eq_zero.1 (huniq _ h1)

end GlobalTheory.QLogBasis
