import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SchurLin

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.comp_continuous (continuous_add_right Z), hf.2.comp_homeomorph (Homeomorph.addRight Z)⟩`.
-/
theorem sb_translate {f : V → ℂ} (hf : f ∈ SB V) (Z : V) : (fun Y => f (Y + Z)) ∈ SB V :=
  ⟨hf.1.comp_continuous (continuous_add_right Z), hf.2.comp_homeomorph (Homeomorph.addRight Z)⟩

/- English proof (translation)
Establish `hcl : IsClosed (U : Set V)` using `AddSubgroup.isClosed_of_isOpen U ho`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ (U : Set V)`.

Use `filter_upwards [ho.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use `filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Conclude with `HasCompactSupport.intro' hc hcl (fun x hx => Set.indicator_of_notMem hx _)`.
-/
theorem sb_indicator (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V)) :
    (U : Set V).indicator (1 : V → ℂ) ∈ SB V := by
  have hcl : IsClosed (U : Set V) := AddSubgroup.isClosed_of_isOpen U ho
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (U : Set V)
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  exact HasCompactSupport.intro' hc hcl (fun x hx => Set.indicator_of_notMem hx _)

/- English proof (translation)
Establish `h1 : ∀ᶠ w in 𝓝 (0 : V), ∀ Y ∈ tsupport f, f (Y + w) = f Y`. Apply `hf.2.isCompact.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `Y _`. Establish `hc : Tendsto (fun z : V × V => z.2 + z.1) (𝓝 ((0 : V), Y)) (𝓝 Y)`. Establish `hcont : Continuous (fun z : V × V => z.2 + z.1)` using `by fun_prop`.

Use `hcont.tendsto ((0 : V), Y) using 2` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Establish `hc2 : Tendsto (fun z : V × V => z.2) (𝓝 ((0 : V), Y)) (𝓝 Y)` using `continuous_snd.tendsto _`. Use `filter_upwards [hc.eventually (hf.1.eventually_eq Y), hc2.eventually (hf.1.eventually_eq Y)] with z h1 h2`. Rewrite using `[h1, h2]`.

Establish `h2 : ∀ᶠ w in 𝓝 (0 : V), ∀ Y ∈ tsupport f, f (Y + -w) = f Y`. Establish `: Tendsto (fun w : V => -w) (𝓝 0) (𝓝 0)`. Simplify using `using (continuous_neg.tendsto (0 : V))`. Conclude with `this.eventually h1`. Use `filter_upwards [h1, h2] with w hw1 hw2`.

Introduce `Y`. Distinguish the cases in `hY : Y ∈ tsupport f`. Conclude with `hw1 Y hY`. Distinguish the cases in `hY' : Y + w ∈ tsupport f`. Use `hw2 _ hY'` as an intermediate fact.

Simplify using `only [add_neg_cancel_right] at this`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']`.
-/
theorem sb_eventually_invariant {f : V → ℂ} (hf : f ∈ SB V) :
    ∀ᶠ w in 𝓝 (0 : V), ∀ Y, f (Y + w) = f Y := by
  have h1 : ∀ᶠ w in 𝓝 (0 : V), ∀ Y ∈ tsupport f, f (Y + w) = f Y := by
    apply hf.2.isCompact.eventually_forall_of_forall_eventually
    intro Y _
    have hc : Tendsto (fun z : V × V => z.2 + z.1) (𝓝 ((0 : V), Y)) (𝓝 Y) := by
      have hcont : Continuous (fun z : V × V => z.2 + z.1) := by fun_prop
      convert hcont.tendsto ((0 : V), Y) using 2
      simp
    have hc2 : Tendsto (fun z : V × V => z.2) (𝓝 ((0 : V), Y)) (𝓝 Y) :=
      continuous_snd.tendsto _
    filter_upwards [hc.eventually (hf.1.eventually_eq Y), hc2.eventually (hf.1.eventually_eq Y)]
      with z h1 h2
    rw [h1, h2]
  have h2 : ∀ᶠ w in 𝓝 (0 : V), ∀ Y ∈ tsupport f, f (Y + -w) = f Y := by
    have : Tendsto (fun w : V => -w) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : V))
    exact this.eventually h1
  filter_upwards [h1, h2] with w hw1 hw2
  intro Y
  by_cases hY : Y ∈ tsupport f
  · exact hw1 Y hY
  by_cases hY' : Y + w ∈ tsupport f
  · have := hw2 _ hY'
    simp only [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']

variable (A : (V → ℂ) → V → ℂ)

/- English proof (translation)
Use `set e : V → ℂ := (U : Set V).indicator 1 with he_def`. Establish `he : e ∈ SB V` using `sb_indicator U ho hc`. Use `haveI := QuotientAddGroup.discreteTopology ho`. Establish `hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite` using `(hf.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `set S := hfin.toFinset`.

Set `g : V ⧸ U → V → ℂ` to `fun q Y => e (Y + -q.out)`. Establish `hg : ∀ q, g q ∈ SB V` using `fun q => sb_translate he _`. Establish `hAg : ∀ q, A (g q) = c • g q`. Introduce `q`. Use `show A (fun Y => e (Y + -q.out)) = _`.

Rewrite using `[htr _ _ he, hA]`. Both sides reduce to the same expression. Establish `hgq : ∀ q Y, g q Y = if (QuotientAddGroup.mk Y : V ⧸ U) = q then 1 else 0`. Introduce `q Y`. Establish `: (QuotientAddGroup.mk Y : V ⧸ U) = q ↔ Y + -q.out ∈ U` using `by conv_lhs => rw [← Quotient.out_eq' q]`.

Rewrite using `[eq_comm]`. Use `show (QuotientAddGroup.mk q.out : V ⧸ U) = QuotientAddGroup.mk Y ↔ _`. Rewrite using `[QuotientAddGroup.eq, show Y + -q.out = -q.out + Y by abel]`. Simplify using `only [g, e, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, this]`. Establish `hdec : f = ∑ q ∈ S, f q.out • g q`.

Use function extensionality and compare the values at `Y`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]`. Use `split_ifs with hS`. Establish `h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) : V ⧸ U) = QuotientAddGroup.mk Y` using `Quotient.out_eq' _`. Rewrite `h1` using `[QuotientAddGroup.eq]`.

Use `hinv (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) _ h1` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`. Conclude with `this`. Establish `: Y ∉ tsupport f` using `fun h => hS (hfin.mem_toFinset.2 ⟨Y, h, rfl⟩)`. Conclude with `image_eq_zero_of_notMem_tsupport this`.

Establish `hzero : A 0 = 0`. Use `hsmul 0 e he` as an intermediate fact. Simplify using `using this`. Establish `hsum : ∀ T : Finset (V ⧸ U), A (∑ q ∈ T, f q.out • g q) = ∑ q ∈ T, f q.out • A (g q)`. Introduce `T`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using hzero`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hadd _ ((SB V).smul_mem _ (hg a)) _ ((SB V).sum_mem fun q _ => (SB V).smul_mem _ (hg q)), hsmul _ _ (hg a), ih]`. Rewrite using `[hdec, hsum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hAg, smul_comm]`.
-/
theorem eq_smul_of_invariant
    (hadd : ∀ f ∈ SB V, ∀ f' ∈ SB V, A (f + f') = A f + A f')
    (hsmul : ∀ (c : ℂ), ∀ f ∈ SB V, A (c • f) = c • A f)
    (htr : ∀ Z : V, ∀ f ∈ SB V, A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z))
    (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V)) (c : ℂ)
    (hA : A ((U : Set V).indicator 1) = c • (U : Set V).indicator 1)
    {f : V → ℂ} (hf : f ∈ SB V) (hinv : ∀ Y, ∀ u ∈ U, f (Y + u) = f Y) : A f = c • f := by
  classical
  set e : V → ℂ := (U : Set V).indicator 1 with he_def
  have he : e ∈ SB V := sb_indicator U ho hc
  haveI := QuotientAddGroup.discreteTopology ho
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite :=
    (hf.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set S := hfin.toFinset
  let g : V ⧸ U → V → ℂ := fun q Y => e (Y + -q.out)
  have hg : ∀ q, g q ∈ SB V := fun q => sb_translate he _
  have hAg : ∀ q, A (g q) = c • g q := by
    intro q
    show A (fun Y => e (Y + -q.out)) = _
    rw [htr _ _ he, hA]
    rfl
  have hgq : ∀ q Y, g q Y = if (QuotientAddGroup.mk Y : V ⧸ U) = q then 1 else 0 := by
    intro q Y
    have : (QuotientAddGroup.mk Y : V ⧸ U) = q ↔ Y + -q.out ∈ U := by
      conv_lhs => rw [← Quotient.out_eq' q]
      rw [eq_comm]
      show (QuotientAddGroup.mk q.out : V ⧸ U) = QuotientAddGroup.mk Y ↔ _
      rw [QuotientAddGroup.eq, show Y + -q.out = -q.out + Y by abel]
    simp only [g, e, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, this]
  have hdec : f = ∑ q ∈ S, f q.out • g q := by
    funext Y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq]
    split_ifs with hS
    · have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) : V ⧸ U)
          = QuotientAddGroup.mk Y := Quotient.out_eq' _
      rw [QuotientAddGroup.eq] at h1
      have := hinv (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) _ h1
      rw [add_neg_cancel_left] at this
      exact this
    · have : Y ∉ tsupport f := fun h => hS (hfin.mem_toFinset.2 ⟨Y, h, rfl⟩)
      exact image_eq_zero_of_notMem_tsupport this
  have hzero : A 0 = 0 := by
    have := hsmul 0 e he
    simpa using this
  have hsum : ∀ T : Finset (V ⧸ U),
      A (∑ q ∈ T, f q.out • g q) = ∑ q ∈ T, f q.out • A (g q) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using hzero
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hadd _ ((SB V).smul_mem _ (hg a)) _ ((SB V).sum_mem fun q _ => (SB V).smul_mem _ (hg q)),
        hsmul _ _ (hg a), ih]
  rw [hdec, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hAg, smul_comm]

/- English proof (translation)
Use `set e : V → ℂ := (U : Set V).indicator 1 with he_def`. Establish `he : e ∈ SB V` using `sb_indicator U ho hc`. Establish `hinv : ∀ u ∈ U, ∀ Y, A e (Y + u) = A e Y`. Introduce `u hu Y`. Establish `: (fun Y => e (Y + u)) = e`.

Use function extensionality and compare the values at `Y`. Simplify using `[e, Set.indicator_apply, U.add_mem_cancel_right hu]`. Establish `h` using `htr u e he`. Rewrite `h` using `[this]`. Conclude with `(congrFun h Y).symm`.

Establish `hzero : ∀ Y ∉ U, A e Y = 0`. Introduce `Y hY`. Take `⟨Z, hZY, hZU⟩` from `hsep Y hY`. Establish `: (fun Y => χ Z Y * e Y) = e`. Use function extensionality and compare the values at `Y`.

Distinguish the cases in `h : Y ∈ U`. Simplify using `[e, h, hZU Y h]`. Simplify using `[e, h]`. Establish `h` using `hmul Z e he`. Rewrite `h` using `[this]`.

Establish `h2` using `congrFun h Y`. Establish `h3 : (χ Z Y - 1) * A e Y = 0` using `by linear_combination (-1 : ℂ) * h2`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) hZY`. Conclude with `h`.

Use function extensionality and compare the values at `Y`. Distinguish the cases in `hY : Y ∈ U`. Use `hinv Y hY 0` as an intermediate fact. Simplify using `only [zero_add] at this`. Simplify using `[e, hY, this]`.

Simplify using `[e, hY, hzero Y hY]`.
-/
theorem indicator_eigen
    (htr : ∀ Z : V, ∀ f ∈ SB V, A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z))
    (χ : V → V → ℂ)
    (hmul : ∀ Z : V, ∀ f ∈ SB V, A (fun Y => χ Z Y * f Y) = fun Y => χ Z Y * A f Y)
    (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V))
    (hsep : ∀ Y ∉ U, ∃ Z, χ Z Y ≠ 1 ∧ ∀ u ∈ U, χ Z u = 1) :
    A ((U : Set V).indicator 1) = A ((U : Set V).indicator 1) 0 • (U : Set V).indicator 1 := by
  classical
  set e : V → ℂ := (U : Set V).indicator 1 with he_def
  have he : e ∈ SB V := sb_indicator U ho hc
  have hinv : ∀ u ∈ U, ∀ Y, A e (Y + u) = A e Y := by
    intro u hu Y
    have : (fun Y => e (Y + u)) = e := by
      funext Y
      simp [e, Set.indicator_apply, U.add_mem_cancel_right hu]
    have h := htr u e he
    rw [this] at h
    exact (congrFun h Y).symm
  have hzero : ∀ Y ∉ U, A e Y = 0 := by
    intro Y hY
    obtain ⟨Z, hZY, hZU⟩ := hsep Y hY
    have : (fun Y => χ Z Y * e Y) = e := by
      funext Y
      by_cases h : Y ∈ U
      · simp [e, h, hZU Y h]
      · simp [e, h]
    have h := hmul Z e he
    rw [this] at h
    have h2 := congrFun h Y
    have h3 : (χ Z Y - 1) * A e Y = 0 := by linear_combination (-1 : ℂ) * h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hZY
    · exact h
  funext Y
  by_cases hY : Y ∈ U
  · have := hinv Y hY 0
    simp only [zero_add] at this
    simp [e, hY, this]
  · simp [e, hY, hzero Y hY]

end General

end GlobalTheory.SchurLin

namespace GlobalTheory.SchurLin

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def dualBall (ψ : AddChar K ℂ) (t : K) : AddSubgroup K where
  carrier := {y | ∀ o ∈ (ValuativeRel.valuation K).integer, ψ (o * (t * y)) = 1}
  zero_mem' := by
    intro o _
    simp
  add_mem' := by
    intro a b ha hb o ho
    simp only [Set.mem_setOf_eq] at *
    rw [mul_add, mul_add, AddChar.map_add_eq_mul, ha o ho, hb o ho, one_mul]
  neg_mem' := by
    intro a ha o ho
    have h : ψ (o * (t * a)) = 1 := ha o ho
    have h2 : ψ (o * (t * -a)) * ψ (o * (t * a)) = 1 := by
      rw [← AddChar.map_add_eq_mul, show o * (t * -a) + o * (t * a) = 0 by ring,
        AddChar.map_zero_eq_one]
    rw [h, mul_one] at h2
    exact h2

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dualBall {ψ : AddChar K ℂ} {t y : K} :
    y ∈ dualBall ψ t ↔ ∀ o ∈ (ValuativeRel.valuation K).integer, ψ (o * (t * y)) = 1 := Iff.rfl

/- English proof (translation)
Establish `h` using `GlobalTheory.Published.SvN.eventually_psi hψc`. Establish `ht : Tendsto (fun y : K => t * y) (𝓝 0) (𝓝 0)`. Use `(continuous_mul_left t).tendsto (0 : K)` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis. Use `filter_upwards [ht.eventually h] with y hy using hy`.
-/
theorem dualBall_mem_nhds {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) :
    (dualBall ψ t : Set K) ∈ 𝓝 0 := by
  have h := GlobalTheory.Published.SvN.eventually_psi hψc
  have ht : Tendsto (fun y : K => t * y) (𝓝 0) (𝓝 0) := by
    have := (continuous_mul_left t).tendsto (0 : K)
    rwa [mul_zero] at this
  filter_upwards [ht.eventually h] with y hy using hy

/- English proof (translation)
Introduce `y hy`. Assume the negation of the conclusion as `hlt`. Simplify using `only [Set.mem_setOf_eq, not_le] at hlt`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hlt`. Establish `ho : x₀ / t / y ∈ (ValuativeRel.valuation K).integer`. Rewrite using `[Valuation.mem_integer_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ hlt.le zero_le'`. Use `hy _ ho` as an intermediate fact.

Rewrite `this` using `[show x₀ / t / y * (t * y) = x₀ by field_simp]`. Conclude with `hx₀ this`.
-/
theorem dualBall_subset {ψ : AddChar K ℂ} {x₀ : K} (hx₀ : ψ x₀ ≠ 1) {t : K} (ht : t ≠ 0) :
    (dualBall ψ t : Set K) ⊆ {y | ValuativeRel.valuation K y ≤ ValuativeRel.valuation K (x₀ / t)} := by
  intro y hy
  by_contra hlt
  simp only [Set.mem_setOf_eq, not_le] at hlt
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hlt
  have ho : x₀ / t / y ∈ (ValuativeRel.valuation K).integer := by
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ hlt.le zero_le'
  have := hy _ ho
  rw [show x₀ / t / y * (t * y) = x₀ by field_simp] at this
  exact hx₀ this

variable (n m : ℕ)

def latt (ψ : AddChar K ℂ) (t : K) : AddSubgroup (Matrix (Fin n) (Fin m) K) where
  carrier := {Y | ∀ i j, Y i j ∈ dualBall ψ t}
  zero_mem' := fun _ _ => (dualBall ψ t).zero_mem
  add_mem' := fun ha hb i j => (dualBall ψ t).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (dualBall ψ t).neg_mem (ha i j)

variable {n m}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latt {ψ : AddChar K ℂ} {t : K} {Y : Matrix (Fin n) (Fin m) K} :
    Y ∈ latt n m ψ t ↔ ∀ i j, Y i j ∈ dualBall ψ t := Iff.rfl

/- English proof (translation)
Establish `h : ∀ i j, ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin m) K), Y i j ∈ dualBall ψ t`. Introduce `i j`. Establish `hc : Continuous (fun Y : Matrix (Fin n) (Fin m) K => Y i j)` using `by fun_prop`. Use `hc.tendsto 0` as an intermediate fact. Rewrite `this` using `[Matrix.zero_apply]`.

Conclude with `this.eventually (dualBall_mem_nhds hψc t)`. Use `filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h i j] with Y hY using hY`.
-/
theorem latt_mem_nhds {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) :
    (latt n m ψ t : Set (Matrix (Fin n) (Fin m) K)) ∈ 𝓝 0 := by
  have h : ∀ i j, ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin m) K), Y i j ∈ dualBall ψ t := by
    intro i j
    have hc : Continuous (fun Y : Matrix (Fin n) (Fin m) K => Y i j) := by fun_prop
    have := hc.tendsto 0
    rw [Matrix.zero_apply] at this
    exact this.eventually (dualBall_mem_nhds hψc t)
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h i j] with Y hY
    using hY

/- English proof (translation)
The claim follows from `AddSubgroup.isOpen_of_mem_nhds _ (latt_mem_nhds hψc t)`.
-/
theorem latt_isOpen {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) :
    IsOpen (latt n m ψ t : Set (Matrix (Fin n) (Fin m) K)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (latt_mem_nhds hψc t)

/- English proof (translation)
Establish `hEq : {Y : Matrix (Fin n) (Fin m) K | ∀ i j, ValuativeRel.valuation K (Y i j) ≤ γ} = ((Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin m => {x : K | ValuativeRel.valuation K x ≤ γ}) : Set (Matrix (Fin n) (Fin m) K))`. Use extensionality with `Y`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩`. Rewrite using `[hEq]`. Conclude with `isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin m => IsNonarchimedeanLocalField.isCompact_closedBall K γ))`.
-/
theorem isCompact_ball (γ : ValuativeRel.ValueGroupWithZero K) :
    IsCompact {Y : Matrix (Fin n) (Fin m) K | ∀ i j, ValuativeRel.valuation K (Y i j) ≤ γ} := by
  have hEq : {Y : Matrix (Fin n) (Fin m) K | ∀ i j, ValuativeRel.valuation K (Y i j) ≤ γ} =
      ((Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin m =>
        {x : K | ValuativeRel.valuation K x ≤ γ}) : Set (Matrix (Fin n) (Fin m) K)) := by
    ext Y
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [hEq]
  exact isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi
    (fun _ : Fin m => IsNonarchimedeanLocalField.isCompact_closedBall K γ))

/- English proof (translation)
Use `(isCompact_ball (ValuativeRel.valuation K (x₀ / t))).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (latt_isOpen hψc t)) ?_` and prove the remaining obligations. Introduce `Y hY i j`. Conclude with `dualBall_subset hx₀ ht (hY i j)`.
-/
theorem latt_isCompact {ψ : AddChar K ℂ} (hψc : Continuous ψ) {x₀ : K} (hx₀ : ψ x₀ ≠ 1) {t : K}
    (ht : t ≠ 0) : IsCompact (latt n m ψ t : Set (Matrix (Fin n) (Fin m) K)) := by
  refine (isCompact_ball (ValuativeRel.valuation K (x₀ / t))).of_isClosed_subset
    (AddSubgroup.isClosed_of_isOpen _ (latt_isOpen hψc t)) ?_
  intro Y hY i j
  exact dualBall_subset hx₀ ht (hY i j)

/- English proof (translation)
Use `set B := {Y : Matrix (Fin n) (Fin m) K | ∀ i j, ValuativeRel.valuation K (Y i j) ≤ 1}`. Establish `hB : IsCompact B` using `isCompact_ball 1`. Establish `h : ∀ᶠ s in 𝓝 (0 : K), ∀ Y ∈ B, s • Y ∈ W`. Apply `hB.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `Y _`.

Establish `hc : Continuous (fun z : K × Matrix (Fin n) (Fin m) K => z.1 • z.2)` using `continuous_fst.smul continuous_snd`. Establish `h2 : Tendsto (fun z : K × Matrix (Fin n) (Fin m) K => z.1 • z.2) (𝓝 ((0 : K), Y)) (𝓝 0)`. Use `hc.tendsto ((0 : K), Y) using 2` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Conclude with `h2.eventually hW`.

Take `⟨γ, hγ, hsub⟩` from `(IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.1 h`. Take `⟨r, hr0, hr1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)`. Take `⟨a, ha⟩` from `ValuativeRel.valuation_surjective γ`. Establish `hx00 : x₀ ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx₀ (AddChar.map_zero_eq_one ψ)`. Use `set s := r * a with hs`. Establish `hvs : ValuativeRel.valuation K s < γ`. Rewrite using `[hs, map_mul, ha]`. Conclude with `mul_lt_of_lt_one_left (zero_lt_iff.2 hγ) hr1`.

Establish `hs0 : s ≠ 0`. Introduce `h0`. Rewrite `hvs` using `[h0, map_zero]`. Establish `: ValuativeRel.valuation K r * γ = 0`. Rewrite using `[← ha, ← map_mul, ← hs, h0, map_zero]`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `hr0 (by simpa using h)`. Conclude with `hγ h`. Use `⟨x₀ / s, div_ne_zero hx00 hs0, ?_⟩` and prove the remaining obligations. Introduce `Y hY`.

Establish `hxs : x₀ / (x₀ / s) = s` using `by field_simp`. Establish `hYs : ∀ i j, ValuativeRel.valuation K (Y i j) ≤ ValuativeRel.valuation K s`. Introduce `i j`. Use `dualBall_subset hx₀ (div_ne_zero hx00 hs0) (hY i j)` as an intermediate fact. Rewrite `this` using `[Set.mem_setOf_eq, hxs]`. Then use the resulting hypothesis.

Establish `hmem : s⁻¹ • Y ∈ B`. Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]`. Establish `hv0 : ValuativeRel.valuation K s ≠ 0` using `by simpa using hs0`. Rewrite using `[inv_mul_le_iff₀ (zero_lt_iff.2 hv0), mul_one]`.

Conclude with `hYs i j`. Use `hsub hvs (s⁻¹ • Y) hmem` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_inv_cancel₀ hs0, one_smul]`. Then use the resulting hypothesis.
-/
theorem latt_small {ψ : AddChar K ℂ} {x₀ : K} (hx₀ : ψ x₀ ≠ 1)
    {W : Set (Matrix (Fin n) (Fin m) K)} (hW : W ∈ 𝓝 0) :
    ∃ t : K, t ≠ 0 ∧ (latt n m ψ t : Set (Matrix (Fin n) (Fin m) K)) ⊆ W := by
  set B := {Y : Matrix (Fin n) (Fin m) K | ∀ i j, ValuativeRel.valuation K (Y i j) ≤ 1}
  have hB : IsCompact B := isCompact_ball 1
  have h : ∀ᶠ s in 𝓝 (0 : K), ∀ Y ∈ B, s • Y ∈ W := by
    apply hB.eventually_forall_of_forall_eventually
    intro Y _
    have hc : Continuous (fun z : K × Matrix (Fin n) (Fin m) K => z.1 • z.2) :=
      continuous_fst.smul continuous_snd
    have h2 : Tendsto (fun z : K × Matrix (Fin n) (Fin m) K => z.1 • z.2) (𝓝 ((0 : K), Y)) (𝓝 0) := by
      convert hc.tendsto ((0 : K), Y) using 2
      simp
    exact h2.eventually hW
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.1 h
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
  have hx00 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  set s := r * a with hs
  have hvs : ValuativeRel.valuation K s < γ := by
    rw [hs, map_mul, ha]
    exact mul_lt_of_lt_one_left (zero_lt_iff.2 hγ) hr1
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvs
    have : ValuativeRel.valuation K r * γ = 0 := by
      rw [← ha, ← map_mul, ← hs, h0, map_zero]
    rcases mul_eq_zero.1 this with h | h
    · exact hr0 (by simpa using h)
    · exact hγ h
  refine ⟨x₀ / s, div_ne_zero hx00 hs0, ?_⟩
  intro Y hY
  have hxs : x₀ / (x₀ / s) = s := by field_simp
  have hYs : ∀ i j, ValuativeRel.valuation K (Y i j) ≤ ValuativeRel.valuation K s := by
    intro i j
    have := dualBall_subset hx₀ (div_ne_zero hx00 hs0) (hY i j)
    rwa [Set.mem_setOf_eq, hxs] at this
  have hmem : s⁻¹ • Y ∈ B := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hv0 : ValuativeRel.valuation K s ≠ 0 := by simpa using hs0
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv0), mul_one]
    exact hYs i j
  have := hsub hvs (s⁻¹ • Y) hmem
  rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul] at this

/- English proof (translation)
Rewrite `hY` using `[mem_latt]`. Use `push_neg at hY`. Take `⟨i, j, hij⟩` from `hY`. Rewrite `hij` using `[mem_dualBall]`. Use `push_neg at hij`.

Take `⟨o, ho, hne⟩` from `hij`. Set `Z : Matrix (Fin n) (Fin m) K` to `fun i' j' => if i' = i then (if j' = j then o * t else 0) else 0`. Establish `hsum : ∀ X : Matrix (Fin n) (Fin m) K, ∑ i', ∑ j', X i' j' * Z i' j' = o * (t * X i j)`. Introduce `X`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by simp [Z, hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [Z, hb]) (by simp)]`.

Simplify using `only [Z, if_true]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Z, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`. Conclude with `hne`.

Introduce `u hu`. Rewrite using `[hsum]`. Conclude with `(mem_latt.1 hu i j) o ho`.
-/
theorem latt_sep {ψ : AddChar K ℂ} (t : K) (Y : Matrix (Fin n) (Fin m) K) (hY : Y ∉ latt n m ψ t) :
    ∃ Z : Matrix (Fin n) (Fin m) K, ψ (∑ i, ∑ j, Y i j * Z i j) ≠ 1 ∧
      ∀ u ∈ latt n m ψ t, ψ (∑ i, ∑ j, u i j * Z i j) = 1 := by
  classical
  rw [mem_latt] at hY
  push_neg at hY
  obtain ⟨i, j, hij⟩ := hY
  rw [mem_dualBall] at hij
  push_neg at hij
  obtain ⟨o, ho, hne⟩ := hij
  let Z : Matrix (Fin n) (Fin m) K := fun i' j' => if i' = i then (if j' = j then o * t else 0) else 0
  have hsum : ∀ X : Matrix (Fin n) (Fin m) K, ∑ i', ∑ j', X i' j' * Z i' j' = o * (t * X i j) := by
    intro X
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Z, hb]) (by simp),
      Finset.sum_eq_single j (fun b _ hb => by simp [Z, hb]) (by simp)]
    simp only [Z, if_true]
    ring
  refine ⟨Z, ?_, ?_⟩
  · rw [hsum]
    exact hne
  · intro u hu
    rw [hsum]
    exact (mem_latt.1 hu i j) o ho

end Local

/- English proof (translation)
Introduce `K _ _ _ _ ψ hψc hψ n m A hadd hsmul htr hmul`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hψ (by ext x; rw [h x, AddChar.one_apply])`.

Establish `hx00 : x₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx₀ (AddChar.map_zero_eq_one ψ)`. Set `e : K → Matrix (Fin n) (Fin m) K → ℂ` to `fun t => (latt n m ψ t : Set _).indicator 1`. Establish `eig : ∀ t : K, t ≠ 0 → A (e t) = A (e t) 0 • e t` using `fun t ht => indicator_eigen A htr (fun Z Y => ψ (∑ i, ∑ j, Y i j * Z i j)) hmul (latt n m ψ t) (latt_isOpen hψc t) (latt_isCompact hψc hx₀ ht) (latt_sep t)`.

Use `⟨A (e 1) 0, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hW : {w | ∀ Y, f (Y + w) = f Y} ∩ (latt n m ψ 1 : Set (Matrix (Fin n) (Fin m) K)) ∈ 𝓝 0` using `Filter.inter_mem (sb_eventually_invariant hf) (latt_mem_nhds hψc 1)`. Take `⟨t, ht, hsub⟩` from `latt_small hx₀ hW`. Establish `h1 : A f = A (e t) 0 • f` using `eq_smul_of_invariant A hadd hsmul htr (latt n m ψ t) (latt_isOpen hψc t) (latt_isCompact hψc hx₀ ht) _ (eig t ht) hf (fun Y u hu => (hsub hu).1 Y)`. Establish `h2 : A (e 1) = A (e t) 0 • e 1` using `eq_smul_of_invariant A hadd hsmul htr (latt n m ψ t) (latt_isOpen hψc t) (latt_isCompact hψc hx₀ ht) _ (eig t ht) (sb_indicator _ (latt_isOpen hψc 1) (latt_isCompact hψc hx₀ one_ne_zero)) (fun Y u hu => by`.

Simplify using `only [e, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, (latt n m ψ 1).add_mem_cancel_right (hsub hu).2])`. Establish `h3 : A (e 1) 0 = A (e t) 0`. Rewrite using `[h2]`. Simplify using `[e, (latt n m ψ 1).zero_mem]`. Rewrite using `[h1, h3]`.
-/
theorem schur_linear_model :
    ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : AddChar K ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ (n m : ℕ) (A : (Matrix (Fin n) (Fin m) K → ℂ) → Matrix (Fin n) (Fin m) K → ℂ),
    (∀ f ∈ SB (Matrix (Fin n) (Fin m) K), ∀ f' ∈ SB (Matrix (Fin n) (Fin m) K), A (f + f') = A f + A f') →
    (∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A (c • f) = c • A f) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z)) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * f Y) = fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * A f Y) →
    ∃ c : ℂ, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A f = c • f := by
  intro K _ _ _ _ ψ hψc hψ n m A hadd hsmul htr hmul
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (by ext x; rw [h x, AddChar.one_apply])
  have hx00 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  let e : K → Matrix (Fin n) (Fin m) K → ℂ := fun t => (latt n m ψ t : Set _).indicator 1
  have eig : ∀ t : K, t ≠ 0 → A (e t) = A (e t) 0 • e t := fun t ht =>
    indicator_eigen A htr (fun Z Y => ψ (∑ i, ∑ j, Y i j * Z i j)) hmul (latt n m ψ t)
      (latt_isOpen hψc t) (latt_isCompact hψc hx₀ ht) (latt_sep t)
  refine ⟨A (e 1) 0, fun f hf => ?_⟩
  have hW : {w | ∀ Y, f (Y + w) = f Y} ∩ (latt n m ψ 1 : Set (Matrix (Fin n) (Fin m) K)) ∈ 𝓝 0 :=
    Filter.inter_mem (sb_eventually_invariant hf) (latt_mem_nhds hψc 1)
  obtain ⟨t, ht, hsub⟩ := latt_small hx₀ hW
  have h1 : A f = A (e t) 0 • f :=
    eq_smul_of_invariant A hadd hsmul htr (latt n m ψ t) (latt_isOpen hψc t)
      (latt_isCompact hψc hx₀ ht) _ (eig t ht) hf (fun Y u hu => (hsub hu).1 Y)
  have h2 : A (e 1) = A (e t) 0 • e 1 :=
    eq_smul_of_invariant A hadd hsmul htr (latt n m ψ t) (latt_isOpen hψc t)
      (latt_isCompact hψc hx₀ ht) _ (eig t ht)
      (sb_indicator _ (latt_isOpen hψc 1) (latt_isCompact hψc hx₀ one_ne_zero))
      (fun Y u hu => by
        simp only [e, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply,
          (latt n m ψ 1).add_mem_cancel_right (hsub hu).2])
  have h3 : A (e 1) 0 = A (e t) 0 := by
    rw [h2]
    simp [e, (latt n m ψ 1).zero_mem]
  rw [h1, h3]

end GlobalTheory.SchurLin
