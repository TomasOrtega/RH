import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrCyclic

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[psiLoc, psiLoc, psiLoc, map_add, map_add]`. Conclude with `AddChar.map_add_eq_mul ψ _ _`.
-/
theorem psiLoc_add (ψ : AddChar (AF F) ℂ) (v : Pl F) (a b : Fv F v) :
    psiLoc ψ v (a + b) = psiLoc ψ v a * psiLoc ψ v b := by
  rw [psiLoc, psiLoc, psiLoc, map_add, map_add]; exact AddChar.map_add_eq_mul ψ _ _

/- English proof (translation)
Rewrite using `[psiLoc, map_zero, map_zero]`. Conclude with `AddChar.map_zero_eq_one ψ`.
-/
theorem psiLoc_zero (ψ : AddChar (AF F) ℂ) (v : Pl F) : psiLoc ψ v 0 = 1 := by
  rw [psiLoc, map_zero, map_zero]; exact AddChar.map_zero_eq_one ψ

/- English proof (translation)
Distinguish the cases in `hY : Nonempty Y`. Use `swap`. Establish `hall : ∀ x, x ∈ U` using `fun x => by`. Assume the negation of the conclusion as `h`. Take `⟨y, -⟩` from `hsep x h`.

Conclude with `hY ⟨y⟩`. Use `hf using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `[hall x]`. Use `QuotientAddGroup.discreteTopology hU` as an intermediate fact.

Establish `hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite` using `(hfc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Establish `hsep' : ∀ q : V ⧸ U, ∃ y, q ≠ 0 → (∀ u ∈ U, e y u = 1) ∧ e y q.out ≠ 1`. Introduce `q`. Distinguish the cases in `hq : q = 0`. Conclude with `⟨Classical.arbitrary _, fun h => (h hq).elim⟩`.

Establish `: q.out ∉ U` using `fun h => hq (by rw [← QuotientAddGroup.out_eq' q]; exact (QuotientAddGroup.eq_zero_iff _).2 h)`. Take `⟨y, hy⟩` from `hsep _ this`. Conclude with `⟨y, fun _ => hy⟩`. Use `choose y hy using hsep'`. Use `set c : V ⧸ U → ℂ := fun q => e (y q) q.out with hcdef`.

Use `set Q := hfin.toFinset.filter (· ≠ 0) with hQ`. Establish `key : ∀ s : Finset (V ⧸ U), (fun x => (∏ q ∈ s, (e (y q) x - c q) / (1 - c q)) * f x) ∈ S`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hf`.

Consider the case `insert q s hq ih`. Establish `h2` using `hS (y q) _ ih`. Establish `: (fun x => (∏ r ∈ insert q s, (e (y r) x - c r) / (1 - c r)) * f x) = (1 - c q)⁻¹ • (fun x => e (y q) x * ((∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x)) + (-(c q) * (1 - c q)⁻¹) • (fun x => (∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.prod_insert hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `S.add_mem (S.smul_mem _ h2) (S.smul_mem _ ih)`. Use `key Q using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Distinguish the cases in `hx : x ∈ tsupport f`. Distinguish the cases in `hxU : x ∈ U`. Rewrite using `[if_pos hxU, Finset.prod_eq_one, one_mul]`. Introduce `q hq`. Establish `hq0 : q ≠ 0` using `(Finset.mem_filter.1 hq).2`.

Rewrite using `[(hy q hq0).1 x hxU, div_self (sub_ne_zero.2 (Ne.symm (hy q hq0).2))]`. Establish `hq0 : (QuotientAddGroup.mk x : V ⧸ U) ≠ 0` using `fun h => hxU ((QuotientAddGroup.eq_zero_iff _).1 h)`. Rewrite using `[if_neg hxU, Finset.prod_eq_zero (i := (QuotientAddGroup.mk x : V ⧸ U)), zero_mul]`. Conclude with `Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, hx, rfl⟩, hq0⟩`. Establish `hw : -(QuotientAddGroup.mk x : V ⧸ U).out + x ∈ U` using `QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)`.

Establish `: e (y (QuotientAddGroup.mk x)) x = c (QuotientAddGroup.mk x)`. Establish `h5 : e (y (QuotientAddGroup.mk x)) ((QuotientAddGroup.mk x : V ⧸ U).out + (-(QuotientAddGroup.mk x : V ⧸ U).out + x)) = e (y (QuotientAddGroup.mk x)) (QuotientAddGroup.mk x : V ⧸ U).out`. Rewrite using `[he, (hy _ hq0).1 _ hw, mul_one]`. Rewrite `h5` using `[add_neg_cancel_left]`. Conclude with `h5`.

Rewrite using `[this, sub_self, zero_div]`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Simplify using the standard rewrite rules.
-/
theorem mem_of_sep {V Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (e : Y → V → ℂ) (he : ∀ y a b, e y (a + b) = e y a * e y b)
    (S : Submodule ℂ (V → ℂ)) (hS : ∀ y, ∀ h ∈ S, (fun x => e y x * h x) ∈ S)
    (U : AddSubgroup V) (hU : IsOpen (U : Set V))
    (hsep : ∀ x ∉ U, ∃ y, (∀ u ∈ U, e y u = 1) ∧ e y x ≠ 1)
    {f : V → ℂ} (hf : f ∈ S) (hfc : HasCompactSupport f) :
    (fun x => if x ∈ U then f x else 0) ∈ S := by
  classical
  by_cases hY : Nonempty Y
  swap
  · have hall : ∀ x, x ∈ U := fun x => by
      by_contra h
      obtain ⟨y, -⟩ := hsep x h
      exact hY ⟨y⟩
    convert hf using 1
    funext x
    simp [hall x]
  have := QuotientAddGroup.discreteTopology hU
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite :=
    (hfc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hsep' : ∀ q : V ⧸ U, ∃ y, q ≠ 0 → (∀ u ∈ U, e y u = 1) ∧ e y q.out ≠ 1 := by
    intro q
    by_cases hq : q = 0
    · exact ⟨Classical.arbitrary _, fun h => (h hq).elim⟩
    · have : q.out ∉ U := fun h => hq (by rw [← QuotientAddGroup.out_eq' q]; exact (QuotientAddGroup.eq_zero_iff _).2 h)
      obtain ⟨y, hy⟩ := hsep _ this
      exact ⟨y, fun _ => hy⟩
  choose y hy using hsep'
  set c : V ⧸ U → ℂ := fun q => e (y q) q.out with hcdef
  set Q := hfin.toFinset.filter (· ≠ 0) with hQ
  have key : ∀ s : Finset (V ⧸ U), (fun x => (∏ q ∈ s, (e (y q) x - c q) / (1 - c q)) * f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | insert q s hq ih =>
      have h2 := hS (y q) _ ih
      have : (fun x => (∏ r ∈ insert q s, (e (y r) x - c r) / (1 - c r)) * f x) =
          (1 - c q)⁻¹ • (fun x => e (y q) x * ((∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x)) +
          (-(c q) * (1 - c q)⁻¹) • (fun x => (∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x) := by
        funext x
        simp only [Finset.prod_insert hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact S.add_mem (S.smul_mem _ h2) (S.smul_mem _ ih)
  convert key Q using 1
  funext x
  by_cases hx : x ∈ tsupport f
  · by_cases hxU : x ∈ U
    · rw [if_pos hxU, Finset.prod_eq_one, one_mul]
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_filter.1 hq).2
      rw [(hy q hq0).1 x hxU, div_self (sub_ne_zero.2 (Ne.symm (hy q hq0).2))]
    · have hq0 : (QuotientAddGroup.mk x : V ⧸ U) ≠ 0 := fun h => hxU ((QuotientAddGroup.eq_zero_iff _).1 h)
      rw [if_neg hxU, Finset.prod_eq_zero (i := (QuotientAddGroup.mk x : V ⧸ U)), zero_mul]
      · exact Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, hx, rfl⟩, hq0⟩
      · have hw : -(QuotientAddGroup.mk x : V ⧸ U).out + x ∈ U :=
          QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
        have : e (y (QuotientAddGroup.mk x)) x = c (QuotientAddGroup.mk x) := by
          have h5 : e (y (QuotientAddGroup.mk x)) ((QuotientAddGroup.mk x : V ⧸ U).out +
              (-(QuotientAddGroup.mk x : V ⧸ U).out + x)) = e (y (QuotientAddGroup.mk x)) (QuotientAddGroup.mk x : V ⧸ U).out := by
            rw [he, (hy _ hq0).1 _ hw, mul_one]
          rw [add_neg_cancel_left] at h5
          exact h5
        rw [this, sub_self, zero_div]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

/- English proof (translation)
Establish `hK : IsCompact (tsupport φ)` using `hc`. Establish `hloc : ∀ z : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ ∀ w ∈ W, φ (z + w) = φ z`. Introduce `z`. Establish `ho : IsOpen {u : V | φ (z + u) = φ z}` using `(hφ.comp_continuous (continuous_const.add continuous_id)).isOpen_fiber (φ z)`. Take `⟨W, hWo, hWs⟩` from `hB _ (ho.mem_nhds (by simp))`.

Conclude with `⟨W, hWo, fun w hw => hWs hw⟩`. Use `choose W hWo hW using hloc`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun z => (fun x => -z + x) ⁻¹' (W z : Set V)) (fun z => (hWo z).preimage (continuous_const.add continuous_id)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [(W x).zero_mem]⟩)`. Use `⟨⋂ z ∈ t, (W z : Set V), (Filter.biInter_finset_mem t).2 fun z _ => (hWo z).mem_nhds (W z).zero_mem, fun W' hW' => ?_⟩` and prove the remaining obligations. Establish `hin : ∀ x ∈ tsupport φ, ∀ w ∈ W', φ (x + w) = φ x`.

Introduce `x hx w hw`. Take `⟨z, hz, hxz⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Establish `hwz : w ∈ W z` using `Set.mem_iInter₂.1 (hW' hw) z hz`. Establish `hxz' : -z + x ∈ W z` using `hxz`. Establish `e1` using `hW z _ ((W z).add_mem hxz' hwz)`.

Establish `e2` using `hW z _ hxz'`. Rewrite `e1` using `[← add_assoc, add_neg_cancel_left]`. Rewrite `e2` using `[add_neg_cancel_left]`. Rewrite using `[e1, e2]`. Introduce `x w hw`.

Distinguish the cases in `hx : x ∈ tsupport φ`. Conclude with `hin x hx w hw`. Distinguish the cases in `hxw : x + w ∈ tsupport φ`. Use `hin _ hxw (-w) (W'.neg_mem hw)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`.

Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]`.
-/
theorem exists_periodic {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (hB : ∀ N ∈ 𝓝 (0 : V), ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ (W : Set V) ⊆ N)
    {φ : V → ℂ} (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ N ∈ 𝓝 (0 : V), ∀ W : AddSubgroup V, (W : Set V) ⊆ N → ∀ x, ∀ w ∈ W, φ (x + w) = φ x := by
  classical
  have hK : IsCompact (tsupport φ) := hc
  have hloc : ∀ z : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ ∀ w ∈ W, φ (z + w) = φ z := by
    intro z
    have ho : IsOpen {u : V | φ (z + u) = φ z} :=
      (hφ.comp_continuous (continuous_const.add continuous_id)).isOpen_fiber (φ z)
    obtain ⟨W, hWo, hWs⟩ := hB _ (ho.mem_nhds (by simp))
    exact ⟨W, hWo, fun w hw => hWs hw⟩
  choose W hWo hW using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z => (fun x => -z + x) ⁻¹' (W z : Set V))
    (fun z => (hWo z).preimage (continuous_const.add continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [(W x).zero_mem]⟩)
  refine ⟨⋂ z ∈ t, (W z : Set V), (Filter.biInter_finset_mem t).2 fun z _ => (hWo z).mem_nhds (W z).zero_mem,
    fun W' hW' => ?_⟩
  have hin : ∀ x ∈ tsupport φ, ∀ w ∈ W', φ (x + w) = φ x := by
    intro x hx w hw
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hwz : w ∈ W z := Set.mem_iInter₂.1 (hW' hw) z hz
    have hxz' : -z + x ∈ W z := hxz
    have e1 := hW z _ ((W z).add_mem hxz' hwz)
    have e2 := hW z _ hxz'
    rw [← add_assoc, add_neg_cancel_left] at e1
    rw [add_neg_cancel_left] at e2
    rw [e1, e2]
  intro x w hw
  by_cases hx : x ∈ tsupport φ
  · exact hin x hx w hw
  · by_cases hxw : x + w ∈ tsupport φ
    · have := hin _ hxw (-w) (W'.neg_mem hw)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

/- English proof (translation)
Establish `key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖u - 1‖ ≤ ‖u ^ 2 ^ k - 1‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Establish `h1 : u ^ 2 ^ (k + 1) - 1 = (u ^ 2 ^ k - 1) * (2 + (u ^ 2 ^ k - 1))` using `by rw [pow_succ, pow_mul]; ring`. Establish `h2 : (3 / 2 : ℝ) ≤ ‖2 + (u ^ 2 ^ k - 1)‖`. Use `norm_sub_norm_le (2 : ℂ) (-(u ^ 2 ^ k - 1))` as an intermediate fact. Rewrite `this` using `[norm_neg, sub_neg_eq_add, Complex.norm_two]`. Combine the linear relations using `[hu (2 ^ k)]`.

Rewrite using `[h1, norm_mul, pow_succ, mul_right_comm]`. Conclude with `mul_le_mul ih h2 (by norm_num) (norm_nonneg _)`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖u - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / 2 / ‖u - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`.

Rewrite `hk` using `[div_lt_iff₀ hpos]`. Combine the linear relations using `[key k, hu (2 ^ k)]`.
-/
theorem eq_one_of_pow_near {u : ℂ} (hu : ∀ n : ℕ, ‖u ^ n - 1‖ < 1 / 2) : u = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖u - 1‖ ≤ ‖u ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : u ^ 2 ^ (k + 1) - 1 = (u ^ 2 ^ k - 1) * (2 + (u ^ 2 ^ k - 1)) := by rw [pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖2 + (u ^ 2 ^ k - 1)‖ := by
        have := norm_sub_norm_le (2 : ℂ) (-(u ^ 2 ^ k - 1))
        rw [norm_neg, sub_neg_eq_add, Complex.norm_two] at this
        linarith [hu (2 ^ k)]
      rw [h1, norm_mul, pow_succ, mul_right_comm]
      exact mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖u - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  linarith [key k, hu (2 ^ k)]

/- English proof (translation)
Set `χA : AddChar (Fv F v) ℂ` to `{ toFun := psiLoc ψ v, map_zero_eq_one' := psiLoc_zero ψ v, map_add_eq_mul' := psiLoc_add ψ v }`. Establish `hsmall : ∃ N ∈ 𝓝 (0 : Fv F v), ∀ s ∈ N, psiLoc ψ v s = 1`. Establish `hc' : Continuous fun s => ‖psiLoc ψ v s - 1‖` using `by fun_prop`. Establish `h1 : {s : Fv F v | ‖psiLoc ψ v s - 1‖ < 1 / 2} ∈ 𝓝 0` using `(isOpen_lt hc' continuous_const).mem_nhds (by simp [psiLoc_zero])`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.1 h1`.

Use `⟨{x | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict x < γ}, (Valued.isClopen_ball _ _).isOpen.mem_nhds (by simp [zero_lt_iff]), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hn : ∀ n : ℕ, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (n • s) < γ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [zero_lt_iff]`.

Consider the case `succ n ih`. Rewrite using `[succ_nsmul]`. Conclude with `Valuation.map_add_lt _ ih hs`. Use `eq_one_of_pow_near fun n => ?_` and prove the remaining obligations. Rewrite using `[show psiLoc ψ v s ^ n = psiLoc ψ v (n • s) from (AddChar.map_nsmul_eq_pow χA n s).symm]`.

Conclude with `hγ (hn n)`. Take `⟨N, hN, hNχ⟩` from `hsmall`. Establish `hopen : IsOpen {s : Fv F v | psiLoc ψ v s = 1}`. Use `isOpen_iff_mem_nhds.2 fun s hs => ?_` and prove the remaining obligations. Rewrite using `[← map_add_left_nhds_zero]`.

Conclude with `Filter.mem_map.2 (Filter.mem_of_superset hN fun u hu => by show psiLoc ψ v (s + u) = 1`. Rewrite using `[psiLoc_add, show psiLoc ψ v s = 1 from hs, hNχ u hu, one_mul])`. Take `⟨w, hw⟩` from `hn`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hw (psiLoc_zero ψ v)`. Establish `hball : IsCompact {s : Fv F v | Valued.v s ≤ Valued.v w}`. Establish `: {s : Fv F v | Valued.v s ≤ Valued.v w} = (fun o => w * o) '' (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `s`. Prove the components needed by the constructor for the conclusion.

Introduce `hs`. Use `⟨s / w, ?_, by field_simp⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]`. Conclude with `div_le_one_of_le₀ hs zero_le'`. Introduce and unpack `⟨o, ho, rfl⟩ show Valued.v (w * o) ≤ Valued.v w`.

Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ho)`. Rewrite using `[this]`. Conclude with `(isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)).image (continuous_mul_left w)`. Use `set C := {s : Fv F v | Valued.v s ≤ Valued.v w} ∩ {s | psiLoc ψ v s ≠ 1} with hC`.

Establish `hCc : IsCompact C` using `hball.inter_right (show IsClosed {s : Fv F v | psiLoc ψ v s ≠ 1} from hopen.isClosed_compl)`. Establish `hloc : ∀ s ∈ C, {t : Fv F v | Valued.v t = Valued.v s} ∈ 𝓝 s`. Introduce `s hs`. Establish `hs0 : s ≠ 0` using `fun h => hs.2 (h ▸ psiLoc_zero ψ v)`. Establish `hr : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict s ≠ 0` using `(Valuation.ne_zero_iff _).2 hs0`.

Use `Valued.mem_nhds.2 ⟨Units.mk0 _ hr, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h1 : Valued.v (t - s) < Valued.v s` using `(Valuation.restrict_lt_iff _).1 ht`. Conclude with `Valuation.map_eq_of_sub_lt _ h1`. Take `⟨t, htC, hcov⟩` from `hCc.elim_nhds_subcover _ hloc`. Establish `hwC : w ∈ C` using `⟨show Valued.v w ≤ Valued.v w from le_rfl, hw⟩`.

Establish `htne : t.Nonempty`. Take `⟨x, hx, -⟩` from `Set.mem_iUnion₂.1 (hcov hwC)`. Conclude with `⟨x, hx⟩`. Take `⟨z, hzt, hzmin⟩` from `t.exists_min_image (fun x => Valued.v x) htne`. Use `⟨z, (htC z hzt).2, fun s hs => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hχs`. Distinguish the cases in `hsw : Valued.v s ≤ Valued.v w`. Take `⟨x, hx, hsx⟩` from `Set.mem_iUnion₂.1 (hcov ⟨hsw, hχs⟩)`. Establish `h1 : Valued.v z ≤ Valued.v x` using `hzmin x hx`. Establish `h2 : Valued.v s = Valued.v x` using `hsx`.

Rewrite `h1` using `[← h2]`. Conclude with `absurd hs (not_lt.2 h1)`. Conclude with `hsw (le_trans hs.le (htC z hzt).1)`.
-/
theorem exists_cond (ψ : AddChar (AF F) ℂ) (v : Pl F) (hc : Continuous (psiLoc ψ v))
    (hn : ∃ x : Fv F v, psiLoc ψ v x ≠ 1) :
    ∃ z : Fv F v, psiLoc ψ v z ≠ 1 ∧ ∀ s : Fv F v, Valued.v s < Valued.v z → psiLoc ψ v s = 1 := by
  classical
  let χA : AddChar (Fv F v) ℂ :=
    { toFun := psiLoc ψ v, map_zero_eq_one' := psiLoc_zero ψ v, map_add_eq_mul' := psiLoc_add ψ v }
  have hsmall : ∃ N ∈ 𝓝 (0 : Fv F v), ∀ s ∈ N, psiLoc ψ v s = 1 := by
    have hc' : Continuous fun s => ‖psiLoc ψ v s - 1‖ := by fun_prop
    have h1 : {s : Fv F v | ‖psiLoc ψ v s - 1‖ < 1 / 2} ∈ 𝓝 0 :=
      (isOpen_lt hc' continuous_const).mem_nhds (by simp [psiLoc_zero])
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 h1
    refine ⟨{x | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict x < γ},
      (Valued.isClopen_ball _ _).isOpen.mem_nhds (by simp [zero_lt_iff]), fun s hs => ?_⟩
    have hn : ∀ n : ℕ, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (n • s) < γ := by
      intro n
      induction n with
      | zero => simp [zero_lt_iff]
      | succ n ih =>
        rw [succ_nsmul]
        exact Valuation.map_add_lt _ ih hs
    refine eq_one_of_pow_near fun n => ?_
    rw [show psiLoc ψ v s ^ n = psiLoc ψ v (n • s) from (AddChar.map_nsmul_eq_pow χA n s).symm]
    exact hγ (hn n)
  obtain ⟨N, hN, hNχ⟩ := hsmall
  have hopen : IsOpen {s : Fv F v | psiLoc ψ v s = 1} := by
    refine isOpen_iff_mem_nhds.2 fun s hs => ?_
    rw [← map_add_left_nhds_zero]
    exact Filter.mem_map.2 (Filter.mem_of_superset hN fun u hu => by
      show psiLoc ψ v (s + u) = 1
      rw [psiLoc_add, show psiLoc ψ v s = 1 from hs, hNχ u hu, one_mul])
  obtain ⟨w, hw⟩ := hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (psiLoc_zero ψ v)
  have hball : IsCompact {s : Fv F v | Valued.v s ≤ Valued.v w} := by
    have : {s : Fv F v | Valued.v s ≤ Valued.v w} =
        (fun o => w * o) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext s
      constructor
      · intro hs
        refine ⟨s / w, ?_, by field_simp⟩
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ hs zero_le'
      · rintro ⟨o, ho, rfl⟩
        show Valued.v (w * o) ≤ Valued.v w
        rw [map_mul]
        exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ho)
    rw [this]
    exact (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)).image
      (continuous_mul_left w)
  set C := {s : Fv F v | Valued.v s ≤ Valued.v w} ∩ {s | psiLoc ψ v s ≠ 1} with hC
  have hCc : IsCompact C := hball.inter_right (show IsClosed {s : Fv F v | psiLoc ψ v s ≠ 1} from hopen.isClosed_compl)
  have hloc : ∀ s ∈ C, {t : Fv F v | Valued.v t = Valued.v s} ∈ 𝓝 s := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => hs.2 (h ▸ psiLoc_zero ψ v)
    have hr : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict s ≠ 0 :=
      (Valuation.ne_zero_iff _).2 hs0
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr, fun t ht => ?_⟩
    have h1 : Valued.v (t - s) < Valued.v s := (Valuation.restrict_lt_iff _).1 ht
    exact Valuation.map_eq_of_sub_lt _ h1
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover _ hloc
  have hwC : w ∈ C := ⟨show Valued.v w ≤ Valued.v w from le_rfl, hw⟩
  have htne : t.Nonempty := by
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hcov hwC)
    exact ⟨x, hx⟩
  obtain ⟨z, hzt, hzmin⟩ := t.exists_min_image (fun x => Valued.v x) htne
  refine ⟨z, (htC z hzt).2, fun s hs => ?_⟩
  by_contra hχs
  by_cases hsw : Valued.v s ≤ Valued.v w
  · obtain ⟨x, hx, hsx⟩ := Set.mem_iUnion₂.1 (hcov ⟨hsw, hχs⟩)
    have h1 : Valued.v z ≤ Valued.v x := hzmin x hx
    have h2 : Valued.v s = Valued.v x := hsx
    rw [← h2] at h1
    exact absurd hs (not_lt.2 h1)
  · exact hsw (le_trans hs.le (htC z hzt).1)

/- English proof (translation)
Establish `hN' : N ∈ Filter.pi fun _ : κ => 𝓝 (0 : Fv F v)` using `by simpa [nhds_pi] using hN`. Take `⟨⟨I, γ⟩, -, hsub⟩` from `(Filter.hasBasis_pi fun _ : κ => Valued.hasBasis_nhds_zero (Fv F v) (WithZero (Multiplicative ℤ))).mem_iff.1 hN'`. Establish `hz0 : z ≠ 0` using `by rintro rfl; exact hz (psiLoc_zero ψ v)`. Set `U : AddSubgroup (κ → Fv F v)` to `{ carrier := {x | ∀ i, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) < ((γ i : _) : _)} zero_mem' := fun i => by`. Simplify using `only [Pi.zero_apply, map_zero]`.

Conclude with `zero_lt_iff.2 (γ i).ne_zero`. Use the proof step `add_mem' := fun hx hy i => Valuation.map_add_lt _ (hx i) (hy i)`. Use the proof step `neg_mem' := fun hx i => by simpa only [Pi.neg_apply, Valuation.map_neg] using hx i }`. Use `⟨U, ?_, fun x hx => hsub fun i _ => hx i, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: (U : Set (κ → Fv F v)) = Set.univ.pi fun i => {y | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < ((γ i : _) : _)}`.

Use extensionality with `x`. Simplify using `[U]`. Rewrite using `[this]`. Conclude with `isOpen_set_pi Set.finite_univ fun i _ => (Valued.isClopen_ball _ _).isOpen`. Establish `hx' : ∃ i, ((γ i : _) : _) ≤ (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i)`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx h`. Take `⟨i, hi⟩` from `hx'`. Establish `hxi : x i ≠ 0`.

Introduce `h`. Rewrite `hi` using `[h, map_zero]`. Conclude with `(γ i).ne_zero (le_antisymm hi zero_le')`. Use `⟨Pi.single i (z / x i), fun u hu => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[dotProduct_single]`.

Apply `hzs` to reduce the goal to its premises. Establish `h1 : Valued.v (u i) < Valued.v (x i)` using `(Valuation.restrict_lt_iff _).1 (lt_of_lt_of_le (hu i) hi)`. Establish `h2 : Valued.v (u i / x i) < 1`. Rewrite using `[map_div₀]`. Conclude with `(div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hxi))).2 h1`.

Rewrite using `[show u i * (z / x i) = (u i / x i) * z by ring, map_mul]`. Conclude with `mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz0)) h2`. Rewrite using `[dotProduct_single, mul_div_cancel₀ _ hxi]`. Conclude with `hz`.
-/
theorem exists_sub (ψ : AddChar (AF F) ℂ) (v : Pl F) {z : Fv F v} (hz : psiLoc ψ v z ≠ 1)
    (hzs : ∀ s : Fv F v, Valued.v s < Valued.v z → psiLoc ψ v s = 1) {κ : Type} [Fintype κ]
    {N : Set (κ → Fv F v)} (hN : N ∈ 𝓝 (0 : κ → Fv F v)) :
    ∃ U : AddSubgroup (κ → Fv F v), IsOpen (U : Set (κ → Fv F v)) ∧ (U : Set (κ → Fv F v)) ⊆ N ∧
      ∀ x ∉ U, ∃ t, (∀ u ∈ U, psiLoc ψ v (u ⬝ᵥ t) = 1) ∧ psiLoc ψ v (x ⬝ᵥ t) ≠ 1 := by
  have hN' : N ∈ Filter.pi fun _ : κ => 𝓝 (0 : Fv F v) := by simpa [nhds_pi] using hN
  obtain ⟨⟨I, γ⟩, -, hsub⟩ := (Filter.hasBasis_pi fun _ : κ => Valued.hasBasis_nhds_zero (Fv F v) (WithZero (Multiplicative ℤ))).mem_iff.1 hN'
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (psiLoc_zero ψ v)
  let U : AddSubgroup (κ → Fv F v) :=
    { carrier := {x | ∀ i, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) < ((γ i : _) : _)}
      zero_mem' := fun i => by
        simp only [Pi.zero_apply, map_zero]
        exact zero_lt_iff.2 (γ i).ne_zero
      add_mem' := fun hx hy i => Valuation.map_add_lt _ (hx i) (hy i)
      neg_mem' := fun hx i => by simpa only [Pi.neg_apply, Valuation.map_neg] using hx i }
  refine ⟨U, ?_, fun x hx => hsub fun i _ => hx i, fun x hx => ?_⟩
  · have : (U : Set (κ → Fv F v)) = Set.univ.pi fun i => {y | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < ((γ i : _) : _)} := by
      ext x; simp [U]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun i _ => (Valued.isClopen_ball _ _).isOpen
  · have hx' : ∃ i, ((γ i : _) : _) ≤ (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) := by
      by_contra h
      push_neg at h
      exact hx h
    obtain ⟨i, hi⟩ := hx'
    have hxi : x i ≠ 0 := by
      intro h
      rw [h, map_zero] at hi
      exact (γ i).ne_zero (le_antisymm hi zero_le')
    refine ⟨Pi.single i (z / x i), fun u hu => ?_, ?_⟩
    · rw [dotProduct_single]
      apply hzs
      have h1 : Valued.v (u i) < Valued.v (x i) := (Valuation.restrict_lt_iff _).1 (lt_of_lt_of_le (hu i) hi)
      have h2 : Valued.v (u i / x i) < 1 := by
        rw [map_div₀]
        exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hxi))).2 h1
      rw [show u i * (z / x i) = (u i / x i) * z by ring, map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz0)) h2
    · rw [dotProduct_single, mul_div_cancel₀ _ hxi]
      exact hz

/- English proof (translation)
Introduce `F _ _ ψ v hc hn κ _ φ₀ φ h0 hne hφ`. Use `set S := Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) with hS`. Establish `htr : ∀ a, ∀ h ∈ S, (fun x => h (x + a)) ∈ S`. Introduce `a h hh`. Proceed by induction on `hh using Submodule.span_induction with`.

Consider the case `mem g hg`. Take `⟨⟨x₁, y⟩, rfl⟩` from `hg`. Establish `: (fun x => GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ (x + a)) = psiLoc ψ v (a ⬝ᵥ y / 2) • GlobalTheory.FinComm.locOp ψ v (x₁ + a, y) φ₀`. Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[← mul_assoc, ← psiLoc_add]`. Use `congr 1`. Use `congr 1`. Simplify using `only [add_dotProduct]`. Establish `h2 : (2 : Fv F v) ≠ 0`.

Use `(map_ne_zero (algebraMap F (Fv F v))).2 (two_ne_zero (α := F))` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take the linear combination `(-(a ⬝ᵥ y)) * inv_mul_cancel₀ h2`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `zero => exact S.zero_mem`. Consider the case `add g₁ g₂ _ _ ih₁ ih₂ => exact S.add_mem ih₁ ih₂`. Consider the case `smul c g _ ih => exact S.smul_mem c ih`.

Establish `hmod : ∀ t, ∀ h ∈ S, (fun x => psiLoc ψ v (x ⬝ᵥ t) * h x) ∈ S`. Introduce `t h hh`. Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨⟨x₁, y⟩, rfl⟩` from `hg`.

Establish `: (fun x => psiLoc ψ v (x ⬝ᵥ t) * GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ x) = psiLoc ψ v (-(x₁ ⬝ᵥ t) / 2) • GlobalTheory.FinComm.locOp ψ v (x₁, y + t) φ₀`. Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← psiLoc_add, ← psiLoc_add]`. Use `congr 2`.

Simplify using `only [dotProduct_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `zero`.

Use `S.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Consider the case `add g₁ g₂ _ _ ih₁ ih₂`. Use `S.add_mem ih₁ ih₂ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using `[mul_add]`. Consider the case `smul c g _ ih`. Use `S.smul_mem c ih using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨z, hz, hzs⟩` from `exists_cond ψ v hc hn`. Establish `hB : ∀ N ∈ 𝓝 (0 : κ → Fv F v), ∃ W : AddSubgroup (κ → Fv F v), IsOpen (W : Set (κ → Fv F v)) ∧ (W : Set (κ → Fv F v)) ⊆ N`. Introduce `N hN`.

Take `⟨U, h1, h2, -⟩` from `exists_sub ψ v hz hzs hN`. Conclude with `⟨U, h1, h2⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc0⟩ : ∃ c, φ₀ c ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne (funext h)`. Use `set f : (κ → Fv F v) → ℂ := fun x => φ₀ (x + c) with hfdef`. Establish `hfS : f ∈ S`. Establish `: f = GlobalTheory.FinComm.locOp ψ v (c, 0) φ₀`. Use function extensionality and compare the values at `x`.

Simplify using `[f, GlobalTheory.FinComm.locOp, psiLoc_zero]`. Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `hfc : HasCompactSupport f` using `h0.2.comp_homeomorph (Homeomorph.addRight c)`. Establish `hfl : IsLocallyConstant f` using `h0.1.comp_continuous (continuous_add_right c)`.

Establish `hf0 : f 0 ≠ 0` using `by simpa [f] using hc0`. Establish `hN1 : {u | f u = f 0} ∈ 𝓝 (0 : κ → Fv F v)` using `(hfl.isOpen_fiber (f 0)).mem_nhds rfl`. Take `⟨N2, hN2, hper⟩` from `exists_periodic hB hφ.1 hφ.2`. Take `⟨U, hUo, hUs, hsep⟩` from `exists_sub ψ v hz hzs (Filter.inter_mem hN1 hN2)`. Establish `h1U : (fun x => if x ∈ U then f x else 0) ∈ S` using `mem_of_sep (fun t x => psiLoc ψ v (x ⬝ᵥ t)) (fun t a b => by rw [add_dotProduct, psiLoc_add]) S hmod U hUo hsep hfS hfc`.

Establish `hind : ∀ a : κ → Fv F v, (fun x => if x + a ∈ U then (1 : ℂ) else 0) ∈ S`. Introduce `a`. Establish `h2 : (fun x => if x ∈ U then (1 : ℂ) else 0) ∈ S`. Establish `: (fun x => if x ∈ U then (1 : ℂ) else 0) = (f 0)⁻¹ • (fun x => if x ∈ U then f x else 0)`. Use function extensionality and compare the values at `x`.

Distinguish the cases in `hx : x ∈ U`. Establish `: f x = f 0` using `(hUs hx).1`. Simplify using `only [hx, if_true, Pi.smul_apply, smul_eq_mul, this, inv_mul_cancel₀ hf0]`. Simplify using `[hx]`. Rewrite using `[this]`.

Conclude with `S.smul_mem _ h1U`. Conclude with `htr a _ h2`. Establish `hper' : ∀ x, ∀ w ∈ U, φ (x + w) = φ x` using `hper U fun y hy => (hUs hy).2`. Use `QuotientAddGroup.discreteTopology hUo` as an intermediate fact. Establish `hfin : ((QuotientAddGroup.mk : (κ → Fv F v) → (κ → Fv F v) ⧸ U) '' tsupport φ).Finite` using `(hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete`.

Establish `hsum : φ = ∑ q ∈ hfin.toFinset, φ q.out • (fun x => if x + -q.out ∈ U then (1 : ℂ) else 0)`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Establish `hmem : ∀ q : (κ → Fv F v) ⧸ U, x + -q.out ∈ U ↔ q = QuotientAddGroup.mk x`. Introduce `q`.

Rewrite using `[add_comm, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']`. Establish `hval : φ (QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out = φ x`. Establish `h3 : x + -(QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out ∈ U` using `(hmem _).2 rfl`. Establish `h4` using `hper' x _ (U.neg_mem h3)`. Rewrite `h4` using `[neg_add, neg_neg, add_neg_cancel_left]`.

Conclude with `h4`. Rewrite using `[Finset.sum_eq_single (QuotientAddGroup.mk x)]`. Rewrite using `[if_pos ((hmem _).2 rfl), hval]`. Introduce `q _ hq`. Rewrite using `[if_neg fun h => hq ((hmem q).1 h)]`.

Introduce `hx`. Establish `hx' : x ∉ tsupport φ` using `fun h => hx (hfin.mem_toFinset.2 ⟨x, h, rfl⟩)`. Use `split_ifs`. Rewrite using `[hval, image_eq_zero_of_notMem_tsupport hx']`. Both sides reduce to the same expression.

Rewrite using `[hsum]`. Conclude with `S.sum_mem fun q _ => S.smul_mem _ (hind _)`.
-/
theorem mem_span_locOp : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F), Continuous (psiLoc ψ v) →
    (∃ x : Fv F v, psiLoc ψ v x ≠ 1) → ∀ {κ : Type} [Fintype κ] (φ₀ φ : (κ → Fv F v) → ℂ), φ₀ ∈ SB _ → φ₀ ≠ 0 →
    φ ∈ SB _ → φ ∈ Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) := by
  intro F _ _ ψ v hc hn κ _ φ₀ φ h0 hne hφ
  set S := Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) with hS
  have htr : ∀ a, ∀ h ∈ S, (fun x => h (x + a)) ∈ S := by
    intro a h hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨x₁, y⟩, rfl⟩ := hg
      have : (fun x => GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ (x + a)) =
          psiLoc ψ v (a ⬝ᵥ y / 2) • GlobalTheory.FinComm.locOp ψ v (x₁ + a, y) φ₀ := by
        funext x
        simp only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← psiLoc_add]
        congr 1
        · congr 1
          simp only [add_dotProduct]
          have h2 : (2 : Fv F v) ≠ 0 := by
            have := (map_ne_zero (algebraMap F (Fv F v))).2 (two_ne_zero (α := F))
            rwa [map_ofNat] at this
          linear_combination (-(a ⬝ᵥ y)) * inv_mul_cancel₀ h2
        · congr 1
          abel
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => exact S.zero_mem
    | add g₁ g₂ _ _ ih₁ ih₂ => exact S.add_mem ih₁ ih₂
    | smul c g _ ih => exact S.smul_mem c ih
  have hmod : ∀ t, ∀ h ∈ S, (fun x => psiLoc ψ v (x ⬝ᵥ t) * h x) ∈ S := by
    intro t h hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨x₁, y⟩, rfl⟩ := hg
      have : (fun x => psiLoc ψ v (x ⬝ᵥ t) * GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ x) =
          psiLoc ψ v (-(x₁ ⬝ᵥ t) / 2) • GlobalTheory.FinComm.locOp ψ v (x₁, y + t) φ₀ := by
        funext x
        simp only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← mul_assoc, ← psiLoc_add, ← psiLoc_add]
        congr 2
        simp only [dotProduct_add]
        ring
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero =>
      convert S.zero_mem using 1
      funext x
      simp
    | add g₁ g₂ _ _ ih₁ ih₂ =>
      convert S.add_mem ih₁ ih₂ using 1
      funext x
      simp [mul_add]
    | smul c g _ ih =>
      convert S.smul_mem c ih using 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  obtain ⟨z, hz, hzs⟩ := exists_cond ψ v hc hn
  have hB : ∀ N ∈ 𝓝 (0 : κ → Fv F v), ∃ W : AddSubgroup (κ → Fv F v), IsOpen (W : Set (κ → Fv F v)) ∧ (W : Set (κ → Fv F v)) ⊆ N := by
    intro N hN
    obtain ⟨U, h1, h2, -⟩ := exists_sub ψ v hz hzs hN
    exact ⟨U, h1, h2⟩
  obtain ⟨c, hc0⟩ : ∃ c, φ₀ c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set f : (κ → Fv F v) → ℂ := fun x => φ₀ (x + c) with hfdef
  have hfS : f ∈ S := by
    have : f = GlobalTheory.FinComm.locOp ψ v (c, 0) φ₀ := by
      funext x
      simp [f, GlobalTheory.FinComm.locOp, psiLoc_zero]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hfc : HasCompactSupport f := h0.2.comp_homeomorph (Homeomorph.addRight c)
  have hfl : IsLocallyConstant f := h0.1.comp_continuous (continuous_add_right c)
  have hf0 : f 0 ≠ 0 := by simpa [f] using hc0
  have hN1 : {u | f u = f 0} ∈ 𝓝 (0 : κ → Fv F v) := (hfl.isOpen_fiber (f 0)).mem_nhds rfl
  obtain ⟨N2, hN2, hper⟩ := exists_periodic hB hφ.1 hφ.2
  obtain ⟨U, hUo, hUs, hsep⟩ := exists_sub ψ v hz hzs (Filter.inter_mem hN1 hN2)
  have h1U : (fun x => if x ∈ U then f x else 0) ∈ S :=
    mem_of_sep (fun t x => psiLoc ψ v (x ⬝ᵥ t)) (fun t a b => by rw [add_dotProduct, psiLoc_add]) S hmod U hUo
      hsep hfS hfc
  have hind : ∀ a : κ → Fv F v, (fun x => if x + a ∈ U then (1 : ℂ) else 0) ∈ S := by
    intro a
    have h2 : (fun x => if x ∈ U then (1 : ℂ) else 0) ∈ S := by
      have : (fun x => if x ∈ U then (1 : ℂ) else 0) = (f 0)⁻¹ • (fun x => if x ∈ U then f x else 0) := by
        funext x
        by_cases hx : x ∈ U
        · have : f x = f 0 := (hUs hx).1
          simp only [hx, if_true, Pi.smul_apply, smul_eq_mul, this, inv_mul_cancel₀ hf0]
        · simp [hx]
      rw [this]
      exact S.smul_mem _ h1U
    exact htr a _ h2
  have hper' : ∀ x, ∀ w ∈ U, φ (x + w) = φ x := hper U fun y hy => (hUs hy).2
  have := QuotientAddGroup.discreteTopology hUo
  have hfin : ((QuotientAddGroup.mk : (κ → Fv F v) → (κ → Fv F v) ⧸ U) '' tsupport φ).Finite :=
    (hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hsum : φ = ∑ q ∈ hfin.toFinset, φ q.out • (fun x => if x + -q.out ∈ U then (1 : ℂ) else 0) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    have hmem : ∀ q : (κ → Fv F v) ⧸ U, x + -q.out ∈ U ↔ q = QuotientAddGroup.mk x := by
      intro q
      rw [add_comm, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hval : φ (QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out = φ x := by
      have h3 : x + -(QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out ∈ U := (hmem _).2 rfl
      have h4 := hper' x _ (U.neg_mem h3)
      rw [neg_add, neg_neg, add_neg_cancel_left] at h4
      exact h4
    rw [Finset.sum_eq_single (QuotientAddGroup.mk x)]
    · rw [if_pos ((hmem _).2 rfl), hval]
    · intro q _ hq
      rw [if_neg fun h => hq ((hmem q).1 h)]
    · intro hx
      have hx' : x ∉ tsupport φ := fun h => hx (hfin.mem_toFinset.2 ⟨x, h, rfl⟩)
      split_ifs
      · rw [hval, image_eq_zero_of_notMem_tsupport hx']
      · rfl
  rw [hsum]
  exact S.sum_mem fun q _ => S.smul_mem _ (hind _)

end GlobalTheory.SchrCyclic
