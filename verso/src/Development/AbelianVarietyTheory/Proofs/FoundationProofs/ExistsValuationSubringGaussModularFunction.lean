import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderPfA

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GaussDom

variable {Ω : Type} [Field Ω] (V : ValuationSubring Ω)

def incH : HahnSeries ℚ V →+* HahnSeries ℚ Ω where
  toFun x := x.map V.subtype
  map_one' := HahnSeries.map_one V.subtype.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul V.subtype.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero V.subtype.toZeroHom
  map_add' _ _ := HahnSeries.map_add V.subtype.toAddMonoidHom

def redH : HahnSeries ℚ V →+* HahnSeries ℚ (IsLocalRing.ResidueField V) where
  toFun x := x.map (IsLocalRing.residue V)
  map_one' := HahnSeries.map_one (IsLocalRing.residue V).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (IsLocalRing.residue V).toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero (IsLocalRing.residue V).toZeroHom
  map_add' _ _ := HahnSeries.map_add (IsLocalRing.residue V).toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma incH_coeff (x : HahnSeries ℚ V) (r : ℚ) : (incH V x).coeff r = (x.coeff r : Ω) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma redH_coeff (x : HahnSeries ℚ V) (r : ℚ) :
    (redH V x).coeff r = IsLocalRing.residue V (x.coeff r) := rfl

/- English proof (translation)
Introduce `x y h`. Use extensionality with `r`. Use `congrArg (fun z => z.coeff r) h` as an intermediate fact. Simplify using `only [incH_coeff] at this`. Conclude with `this`.
-/
lemma incH_injective : Function.Injective (incH V) := by
  intro x y h
  ext r
  have := congrArg (fun z => z.coeff r) h
  simp only [incH_coeff] at this
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ r`. Conclude with `(y.coeff r).2`. Introduce `h`. Use `⟨⟨fun r => ⟨x.coeff r, h r⟩, x.isPWO_support.mono ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `r hr`. Rewrite using `[HahnSeries.mem_support]`. Introduce `h0`. Conclude with `hr (Subtype.ext h0)`. Use extensionality with `r`.

Both sides reduce to the same expression.
-/
lemma mem_range_incH (x : HahnSeries ℚ Ω) : x ∈ (incH V).range ↔ ∀ r, x.coeff r ∈ V := by
  constructor
  · rintro ⟨y, rfl⟩ r
    exact (y.coeff r).2
  · intro h
    refine ⟨⟨fun r => ⟨x.coeff r, h r⟩, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro r hr
      rw [HahnSeries.mem_support]
      intro h0
      exact hr (Subtype.ext h0)
    · ext r
      rfl

variable {K : Type} [Field K] [Algebra Ω K] (e : K →ₐ[Ω] HahnSeries ℚ Ω)

def intA : Subring K := (incH V).range.comap e.toRingHom

/- English proof (translation)
Rewrite using `[intA, Subring.mem_comap]`. Conclude with `mem_range_incH V (e f)`.
-/
lemma mem_intA (f : K) : f ∈ intA V e ↔ ∀ r, (e f).coeff r ∈ V := by
  rw [intA, Subring.mem_comap]
  exact mem_range_incH V (e f)

def eqvH : HahnSeries ℚ V ≃+* (incH V).range :=
  RingEquiv.ofBijective (incH V).rangeRestrict
    ⟨fun x y h => incH_injective V (congrArg Subtype.val h), (incH V).rangeRestrict_surjective⟩

def redA : intA V e →+* HahnSeries ℚ (IsLocalRing.ResidueField V) :=
  (redH V).comp ((eqvH V).symm.toRingHom.comp
    (e.toRingHom.restrict (intA V e) (incH V).range (fun _ hx => hx)))

/- English proof (translation)
Establish `hy : incH V ((eqvH V).symm (e.toRingHom.restrict (intA V e) (incH V).range (fun _ hx => hx) f)) = e f` using `congrArg Subtype.val ((eqvH V).apply_symm_apply (e.toRingHom.restrict (intA V e) (incH V).range (fun _ hx => hx) f))`. Use `show IsLocalRing.residue V (((eqvH V).symm _).coeff r) = _`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← incH_coeff, hy]`.
-/
lemma redA_coeff (f : intA V e) (r : ℚ) :
    (redA V e f).coeff r = IsLocalRing.residue V ⟨(e f).coeff r, (mem_intA V e f).1 f.2 r⟩ := by
  have hy : incH V ((eqvH V).symm (e.toRingHom.restrict (intA V e) (incH V).range (fun _ hx => hx) f)) = e f :=
    congrArg Subtype.val ((eqvH V).apply_symm_apply
      (e.toRingHom.restrict (intA V e) (incH V).range (fun _ hx => hx) f))
  show IsLocalRing.residue V (((eqvH V).symm _).coeff r) = _
  congr 1
  apply Subtype.ext
  rw [← incH_coeff, hy]

/- English proof (translation)
Rewrite using `[← HahnSeries.coeff_inj, funext_iff]`. Use `forall_congr' fun r => ?_` and prove the remaining obligations. Rewrite using `[redA_coeff, HahnSeries.coeff_zero, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]`.
-/
lemma redA_eq_zero (f : intA V e) : redA V e f = 0 ↔ ∀ r, (e f).coeff r ∈ V.nonunits := by
  rw [← HahnSeries.coeff_inj, funext_iff]
  refine forall_congr' fun r => ?_
  rw [redA_coeff, HahnSeries.coeff_zero, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff,
    ValuationSubring.mem_nonunits_iff]

end GlobalTheory.KZ.GaussDom

namespace GlobalTheory.KZ.GaussDom

/- English proof (translation)
Rewrite using `[HahnSeries.algebraMap_apply']`. Simplify using the standard rewrite rules.
-/
lemma algS {k : Type} [Field k] (c : k) :
    algebraMap k (HahnSeries ℚ k) c = HahnSeries.single (0 : ℚ) c := by
  rw [HahnSeries.algebraMap_apply']; simp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Q hQ hn`. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero hn, Polynomial.aeval_C, algS]`.

Establish `h0 : Q.coeff 0 ≠ 0`. Introduce `h`. Apply `hQ` to reduce the goal to its premises. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero hn, h, map_zero]`. Rewrite using `[HahnSeries.orderTop_single (by simpa using h0)]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `Q hQ hn`. Establish `hd : Q.divX ≠ 0`. Introduce `h`.

Rewrite `h` using `[Polynomial.divX_eq_zero_iff]`. Rewrite `hn` using `[h, Polynomial.natDegree_C]`. Conclude with `Nat.succ_ne_zero n hn.symm`. Establish `hdn : Q.divX.natDegree = n`. Rewrite using `[Polynomial.natDegree_divX_eq_natDegree_tsub_one, hn]`.

Both sides reduce to the same expression. Establish `hsplit` using `Polynomial.X_mul_divX_add Q`. Establish `hR` using `ih Q.divX hd hdn`. Rewrite using `[← hsplit, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]`. Establish `hm : (J * Polynomial.aeval J Q.divX).orderTop = ((-((n + 1 : ℕ) : ℚ) : ℚ) : WithTop ℚ)`.

Rewrite using `[HahnSeries.orderTop_mul, hJ, hR, ← WithTop.coe_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[HahnSeries.orderTop_add_eq_left, hm]`.

Rewrite using `[hm, algS]`. Use `lt_of_lt_of_le ?_ HahnSeries.orderTop_single_le` and prove the remaining obligations. Conclude with `WithTop.coe_lt_coe.2 (by push_cast; linarith)`.
-/
lemma orderTop_aeval {k : Type} [Field k] (J : HahnSeries ℚ k) (hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ)) :
    ∀ (n : ℕ) (Q : Polynomial k), Q ≠ 0 → Q.natDegree = n →
      (Polynomial.aeval J Q).orderTop = ((-(n : ℚ) : ℚ) : WithTop ℚ) := by
  intro n
  induction n with
  | zero =>
    intro Q hQ hn
    rw [Polynomial.eq_C_of_natDegree_eq_zero hn, Polynomial.aeval_C, algS]
    have h0 : Q.coeff 0 ≠ 0 := by
      intro h; apply hQ
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn, h, map_zero]
    rw [HahnSeries.orderTop_single (by simpa using h0)]
    simp
  | succ n ih =>
    intro Q hQ hn
    have hd : Q.divX ≠ 0 := by
      intro h
      rw [Polynomial.divX_eq_zero_iff] at h
      rw [h, Polynomial.natDegree_C] at hn
      exact Nat.succ_ne_zero n hn.symm
    have hdn : Q.divX.natDegree = n := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hn]; rfl
    have hsplit := Polynomial.X_mul_divX_add Q
    have hR := ih Q.divX hd hdn
    rw [← hsplit, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    have hm : (J * Polynomial.aeval J Q.divX).orderTop = ((-((n + 1 : ℕ) : ℚ) : ℚ) : WithTop ℚ) := by
      rw [HahnSeries.orderTop_mul, hJ, hR, ← WithTop.coe_add]
      congr 1
      push_cast; ring
    rw [HahnSeries.orderTop_add_eq_left, hm]
    rw [hm, algS]
    refine lt_of_lt_of_le ?_ HahnSeries.orderTop_single_le
    exact WithTop.coe_lt_coe.2 (by push_cast; linarith)

end GlobalTheory.KZ.GaussDom

namespace GlobalTheory.KZ.GaussDom

variable {Ω : Type} [Field Ω] (V : ValuationSubring Ω) {K : Type} [Field K] [Algebra Ω K]
  (e : K →ₐ[Ω] HahnSeries ℚ Ω)

/- English proof (translation)
Rewrite using `[e.commutes, algS, HahnSeries.coeff_single]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma coeff_const (c : Ω) (r : ℚ) : (e (algebraMap Ω K c)).coeff r = if r = 0 then c else 0 := by
  rw [e.commutes, algS, HahnSeries.coeff_single]
  split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[mem_intA]`. Introduce `r`. Rewrite using `[coeff_const]`. Use `split_ifs`. Use `exacts [hc, V.zero_mem]`.
-/
lemma const_mem (c : Ω) (hc : c ∈ V) : algebraMap Ω K c ∈ intA V e := by
  rw [mem_intA]
  intro r
  rw [coeff_const]
  split_ifs
  exacts [hc, V.zero_mem]

/- English proof (translation)
Rewrite using `[ValuationSubring.mem_nonunits_iff, map_zero]`. Conclude with `zero_lt_one`.
-/
lemma zero_mem_nonunits : (0 : Ω) ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]
  exact zero_lt_one

/- English proof (translation)
Apply `HahnSeries.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `r`. Rewrite using `[redA_coeff, algS, HahnSeries.coeff_single]`. Distinguish the cases in `hr : r = 0`. Rewrite using `[if_pos hr]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (e (algebraMap Ω K v)).coeff r = v`. Rewrite using `[coeff_const, if_pos hr]`. Rewrite using `[if_neg hr]`.

Establish `h0 : (⟨(e (algebraMap Ω K v)).coeff r, (mem_intA V e _).1 (const_mem V e v v.2) r⟩ : V) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (e (algebraMap Ω K v)).coeff r = 0`. Rewrite using `[coeff_const, if_neg hr]`. Rewrite using `[h0, map_zero]`.
-/
lemma redA_const (v : V) :
    redA V e ⟨algebraMap Ω K v, const_mem V e v v.2⟩ =
      algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))
        (IsLocalRing.residue V v) := by
  apply HahnSeries.ext
  funext r
  rw [redA_coeff, algS, HahnSeries.coeff_single]
  by_cases hr : r = 0
  · rw [if_pos hr]
    congr 1
    apply Subtype.ext
    show (e (algebraMap Ω K v)).coeff r = v
    rw [coeff_const, if_pos hr]
  · rw [if_neg hr]
    have h0 : (⟨(e (algebraMap Ω K v)).coeff r, (mem_intA V e _).1 (const_mem V e v v.2) r⟩ : V) = 0 := by
      apply Subtype.ext
      show (e (algebraMap Ω K v)).coeff r = 0
      rw [coeff_const, if_neg hr]
    rw [h0, map_zero]

/- English proof (translation)
Use `haveI : (RingHom.ker (redA V e)).IsPrime := RingHom.ker_isPrime _`. Take `⟨W, hA, hinv, hlt⟩` from `ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd.exists_val_of_prime (intA V e) (RingHom.ker (redA V e))`. Establish `hker : ∀ x : intA V e, x ∈ RingHom.ker (redA V e) ↔ ∀ r, (e x).coeff r ∈ V.nonunits` using `fun x => (RingHom.mem_ker).trans (redA_eq_zero V e x)`. Establish `hone : ∀ x : intA V e, x ∉ RingHom.ker (redA V e) → W.valuation (x : K) = 1`. Introduce `x hx`.

Establish `hx0 : (x : K) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Establish `: x = 0` using `Subtype.ext h0`. Rewrite using `[this]`.

Conclude with `Ideal.zero_mem _`. Establish `h1` using `(W.valuation_le_one_iff _).2 (hA x)`. Establish `h2` using `(W.valuation_le_one_iff _).2 (hinv x hx)`. Rewrite `h2` using `[map_inv₀]`. Establish `hv0 : W.valuation (x : K) ≠ 0` using `by simpa using hx0`.

Conclude with `le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2)`. Use `⟨W, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`.

Assume the negation of the conclusion as `hnot`. Establish `ha0 : a ≠ 0` using `fun h => hnot (h ▸ V.zero_mem)`. Establish `hinvV : a⁻¹ ∈ V` using `(V.mem_or_inv_mem a).resolve_left hnot`. Establish `hnu : a⁻¹ ∈ V.nonunits`. Rewrite using `[ValuationSubring.mem_nonunits_iff]`.

Use `lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinvV) ?_` and prove the remaining obligations. Introduce `h1`. Apply `hnot` to reduce the goal to its premises. Rewrite `h1` using `[map_inv₀, inv_eq_one]`. Conclude with `(V.valuation_le_one_iff a).1 (le_of_eq h1)`.

Establish `hm : algebraMap Ω K a⁻¹ ∈ intA V e` using `const_mem V e _ hinvV`. Establish `hk : (⟨_, hm⟩ : intA V e) ∈ RingHom.ker (redA V e)`. Rewrite using `[hker]`. Introduce `r`. Use `show (e (algebraMap Ω K a⁻¹)).coeff r ∈ V.nonunits`.

Rewrite using `[coeff_const]`. Use `split_ifs`. Conclude with `hnu`. Conclude with `zero_mem_nonunits V`. Establish `h3 : W.valuation (algebraMap Ω K a⁻¹) < 1` using `hlt _ hk`.

Establish `h4` using `(W.valuation_le_one_iff _).2 ha`. Establish `h5 : W.valuation (algebraMap Ω K a) * W.valuation (algebraMap Ω K a⁻¹) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]`. Establish `h6 : W.valuation (algebraMap Ω K a) * W.valuation (algebraMap Ω K a⁻¹) ≤ 1 * W.valuation (algebraMap Ω K a⁻¹)` using `by gcongr`. Rewrite `h6` using `[h5, one_mul]`.

Conclude with `absurd (lt_of_le_of_lt h6 h3) (lt_irrefl 1)`. Introduce `ha`. Conclude with `hA ⟨_, const_mem V e a ha⟩`. Introduce and unpack `P hP ⟨i0, hne, hi0, hi0'⟩`. Establish `hjA : j ∈ intA V e` using `(mem_intA V e j).2 hj3`.

Take `⟨P', hP'⟩ : ∃ P' : Polynomial V, P'.map V.subtype = P` from `(Polynomial.lifts_iff_coeff_lifts P).2 (fun n => ⟨⟨_, hP n⟩, rfl⟩)`. Set `ι : V →+* intA V e` to `((algebraMap Ω K).comp V.subtype).codRestrict (intA V e) (fun v => const_mem V e v v.2)`. Establish `hx : Polynomial.aeval j P = (intA V e).subtype (P'.eval₂ ι ⟨j, hjA⟩)`. Rewrite using `[Polynomial.hom_eval₂, ← hP', Polynomial.aeval_def, Polynomial.eval₂_map]`. Both sides reduce to the same expression.

Rewrite using `[hx]`. Apply `hone` to reduce the goal to its premises. Introduce `hk`. Rewrite `hk` using `[RingHom.mem_ker, Polynomial.hom_eval₂]`. Establish `hc : (redA V e).comp ι = (algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))).comp (IsLocalRing.residue V)`.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `redA_const V e v`. Rewrite `hk` using `[hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]`. Use `set J := redA V e ⟨j, hjA⟩ with hJdef`.

Establish `hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ)`. Apply `HahnSeries.orderTop_eq_of_le` to reduce the goal to its premises. Rewrite using `[HahnSeries.mem_support, hJdef, redA_coeff]`. Establish `h1 : (⟨(e j).coeff (-1), (mem_intA V e j).1 hjA (-1)⟩ : V) = 1` using `Subtype.ext hj1`. Rewrite using `[h1, map_one]`.

Conclude with `one_ne_zero`. Introduce `g hg`. Rewrite `hg` using `[HahnSeries.mem_support, hJdef, redA_coeff]`. Assume the negation of the conclusion as `hlt'`. Apply `hg` to reduce the goal to its premises.

Establish `h0 : (⟨(e j).coeff g, (mem_intA V e j).1 hjA g⟩ : V) = 0` using `Subtype.ext (hj2 g (lt_of_not_ge hlt'))`. Rewrite using `[h0, map_zero]`. Establish `hQ : P'.map (IsLocalRing.residue V) ≠ 0`. Introduce `h0`. Establish `hc0` using `congrArg (fun Q => Q.coeff i0) h0`.

Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc0`. Establish `hPi : ((P'.coeff i0 : V) : Ω) = P.coeff i0`. Rewrite using `[← hP', Polynomial.coeff_map]`. Both sides reduce to the same expression. Establish `hu : IsUnit (P'.coeff i0)`.

Use `isUnit_iff_exists_inv.2 ⟨⟨(P.coeff i0)⁻¹, hi0'⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show ((P'.coeff i0 : V) : Ω) * (P.coeff i0)⁻¹ = 1`. Rewrite using `[hPi, mul_inv_cancel₀ hne]`. Rewrite `hc0` using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]`. Conclude with `hc0 hu`.

Establish `hot` using `orderTop_aeval J hJ _ _ hQ rfl`. Rewrite `hot` using `[hk, HahnSeries.orderTop_zero]`. Conclude with `WithTop.top_ne_coe hot`. Introduce `f hf hf0`. Establish `hm : f - algebraMap Ω K ((e f).coeff 0) ∈ intA V e` using `sub_mem ((mem_intA V e f).2 hf) (const_mem V e _ (hf 0))`.

Apply `hlt ⟨_, hm⟩` to reduce the goal to its premises. Rewrite using `[hker]`. Introduce `r`. Use `show (e (f - algebraMap Ω K ((e f).coeff 0))).coeff r ∈ V.nonunits`. Rewrite using `[map_sub, HahnSeries.coeff_sub, coeff_const]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[sub_self]`. Conclude with `zero_mem_nonunits V`. Rewrite using `[sub_zero]`.

Conclude with `hf0 r h`.
-/
theorem exists_dom (j : K) (hj1 : (e j).coeff (-1) = 1) (hj2 : ∀ r : ℚ, r < -1 → (e j).coeff r = 0)
    (hj3 : ∀ r, (e j).coeff r ∈ V) :
    ∃ W : ValuationSubring K, (∀ a : Ω, algebraMap Ω K a ∈ W ↔ a ∈ V) ∧
      (∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) →
        W.valuation (Polynomial.aeval j P) = 1) ∧
      ∀ f : K, (∀ r, (e f).coeff r ∈ V) → (∀ r, r ≠ 0 → (e f).coeff r ∈ V.nonunits) →
        W.valuation (f - algebraMap Ω K ((e f).coeff 0)) < 1 := by
  classical
  haveI : (RingHom.ker (redA V e)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hA, hinv, hlt⟩ :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd.exists_val_of_prime (intA V e) (RingHom.ker (redA V e))
  have hker : ∀ x : intA V e, x ∈ RingHom.ker (redA V e) ↔ ∀ r, (e x).coeff r ∈ V.nonunits :=
    fun x => (RingHom.mem_ker).trans (redA_eq_zero V e x)
  have hone : ∀ x : intA V e, x ∉ RingHom.ker (redA V e) → W.valuation (x : K) = 1 := by
    intro x hx
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      apply hx
      have : x = 0 := Subtype.ext h0
      rw [this]
      exact Ideal.zero_mem _
    have h1 := (W.valuation_le_one_iff _).2 (hA x)
    have h2 := (W.valuation_le_one_iff _).2 (hinv x hx)
    rw [map_inv₀] at h2
    have hv0 : W.valuation (x : K) ≠ 0 := by simpa using hx0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro ha
      by_contra hnot
      have ha0 : a ≠ 0 := fun h => hnot (h ▸ V.zero_mem)
      have hinvV : a⁻¹ ∈ V := (V.mem_or_inv_mem a).resolve_left hnot
      have hnu : a⁻¹ ∈ V.nonunits := by
        rw [ValuationSubring.mem_nonunits_iff]
        refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinvV) ?_
        intro h1
        apply hnot
        rw [map_inv₀, inv_eq_one] at h1
        exact (V.valuation_le_one_iff a).1 (le_of_eq h1)
      have hm : algebraMap Ω K a⁻¹ ∈ intA V e := const_mem V e _ hinvV
      have hk : (⟨_, hm⟩ : intA V e) ∈ RingHom.ker (redA V e) := by
        rw [hker]
        intro r
        show (e (algebraMap Ω K a⁻¹)).coeff r ∈ V.nonunits
        rw [coeff_const]
        split_ifs
        · exact hnu
        · exact zero_mem_nonunits V
      have h3 : W.valuation (algebraMap Ω K a⁻¹) < 1 := hlt _ hk
      have h4 := (W.valuation_le_one_iff _).2 ha
      have h5 : W.valuation (algebraMap Ω K a) * W.valuation (algebraMap Ω K a⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
      have h6 : W.valuation (algebraMap Ω K a) * W.valuation (algebraMap Ω K a⁻¹) ≤
          1 * W.valuation (algebraMap Ω K a⁻¹) := by gcongr
      rw [h5, one_mul] at h6
      exact absurd (lt_of_le_of_lt h6 h3) (lt_irrefl 1)
    · intro ha
      exact hA ⟨_, const_mem V e a ha⟩
  · rintro P hP ⟨i0, hne, hi0, hi0'⟩
    have hjA : j ∈ intA V e := (mem_intA V e j).2 hj3
    obtain ⟨P', hP'⟩ : ∃ P' : Polynomial V, P'.map V.subtype = P :=
      (Polynomial.lifts_iff_coeff_lifts P).2 (fun n => ⟨⟨_, hP n⟩, rfl⟩)
    let ι : V →+* intA V e :=
      ((algebraMap Ω K).comp V.subtype).codRestrict (intA V e) (fun v => const_mem V e v v.2)
    have hx : Polynomial.aeval j P = (intA V e).subtype (P'.eval₂ ι ⟨j, hjA⟩) := by
      rw [Polynomial.hom_eval₂, ← hP', Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [hx]
    apply hone
    intro hk
    rw [RingHom.mem_ker, Polynomial.hom_eval₂] at hk
    have hc : (redA V e).comp ι =
        (algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))).comp
          (IsLocalRing.residue V) := by
      apply RingHom.ext
      intro v
      exact redA_const V e v
    rw [hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hk
    set J := redA V e ⟨j, hjA⟩ with hJdef
    have hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ) := by
      apply HahnSeries.orderTop_eq_of_le
      · rw [HahnSeries.mem_support, hJdef, redA_coeff]
        have h1 : (⟨(e j).coeff (-1), (mem_intA V e j).1 hjA (-1)⟩ : V) = 1 := Subtype.ext hj1
        rw [h1, map_one]
        exact one_ne_zero
      · intro g hg
        rw [HahnSeries.mem_support, hJdef, redA_coeff] at hg
        by_contra hlt'
        apply hg
        have h0 : (⟨(e j).coeff g, (mem_intA V e j).1 hjA g⟩ : V) = 0 :=
          Subtype.ext (hj2 g (lt_of_not_ge hlt'))
        rw [h0, map_zero]
    have hQ : P'.map (IsLocalRing.residue V) ≠ 0 := by
      intro h0
      have hc0 := congrArg (fun Q => Q.coeff i0) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc0
      have hPi : ((P'.coeff i0 : V) : Ω) = P.coeff i0 := by
        rw [← hP', Polynomial.coeff_map]
        rfl
      have hu : IsUnit (P'.coeff i0) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨(P.coeff i0)⁻¹, hi0'⟩, Subtype.ext ?_⟩
        show ((P'.coeff i0 : V) : Ω) * (P.coeff i0)⁻¹ = 1
        rw [hPi, mul_inv_cancel₀ hne]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at hc0
      exact hc0 hu
    have hot := orderTop_aeval J hJ _ _ hQ rfl
    rw [hk, HahnSeries.orderTop_zero] at hot
    exact WithTop.top_ne_coe hot
  · intro f hf hf0
    have hm : f - algebraMap Ω K ((e f).coeff 0) ∈ intA V e :=
      sub_mem ((mem_intA V e f).2 hf) (const_mem V e _ (hf 0))
    apply hlt ⟨_, hm⟩
    rw [hker]
    intro r
    show (e (f - algebraMap Ω K ((e f).coeff 0))).coeff r ∈ V.nonunits
    rw [map_sub, HahnSeries.coeff_sub, coeff_const]
    split_ifs with h
    · subst h
      rw [sub_self]
      exact zero_mem_nonunits V
    · rw [sub_zero]
      exact hf0 r h

end GlobalTheory.KZ.GaussDom

namespace GlobalTheory.KZ

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ _ q _ V _`. Take `⟨W, h1, h2, h3⟩` from `GaussDom.exists_dom V X.exp X.jK X.j_exp.1 X.j_exp.2.1 (fun r => by`. Take `⟨n, hn⟩` from `X.j_exp.2.2 r`. Rewrite using `[hn]`. Conclude with `intCast_mem V n)`.

Conclude with `⟨W, h1, fun P hP ⟨i, ha, hb, hc⟩ => h2 P hP ⟨i, hb, ha, hc⟩, h3⟩`.
-/
theorem exists_valuationSubring_gauss : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∃ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval X.jK P) = 1) ∧ ∀ f : X.K, (∀ r, (X.exp f).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp f).coeff r ∈ V.nonunits) → W.valuation (f - algebraMap Ω X.K ((X.exp f).coeff 0)) < 1 := by
  intro Ω _ _ _ ε X _ _ q _ V _
  obtain ⟨W, h1, h2, h3⟩ := GaussDom.exists_dom V X.exp X.jK X.j_exp.1 X.j_exp.2.1 (fun r => by
    obtain ⟨n, hn⟩ := X.j_exp.2.2 r
    rw [hn]
    exact intCast_mem V n)
  exact ⟨W, h1, fun P hP ⟨i, ha, hb, hc⟩ => h2 P hP ⟨i, hb, ha, hc⟩, h3⟩

end GlobalTheory.KZ
