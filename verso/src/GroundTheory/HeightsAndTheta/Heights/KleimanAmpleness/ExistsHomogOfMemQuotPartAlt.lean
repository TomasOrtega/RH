import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)

noncomputable section

namespace CellLocEval

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Homog

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver S ι) a := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[C_apply]`. Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset hm)]`. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_C (r : S) : IsMultiHomog (C r : MRingOver S ι) 0 := by
  intro m hm k
  rw [C_apply] at hm
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  simp

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases. Conclude with `hp m h k`. Conclude with `hq m h k`.
-/
theorem isMultiHomog_add {p q : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

/- English proof (translation)
Introduce `m hm k` and use `hp m (support_smul hm) k`.
-/
theorem isMultiHomog_smul {p : MRingOver S ι} {a : K → ℕ} (s : S) (hp : IsMultiHomog p a) :
    IsMultiHomog (s • p) a :=
  fun m hm k => hp m (support_smul hm) k

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, h₁, m₂, h₂, rfl⟩` from `Finset.mem_add.mp (support_mul p q hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]`.
-/
theorem isMultiHomog_mul {p q : MRingOver S ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]

end Homog

section Eval

variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Simplify using `only [map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hX : ∏ p : Σ k, ι k, (X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, (X k : MvPolynomial K Ω) ^ d k`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, (X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg μ hμ k]`. Rewrite using `[mConeMapOver, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, MvPolynomial.algebraMap_apply, map_mul, map_prod, map_pow, hX]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMapOver_homog {g : MRingOver S ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMapOver S y g = C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : Σ k, ι k, (X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg μ hμ k]
  rw [mConeMapOver, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, MvPolynomial.algebraMap_apply, map_mul, map_prod, map_pow, hX]
  ring

/- English proof (translation)
Establish `h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMapOver S y).toRingHom = (aeval y : MRingOver S ι →ₐ[S] Ω).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[mConeMapOver, MvPolynomial.algebraMap_apply]`. Introduce `p`.

Simplify using `[mConeMapOver]`. Establish `h2` using `RingHom.congr_fun h f`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2`. Rewrite using `[← h2, show mConeMapOver S y f = 0 from (RingHom.mem_ker).mp hf, map_zero]`.
-/
theorem aeval_eq_zero_of_mem {f : MRingOver S ι} (hf : f ∈ mIdealOver S y) : aeval y f = 0 := by
  have h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMapOver S y).toRingHom =
      (aeval y : MRingOver S ι →ₐ[S] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapOver, MvPolynomial.algebraMap_apply]
    · intro p
      simp [mConeMapOver]
  have h2 := RingHom.congr_fun h f
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [← h2, show mConeMapOver S y f = 0 from (RingHom.mem_ker).mp hf, map_zero]

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `show g ∈ RingHom.ker (mConeMapOver S y)`. Rewrite using `[RingHom.mem_ker, mConeMapOver_homog y hg, h0, map_zero, zero_mul]`.
-/
theorem mk_eq_zero_of_aeval {g : MRingOver S ι} {d : K → ℕ} (hg : IsMultiHomog g d) (h0 : aeval y g = 0) :
    Ideal.Quotient.mk (mIdealOver S y) g = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  show g ∈ RingHom.ker (mConeMapOver S y)
  rw [RingHom.mem_ker, mConeMapOver_homog y hg, h0, map_zero, zero_mul]

def ev0 : (MRingOver S ι ⧸ mIdealOver S y) →ₐ[S] Ω :=
  Ideal.Quotient.liftₐ (mIdealOver S y) (aeval y) (fun _ hf => aeval_eq_zero_of_mem y hf)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalAtPoint_mk (p : MRingOver S ι) : ev0 y (Ideal.Quotient.mk (mIdealOver S y) p) = aeval y p := rfl

/- English proof (translation)
Take `⟨m, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Use `show ev0 y (Ideal.Quotient.mk _ (r * m)) = _`. Rewrite using `[evalAtPoint_mk, evalAtPoint_mk, map_mul]`.
-/
theorem evalAtPoint_smul (r : MRingOver S ι) (m : MRingOver S ι ⧸ mIdealOver S y) :
    ev0 y (r • m) = aeval y r * ev0 y m := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  show ev0 y (Ideal.Quotient.mk _ (r * m)) = _
  rw [evalAtPoint_mk, evalAtPoint_mk, map_mul]

variable {y}

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon at ht`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨k, i, hi, rfl⟩` from `hx`. Rewrite using `[aeval_X]`.

Conclude with `hI k i hi`. Consider the case `one => simp`. Consider the case `mul x z _ _ hx hz => rw [map_mul]`. Conclude with `mul_ne_zero hx hz`.
-/
theorem aeval_ne_zero_of_mem {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) {t : MRingOver S ι}
    (ht : t ∈ cellMon S I) : aeval y t ≠ 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x z _ _ hx hz => rw [map_mul]; exact mul_ne_zero hx hz

variable (y)

def ev (I : ∀ k, Finset (ι k)) (hI : CellMeets y I)
    (x : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) : Ω :=
  LocalizedModule.liftOn x (fun p => ev0 y p.1 / aeval y (p.2 : MRingOver S ι)) (by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨u, hu⟩
    simp only [Submonoid.smul_def] at hu
    have h := congrArg (ev0 y) hu
    rw [evalAtPoint_smul, evalAtPoint_smul, evalAtPoint_smul, evalAtPoint_smul] at h
    have hu0 := aeval_ne_zero_of_mem hI u.2
    have hs0 := aeval_ne_zero_of_mem hI s.2
    have ht0 := aeval_ne_zero_of_mem hI t.2
    dsimp only
    rw [div_eq_div_iff hs0 ht0]
    have h' := mul_left_cancel₀ hu0 h
    linear_combination h')

/- English proof (translation)
The claim follows from `LocalizedModule.liftOn_mk _ _ _`.
-/
theorem ev_mk (I : ∀ k, Finset (ι k)) (hI : CellMeets y I) (m : MRingOver S ι ⧸ mIdealOver S y)
    (s : cellMon S I) : ev y I hI (LocalizedModule.mk m s) = ev0 y m / aeval y (s : MRingOver S ι) :=
  LocalizedModule.liftOn_mk _ _ _

def evLin (I : ∀ k, Finset (ι k)) (hI : CellMeets y I) :
    LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y) →ₗ[S] Ω where
  toFun := ev y I hI
  map_add' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction x' using LocalizedModule.induction_on with
      | h m' s' =>
        have hs0 := aeval_ne_zero_of_mem hI s.2
        have hs0' := aeval_ne_zero_of_mem hI s'.2
        rw [LocalizedModule.mk_add_mk, ev_mk, ev_mk, ev_mk]
        simp only [Submonoid.smul_def, map_add, evalAtPoint_smul, Submonoid.coe_mul, map_mul]
        field_simp
  map_smul' s x := by
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [LocalizedModule.smul'_mk, ev_mk, ev_mk, map_smul, smul_div_assoc, RingHom.id_apply]

open Classical in

def evMap (I : ∀ k, Finset (ι k)) :
    LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y) →ₗ[S] Ω :=
  if h : CellMeets y I then evLin y I h else 0

/- English proof (translation)
Unfold `evMap`. Rewrite using `[dif_pos hI]`. Conclude with `ev_mk y I hI _ t`.
-/
theorem evMap_mk' {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (m : MRingOver S ι ⧸ mIdealOver S y)
    (t : cellMon S I) :
    evMap y I (LocalizedModule.mk m t) = ev0 y m / aeval y (t : MRingOver S ι) := by
  unfold evMap
  rw [dif_pos hI]
  exact ev_mk y I hI _ t

/- English proof (translation)
The claim follows from `evMap_mk' y hI _ t`.
-/
theorem evMap_mk {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (g : MRingOver S ι) (t : cellMon S I) :
    evMap y I (LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) g) t) =
      aeval y g / aeval y (t : MRingOver S ι) :=
  evMap_mk' y hI _ t

/- English proof (translation)
Unfold `evMap`. Rewrite using `[dif_neg hI]`. Both sides reduce to the same expression.
-/
theorem evMap_of_not {I : ∀ k, Finset (ι k)} (hI : ¬ CellMeets y I)
    (x : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) : evMap y I x = 0 := by
  unfold evMap
  rw [dif_neg hI]
  rfl

end Eval

section Rep

variable {V : Ideal (MRingOver S ι)}

/- English proof (translation)
Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, ⟨hnn, hp⟩, rfl⟩` from `hx`. Conclude with `⟨p, hp, Or.inl hnn, rfl⟩`. Consider the case `zero => exact ⟨0, isMultiHomog_zero _, Or.inr rfl, map_zero _⟩`.

Consider the case `add x x' _ _ h h'`. Take `⟨g, hg, hd, rfl⟩` from `h`. Take `⟨g', hg', hd', rfl⟩` from `h'`. Use `⟨g + g', isMultiHomog_add hg hg', ?_, map_add _ _ _⟩` and prove the remaining obligations. Break down `hd with hd | rfl` into its components or cases.

Conclude with `Or.inl hd`. Break down `hd' with hd' | rfl` into its components or cases. Conclude with `Or.inl hd'`. Conclude with `Or.inr (add_zero 0)`. Consider the case `smul s x _ h`.

Take `⟨g, hg, hd, rfl⟩` from `h`. Use `⟨s • g, isMultiHomog_smul s hg, ?_, ?_⟩` and prove the remaining obligations. Break down `hd with hd | rfl` into its components or cases. Conclude with `Or.inl hd`. Conclude with `Or.inr (smul_zero s)`.

Rewrite using `[← Ideal.Quotient.mkₐ_eq_mk S, map_smul]`.
-/
theorem exists_homog_of_mem_quotPart {d : K → ℤ} {m : MRingOver S ι ⧸ V} (hm : m ∈ quotPart S V d) :
    ∃ g : MRingOver S ι, IsMultiHomog g (fun k => (d k).toNat) ∧ ((∀ k, 0 ≤ d k) ∨ g = 0) ∧
      Ideal.Quotient.mk V g = m := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, ⟨hnn, hp⟩, rfl⟩ := hx
    exact ⟨p, hp, Or.inl hnn, rfl⟩
  | zero => exact ⟨0, isMultiHomog_zero _, Or.inr rfl, map_zero _⟩
  | add x x' _ _ h h' =>
    obtain ⟨g, hg, hd, rfl⟩ := h
    obtain ⟨g', hg', hd', rfl⟩ := h'
    refine ⟨g + g', isMultiHomog_add hg hg', ?_, map_add _ _ _⟩
    rcases hd with hd | rfl
    · exact Or.inl hd
    · rcases hd' with hd' | rfl
      · exact Or.inl hd'
      · exact Or.inr (add_zero 0)
  | smul s x _ h =>
    obtain ⟨g, hg, hd, rfl⟩ := h
    refine ⟨s • g, isMultiHomog_smul s hg, ?_, ?_⟩
    · rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr (smul_zero s)
    · rw [← Ideal.Quotient.mkₐ_eq_mk S, map_smul]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, t, a, ht, hm, rfl⟩` from `hx`. Take `⟨g, hg, hd, rfl⟩` from `exists_homog_of_mem_quotPart hm`. Conclude with `⟨g, t, a, ht, hg, hd, rfl⟩`.

Consider the case `zero`. Use `⟨0, 1, 0, ?_, isMultiHomog_zero _, Or.inr rfl, ?_⟩` and prove the remaining obligations. Simplify using `using isMultiHomog_C (S := S) (ι := ι) 1`. Rewrite using `[map_zero, LocalizedModule.zero_mk]`. Consider the case `add x x' _ _ h h'`.

Take `⟨g, t, a, ht, hg, hd, rfl⟩` from `h`. Take `⟨g', t', a', ht', hg', hd', rfl⟩` from `h'`. Break down `hd with hd | rfl` into its components or cases. Use `swap`. Conclude with `⟨g', t', a', ht', hg', hd', by rw [map_zero, LocalizedModule.zero_mk, zero_add]⟩`.

Break down `hd' with hd' | rfl` into its components or cases. Use `swap`. Conclude with `⟨g, t, a, ht, hg, Or.inl hd, by rw [map_zero, LocalizedModule.zero_mk, add_zero]⟩`. Use `⟨(t' : MRingOver S ι) * g + (t : MRingOver S ι) * g', t * t', a + a', ?_, ?_, Or.inl ?_, ?_⟩` and prove the remaining obligations. Simplify using `using isMultiHomog_mul ht ht'`.

Establish `e1 : (fun k => (γ k + ((a + a') k : ℕ)).toNat) = a' + (fun k => (γ k + a k).toNat)`. Use function extensionality and compare the values at `k`. Use `hd k` as an intermediate fact. Simplify using `only [Pi.add_apply, Nat.cast_add]`. Use linear arithmetic over natural numbers and integers.

Establish `e2 : (fun k => (γ k + ((a + a') k : ℕ)).toNat) = a + (fun k => (γ k + a' k).toNat)`. Use function extensionality and compare the values at `k`. Use `hd' k` as an intermediate fact. Simplify using `only [Pi.add_apply, Nat.cast_add]`. Use linear arithmetic over natural numbers and integers.

Use `isMultiHomog_add ?_ ?_` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `isMultiHomog_mul ht' hg`. Rewrite using `[e2]`. Conclude with `isMultiHomog_mul ht hg'`.

Introduce `k`. Use `hd k` as an intermediate fact. Simplify using `only [Pi.add_apply, Nat.cast_add]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[LocalizedModule.mk_add_mk]`.

Use `congr 1`. Consider the case `smul s x _ h`. Take `⟨g, t, a, ht, hg, hd, rfl⟩` from `h`. Use `⟨s • g, t, a, ht, isMultiHomog_smul s hg, ?_, ?_⟩` and prove the remaining obligations. Break down `hd with hd | rfl` into its components or cases.

Conclude with `Or.inl hd`. Conclude with `Or.inr (smul_zero s)`. Rewrite using `[LocalizedModule.smul'_mk, ← Ideal.Quotient.mkₐ_eq_mk S, map_smul]`.
-/
theorem exists_rep {T : Submonoid (MRingOver S ι)} {γ : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ locPart ι (quotPart S V) T γ) :
    ∃ (g : MRingOver S ι) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ ((∀ k, 0 ≤ γ k + a k) ∨ g = 0) ∧
      x = LocalizedModule.mk (Ideal.Quotient.mk V g) t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨g, hg, hd, rfl⟩ := exists_homog_of_mem_quotPart hm
    exact ⟨g, t, a, ht, hg, hd, rfl⟩
  | zero =>
    refine ⟨0, 1, 0, ?_, isMultiHomog_zero _, Or.inr rfl, ?_⟩
    · simpa using isMultiHomog_C (S := S) (ι := ι) 1
    · rw [map_zero, LocalizedModule.zero_mk]
  | add x x' _ _ h h' =>
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := h
    obtain ⟨g', t', a', ht', hg', hd', rfl⟩ := h'
    rcases hd with hd | rfl
    swap
    · exact ⟨g', t', a', ht', hg', hd', by rw [map_zero, LocalizedModule.zero_mk, zero_add]⟩
    rcases hd' with hd' | rfl
    swap
    · exact ⟨g, t, a, ht, hg, Or.inl hd, by rw [map_zero, LocalizedModule.zero_mk, add_zero]⟩
    refine ⟨(t' : MRingOver S ι) * g + (t : MRingOver S ι) * g', t * t', a + a', ?_, ?_, Or.inl ?_, ?_⟩
    · simpa using isMultiHomog_mul ht ht'
    · have e1 : (fun k => (γ k + ((a + a') k : ℕ)).toNat) = a' + (fun k => (γ k + a k).toNat) := by
        funext k
        have := hd k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      have e2 : (fun k => (γ k + ((a + a') k : ℕ)).toNat) = a + (fun k => (γ k + a' k).toNat) := by
        funext k
        have := hd' k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      refine isMultiHomog_add ?_ ?_
      · rw [e1]; exact isMultiHomog_mul ht' hg
      · rw [e2]; exact isMultiHomog_mul ht hg'
    · intro k
      have := hd k
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · rw [LocalizedModule.mk_add_mk]
      congr 1
  | smul s x _ h =>
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := h
    refine ⟨s • g, t, a, ht, isMultiHomog_smul s hg, ?_, ?_⟩
    · rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr (smul_zero s)
    · rw [LocalizedModule.smul'_mk, ← Ideal.Quotient.mkₐ_eq_mk S, map_smul]

end Rep

section Parts

variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

/- English proof (translation)
Introduce `x hx x' hx' hxx'`. Rewrite using `[← sub_eq_zero]`. Establish `hs : x - x' ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ` using `sub_mem hx hx'`. Establish `h0 : evMap y I (x - x') = 0` using `by rw [map_sub, hxx', sub_self]`. Take `⟨g, t, a, -, hg, -, he⟩` from `exists_rep hs`.

Rewrite `h0`, the goal using `[he]`. Rewrite `h0` using `[evMap_mk y hI, div_eq_zero_iff]`. Break down `h0 with h0 | h0` into its components or cases. Rewrite using `[mk_eq_zero_of_aeval y hg h0, LocalizedModule.zero_mk]`. Conclude with `absurd h0 (aeval_ne_zero_of_mem hI t.2)`.
-/
theorem evMap_injOn {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (γ : K → ℤ) :
    Set.InjOn (evMap (S := S) y I) (locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ) := by
  intro x hx x' hx' hxx'
  rw [← sub_eq_zero]
  have hs : x - x' ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ := sub_mem hx hx'
  have h0 : evMap y I (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  obtain ⟨g, t, a, -, hg, -, he⟩ := exists_rep hs
  rw [he] at h0 ⊢
  rw [evMap_mk y hI, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · rw [mk_eq_zero_of_aeval y hg h0, LocalizedModule.zero_mk]
  · exact absurd h0 (aeval_ne_zero_of_mem hI t.2)

/- English proof (translation)
Unfold `cellSec`. Rewrite using `[if_pos hI]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `x hx`.

Take `⟨g, t, a, ht, hg, hd, rfl⟩` from `exists_rep hx`. Rewrite using `[Submodule.mem_comap, evMap_mk y hI]`. Break down `hd with hd | rfl` into its components or cases. Conclude with `Submodule.subset_span ⟨g, t, a, t.2, ht, hd, hg, rfl⟩`. Rewrite using `[map_zero, zero_div]`.

Conclude with `Submodule.zero_mem _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `z ⟨g, t, a, ht, ht', hnn, hg, rfl⟩`. Use `⟨LocalizedModule.mk (Ideal.Quotient.mk _ g) ⟨t, ht⟩, Submodule.subset_span ⟨Ideal.Quotient.mk _ g, ⟨t, ht⟩, a, ht', ?_, rfl⟩, evMap_mk y hI g ⟨t, ht⟩⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨g, ⟨hnn, hg⟩, rfl⟩`.
-/
theorem map_evMap_locPart {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (γ : K → ℤ) :
    (locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ).map (evMap y I) = cellSec S y γ I := by
  unfold cellSec
  rw [if_pos hI]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := exists_rep hx
    rw [Submodule.mem_comap, evMap_mk y hI]
    rcases hd with hd | rfl
    · exact Submodule.subset_span ⟨g, t, a, t.2, ht, hd, hg, rfl⟩
    · rw [map_zero, zero_div]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro z ⟨g, t, a, ht, ht', hnn, hg, rfl⟩
    refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ g) ⟨t, ht⟩,
      Submodule.subset_span ⟨Ideal.Quotient.mk _ g, ⟨t, ht⟩, a, ht', ?_, rfl⟩, evMap_mk y hI g ⟨t, ht⟩⟩
    exact Submodule.subset_span ⟨g, ⟨hnn, hg⟩, rfl⟩

/- English proof (translation)
Unfold `CellMeets at hI`. Use `push Not at hI`. Take `⟨k, i, hi, hy⟩` from `hI`. Establish `hX : (X ⟨k, i⟩ : MRingOver S ι) ∈ cellMon S I` using `Submonoid.subset_closure ⟨k, i, hi, rfl⟩`. Establish `hmem : (X ⟨k, i⟩ : MRingOver S ι) ∈ mIdealOver S y`.

Simplify using `[mIdealOver, mConeMapOver, RingHom.mem_ker, hy]`. Establish `hz : ∀ w : MRingOver S ι ⧸ mIdealOver S y, (X ⟨k, i⟩ : MRingOver S ι) • w = 0`. Introduce `w`. Take `⟨g, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hmem`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using LocalizedModule.induction_on with`. Consider the case `h m t`. Proceed by induction on `b using LocalizedModule.induction_on with`.

Consider the case `h m' t'`. Rewrite using `[LocalizedModule.mk_eq]`. Use `⟨⟨_, hX⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.smul_def]`. Rewrite using `[hz, hz]`.
-/
theorem subsingleton_of_not {I : ∀ k, Finset (ι k)} (hI : ¬ CellMeets y I) :
    Subsingleton (LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) := by
  unfold CellMeets at hI
  push Not at hI
  obtain ⟨k, i, hi, hy⟩ := hI
  have hX : (X ⟨k, i⟩ : MRingOver S ι) ∈ cellMon S I := Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hmem : (X ⟨k, i⟩ : MRingOver S ι) ∈ mIdealOver S y := by
    simp [mIdealOver, mConeMapOver, RingHom.mem_ker, hy]
  have hz : ∀ w : MRingOver S ι ⧸ mIdealOver S y, (X ⟨k, i⟩ : MRingOver S ι) • w = 0 := by
    intro w
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hmem
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m t =>
    induction b using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨_, hX⟩, ?_⟩
      simp only [Submonoid.smul_def]
      rw [hz, hz]

end Parts

section Res

/- English proof (translation)
Apply `Submonoid.closure_mono` to reduce the goal to its premises. Introduce and unpack `f ⟨k, i, hi, rfl⟩`. Conclude with `⟨k, i, h k hi, rfl⟩`.
-/
theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

/- English proof (translation)
Unfold `cellRes`. Rewrite using `[dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']`.
-/
theorem cellRes_mk {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

variable {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Distinguish the cases in `h : cellMon S J ≤ cellMon S I`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m t => rw [LocalizedModule.smul'_mk, cellRes_mk h, cellRes_mk h, LocalizedModule.smul'_mk]`. Unfold `cellRes`. Rewrite using `[dif_neg h]`.

Simplify using the standard rewrite rules.
-/
theorem cellRes_smul {J I : ∀ k, Finset (ι k)} (s : S)
    (x : LocalizedModule (cellMon S J) (MRingOver S ι ⧸ mIdealOver S y)) :
    cellRes S _ J I (s • x) = s • cellRes S _ J I x := by
  by_cases h : cellMon S J ≤ cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t => rw [LocalizedModule.smul'_mk, cellRes_mk h, cellRes_mk h,
        LocalizedModule.smul'_mk]
  · unfold cellRes
    rw [dif_neg h]
    simp

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, t, a, ht, hm, rfl⟩` from `hx`. Rewrite using `[cellRes_mk h]`. Conclude with `Submodule.subset_span ⟨m, ⟨t.1, h t.2⟩, a, ht, hm, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x₁ x₂ _ _ h₁ h₂ => rw [map_add]`. Conclude with `add_mem h₁ h₂`. Consider the case `smul s x _ h' => rw [cellRes_smul]`.

Conclude with `Submodule.smul_mem _ s h'`.
-/
theorem cellRes_mem_locPart {J I : ∀ k, Finset (ι k)} (h : cellMon S J ≤ cellMon S I) (γ : K → ℤ)
    {x : LocalizedModule (cellMon S J) (MRingOver S ι ⧸ mIdealOver S y)}
    (hx : x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S J) γ) :
    cellRes S _ J I x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [cellRes_mk h]
    exact Submodule.subset_span ⟨m, ⟨t.1, h t.2⟩, a, ht, hm, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul s x _ h' => rw [cellRes_smul]; exact Submodule.smul_mem _ s h'

/- English proof (translation)
Establish `hJ : CellMeets y J` using `fun k i hi => hI k i (hJI k hi)`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m t`. Rewrite using `[cellRes_mk (cellMon_mono hJI), evMap_mk' y hI, evMap_mk' y hJ]`.
-/
theorem evMap_cellRes {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (hI : CellMeets y I)
    (x : LocalizedModule (cellMon S J) (MRingOver S ι ⧸ mIdealOver S y)) :
    evMap y I (cellRes S _ J I x) = evMap y J x := by
  have hJ : CellMeets y J := fun k i hi => hI k i (hJI k hi)
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [cellRes_mk (cellMon_mono hJI), evMap_mk' y hI, evMap_mk' y hJ]

end Res

end CellLocEval

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
