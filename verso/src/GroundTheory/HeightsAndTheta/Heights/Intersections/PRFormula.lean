import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

set_option linter.unusedSectionVars false

namespace DiagRAux

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hev` using `hγ.choose_spec.2`. Establish `hy : hγ.choose y ∈ mcPts P` using `hev.self_of_nhds.2.1`. Rewrite using `[hg _ hy]`.

Use `congr 1`. Apply `maDensity_congr_of_eventuallyEq` to reduce the goal to its premises. Introduce `j`. Use `filter_upwards [hev] with y' hy' using hφ j _ hy'.2.1`. Both sides reduce to the same expression.
-/
theorem sheetDensity_congr_mcPts (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z)
    (hg : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hev := hγ.choose_spec.2
    have hy : hγ.choose y ∈ mcPts P := hev.self_of_nhds.2.1
    rw [hg _ hy]
    congr 1
    apply maDensity_congr_of_eventuallyEq
    intro j
    filter_upwards [hev] with y' hy' using hφ j _ hy'.2.1
  · rfl

/- English proof (translation)
Unfold `ptsIntegral ptsIntegralAt`. Use `split_ifs with hΨ`. Simplify using `only [sheetDensity_congr_mcPts P _ hφ hg]`. Both sides reduce to the same expression.
-/
theorem ptsIntegral_congr_mcPts (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z)
    (hg : ∀ z ∈ mcPts P, g z = g' z) : ptsIntegral P φ g = ptsIntegral P φ' g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · simp only [sheetDensity_congr_mcPts P _ hφ hg]
  · rfl

/- English proof (translation)
Unfold `ptsIntegral ptsIntegralAt sheetDensity`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ptsIntegral_zero (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun _ => 0) = 0 := by
  unfold ptsIntegral ptsIntegralAt sheetDensity
  split_ifs <;> simp

/- English proof (translation)
Establish `hhom : IsMultiHomog (1 : MRing ι) 0`. Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.support_one, Finset.mem_singleton]`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.

Establish `hnot : (1 : MRing ι) ∉ P` using `fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)`. Rewrite using `[hI.2.2 P n L A 1 0 hP hL hA (fun k => by simp [ha]) hhom hnot]`. Establish `hsupp : divSupp P (1 : MRing ι) = ∅`. Use extensionality with `W`. Use `⟨fun hW => ?_, fun h => h.elim⟩` and prove the remaining obligations.

Establish `h1 : P ⊔ Ideal.span {(1 : MRing ι)} = ⊤` using `by simp`. Establish `hp : W.IsPrime` using `hW.1.1.1`. Establish `hle : P ⊔ Ideal.span {(1 : MRing ι)} ≤ W` using `hW.1.1.2`. Rewrite `hle` using `[h1]`. Conclude with `hp.ne_top (top_le_iff.1 hle)`.

Unfold `recR arInt`. Simplify using `only [hsupp, finsum_mem_empty, zero_sub, neg_eq_zero]`. Rewrite using `[ptsIntegral_congr_mcPts P (φ' := fun j z => Real.log ((L j).h z)) (g' := fun _ => 0) (fun _ _ _ => rfl) (fun z hz => by simp [logNorm, h1 z hz])]`. Conclude with `ptsIntegral_zero P _`.
-/
theorem I_snoc_triv {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (ha : A.a = 0) (h1 : ∀ z ∈ mcPts P, A.h z = 1) :
    I P (n + 1) (Fin.snoc L A) = 0 := by
  have hhom : IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [hI.2.2 P n L A 1 0 hP hL hA (fun k => by simp [ha]) hhom hnot]
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    refine ⟨fun hW => ?_, fun h => h.elim⟩
    have h1 : P ⊔ Ideal.span {(1 : MRing ι)} = ⊤ := by simp
    have hp : W.IsPrime := hW.1.1.1
    have hle : P ⊔ Ideal.span {(1 : MRing ι)} ≤ W := hW.1.1.2
    rw [h1] at hle
    exact hp.ne_top (top_le_iff.1 hle)
  unfold recR arInt
  simp only [hsupp, finsum_mem_empty, zero_sub, neg_eq_zero]
  rw [ptsIntegral_congr_mcPts P (φ' := fun j z => Real.log ((L j).h z)) (g' := fun _ => 0)
    (fun _ _ _ => rfl) (fun z hz => by simp [logNorm, h1 z hz])]
  exact ptsIntegral_zero P _

end General

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def halfInvLine (A B : HermLine ι) (c : K → ℤ) (hc : ∀ k, 2 * c k = -(A.a k + B.a k)) : HermLine ι where
  a := c
  h z := |A.h z * B.h z| ^ (-(1 / 2 : ℝ))
  pos z hz := Real.rpow_pos_of_pos (abs_pos.2 (mul_pos (A.pos z hz) (B.pos z hz)).ne') _
  smul c' z hc' := by
    rw [A.smul c' z hc', B.smul c' z hc']
    have hp : ∀ k, 0 < ‖c' k‖ := fun k => norm_pos_iff.2 (hc' k)
    have e1 : (∏ k, ‖c' k‖ ^ A.a k) * A.h z * ((∏ k, ‖c' k‖ ^ B.a k) * B.h z) =
        (∏ k, ‖c' k‖ ^ (A.a k + B.a k)) * (A.h z * B.h z) := by
      rw [show (∏ k, ‖c' k‖ ^ (A.a k + B.a k)) = (∏ k, ‖c' k‖ ^ A.a k) * ∏ k, ‖c' k‖ ^ B.a k by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hp k).ne' _ _]
      ring
    have hpos : 0 < ∏ k, ‖c' k‖ ^ (A.a k + B.a k) := Finset.prod_pos fun k _ => zpow_pos (hp k) _
    rw [e1, abs_mul, abs_of_pos hpos, Real.mul_rpow hpos.le (abs_nonneg _)]
    congr 1
    rw [← Real.finsetProd_rpow _ _ (fun k _ => (zpow_pos (hp k) _).le)]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul (hp k).le, ← Real.rpow_intCast]
    congr 1
    have := hc k
    push_cast
    have h2 : ((c k : ℤ) : ℝ) * 2 = -((A.a k : ℝ) + B.a k) := by exact_mod_cast (by linarith)
    linarith

/- English proof (translation)
Simplify using `only [halfInvLine, abs_of_pos (mul_pos (A.pos z hz) (B.pos z hz))]`.
-/
theorem halfInvLine_h_of_pos (A B : HermLine ι) (c : K → ℤ) (hc : ∀ k, 2 * c k = -(A.a k + B.a k))
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (halfInvLine A B c hc).h z = (A.h z * B.h z) ^ (-(1 / 2 : ℝ)) := by
  simp only [halfInvLine, abs_of_pos (mul_pos (A.pos z hz) (B.pos z hz))]

/- English proof (translation)
Establish `hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A.h z * B.h z) ^ (-(1 / 2 : ℝ))) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `(hA.mul hB).rpow_const_of_ne fun z hz => (mul_pos (A.pos z hz) (B.pos z hz)).ne'`. Conclude with `hs.congr fun z hz => halfInvLine_h_of_pos A B c hc z hz`.
-/
theorem isSmoothHerm_halfInvLine {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (c : K → ℤ)
    (hc : ∀ k, 2 * c k = -(A.a k + B.a k)) : IsSmoothHerm (halfInvLine A B c hc) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A.h z * B.h z) ^ (-(1 / 2 : ℝ)))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA.mul hB).rpow_const_of_ne fun z hz => (mul_pos (A.pos z hz) (B.pos z hz)).ne'
  exact hs.congr fun z hz => halfInvLine_h_of_pos A B c hc z hz

/- English proof (translation)
The claim follows from `hA.mul hB`.
-/
theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

/- English proof (translation)
Establish `hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A.h z)⁻¹) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `hA.inv fun z hz => (A.pos z hz).ne'`. Use `hs.congr fun z _ => ?_` and prove the remaining obligations. Simplify using `[hermZpow]`.
-/
theorem isSmoothHerm_inv {A : HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (hermZpow A (-1)) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A.h z)⁻¹)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    hA.inv fun z hz => (A.pos z hz).ne'
  refine hs.congr fun z _ => ?_
  simp [hermZpow]

/- English proof (translation)
Simplify using `[hermZpow]`.
-/
theorem hermZpow_neg_one_h (A : HermLine ι) (z : (Σ k, ι k) → ℂ) : (hermZpow A (-1)).h z = (A.h z)⁻¹ := by
  simp [hermZpow]

/- English proof (translation)
Simplify using `[hermZpow]`.
-/
theorem hermZpow_neg_one_a (A : HermLine ι) : (hermZpow A (-1)).a = -A.a := by
  simp [hermZpow]

end Lines

section Cycles

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def cycTerm (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ} (L : Fin n → HermLine ι)
    (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

/- English proof (translation)
Unfold `cycR cycTerm`. Rewrite using `[finsum_mem_def]`. Use `finsum_congr fun W => ?_` and prove the remaining obligations. Distinguish the cases in `hW : W ∈ divSupp P s`. Simplify using `[divCycle, Finsupp.ofSupportFinite_coe, hW]`.

Simplify using `[divCycle, Finsupp.ofSupportFinite_coe, hW]`.
-/
theorem cycR_eq_finsum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = ∑ᶠ W, (divCycle P s W : ℝ) * cycTerm I L W := by
  classical
  unfold cycR cycTerm
  rw [finsum_mem_def]
  refine finsum_congr fun W => ?_
  by_cases hW : W ∈ divSupp P s
  · simp [divCycle, Finsupp.ofSupportFinite_coe, hW]
  · simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

/- English proof (translation)
Rewrite using `[cycR_eq_finsum, cycR_eq_finsum, ← finsum_sub_distrib]`. Establish `hW : ∀ W, (divCycle P f W : ℝ) - divCycle P g W = ((Finsupp.single W₀ (1 : ℤ) W : ℤ) : ℝ)`. Introduce `W`. Use `congrArg (fun z => z W) hdiv` as an intermediate fact. Simplify using `only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply] at this`.

Rewrite using `[← this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : ∀ W, (divCycle P f W : ℝ) * cycTerm I L W - divCycle P g W * cycTerm I L W = ((Finsupp.single W₀ (1 : ℤ) W : ℤ) : ℝ) * cycTerm I L W` using `fun W => by`. Rewrite using `[← hW W]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Rewrite using `[finsum_eq_single _ W₀ (fun W hW => by simp [Ne.symm hW])]`. Simplify using `[cycTerm, hW₀]`. Conclude with `(divCycle P f).hasFiniteSupport.subset fun W hW h0 => hW (by simp [h0])`.

Conclude with `(divCycle P g).hasFiniteSupport.subset fun W hW h0 => hW (by simp [h0])`.
-/
theorem cycR_sub_eq (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (f g : MRing ι) (W₀ : Ideal (MRing ι))
    (hdiv : T.toZCycle (divCycle P f) - T.toZCycle (divCycle P g) = Finsupp.single W₀ 1)
    (hW₀ : IsHorizontal W₀) : cycR I P L f - cycR I P L g = I W₀ n L := by
  rw [cycR_eq_finsum, cycR_eq_finsum, ← finsum_sub_distrib]
  · have hW : ∀ W, (divCycle P f W : ℝ) - divCycle P g W = ((Finsupp.single W₀ (1 : ℤ) W : ℤ) : ℝ) := by
      intro W
      have := congrArg (fun z => z W) hdiv
      simp only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply] at this
      rw [← this]
      push_cast
      ring
    have e : ∀ W, (divCycle P f W : ℝ) * cycTerm I L W - divCycle P g W * cycTerm I L W =
        ((Finsupp.single W₀ (1 : ℤ) W : ℤ) : ℝ) * cycTerm I L W := fun W => by
      rw [← hW W]; ring
    simp only [e]
    rw [finsum_eq_single _ W₀ (fun W hW => by simp [Ne.symm hW])]
    simp [cycTerm, hW₀]
  · exact (divCycle P f).hasFiniteSupport.subset fun W hW h0 => hW (by simp [h0])
  · exact (divCycle P g).hasFiniteSupport.subset fun W hW h0 => hW (by simp [h0])

/- English proof (translation)
Assume the negation of the conclusion as `hW`. Conclude with `h (by simp [divCycle, Finsupp.ofSupportFinite_coe, hW])`.
-/
theorem mem_divSupp_of_divCycle_ne_zero {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (h : divCycle P s W ≠ 0) : W ∈ divSupp P s := by
  classical
  by_contra hW
  exact h (by simp [divCycle, Finsupp.ofSupportFinite_coe, hW])

end Cycles

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

/- English proof (translation)
Use `conv_lhs => rw [s.as_sum]`. Use `conv_rhs => rw [s.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hX : (m.prod fun p e => (X p.1 : MvPolynomial K Φ) ^ e) = ∏ k, X k ^ β k`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ y, (X k : MvPolynomial K Φ) ^ m ⟨k, y⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hs m hm k]`. Simplify using `only [T.multiConeMap, coe_eval₂Hom, eval₂_monomial, aeval_monomial, mul_pow, Finsupp.prod_mul, ← hX, map_mul, eq_intCast, algebraMap_int_eq, map_intCast]`.

Rewrite using `[show (m.prod fun p e => (C (c p) : MvPolynomial K Φ) ^ e) = C (m.prod fun p e => c p ^ e) by`. Simplify using `[Finsupp.prod, map_prod, map_pow]]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem multiConeMap_of_homog (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    T.multiConeMap c s = C (aeval c s) * ∏ k, X k ^ β k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : (m.prod fun p e => (X p.1 : MvPolynomial K Φ) ^ e) = ∏ k, X k ^ β k := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, (X k : MvPolynomial K Φ) ^ m ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  simp only [T.multiConeMap, coe_eval₂Hom, eval₂_monomial, aeval_monomial, mul_pow, Finsupp.prod_mul,
    ← hX, map_mul, eq_intCast, algebraMap_int_eq, map_intCast]
  rw [show (m.prod fun p e => (C (c p) : MvPolynomial K Φ) ^ e) = C (m.prod fun p e => c p ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  ring

/- English proof (translation)
Rewrite using `[RingHom.mem_ker, multiConeMap_of_homog c s β hs, not_iff_not]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hm : (∏ k, (X k : MvPolynomial K Φ) ^ β k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)`. Conclude with `C_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hm)`.

Introduce `h`. Simplify using `[h]`.
-/
theorem not_mem_ker_iff_aeval_ne (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    s ∉ RingHom.ker (T.multiConeMap c) ↔ aeval c s ≠ 0 := by
  rw [RingHom.mem_ker, multiConeMap_of_homog c s β hs, not_iff_not]
  constructor
  · intro h
    have hm : (∏ k, (X k : MvPolynomial K Φ) ^ β k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact C_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hm)
  · intro h; simp [h]

end Cone

section Tuples

variable {α : Type*}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp]`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality. Rewrite using `[Equiv.swap_apply_left, ← Fin.castSucc_zero, Fin.snoc_last, Fin.snoc_castSucc, Fin.cons_zero]`.

Distinguish the cases in `hl : i = Fin.last (n + 1)`. Substitute `hl` using the available equality. Rewrite using `[Equiv.swap_apply_right, Fin.snoc_last, ← Fin.castSucc_zero, Fin.snoc_castSucc, Fin.cons_zero]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne h0 hl]`. Take `⟨i', rfl⟩` from `Fin.exists_castSucc_eq.2 hl`.

Establish `hi' : i' ≠ 0` using `fun h => h0 (by rw [h, Fin.castSucc_zero])`. Take `⟨j, rfl⟩` from `Fin.exists_succ_eq.2 hi'`. Rewrite using `[Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.cons_succ, Fin.cons_succ]`.
-/
theorem snoc_cons_comp_swap {n : ℕ} (A B : α) (L : Fin n → α) :
    (Fin.snoc (Fin.cons A L : Fin (n + 1) → α) B : Fin (n + 2) → α) ∘ Equiv.swap 0 (Fin.last (n + 1)) =
      Fin.snoc (Fin.cons B L : Fin (n + 1) → α) A := by
  funext i
  simp only [Function.comp]
  by_cases h0 : i = 0
  · subst h0
    rw [Equiv.swap_apply_left, ← Fin.castSucc_zero, Fin.snoc_last, Fin.snoc_castSucc, Fin.cons_zero]
  by_cases hl : i = Fin.last (n + 1)
  · subst hl
    rw [Equiv.swap_apply_right, Fin.snoc_last, ← Fin.castSucc_zero, Fin.snoc_castSucc, Fin.cons_zero]
  rw [Equiv.swap_apply_of_ne_of_ne h0 hl]
  obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hl
  have hi' : i' ≠ 0 := fun h => h0 (by rw [h, Fin.castSucc_zero])
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi'
  rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.cons_succ, Fin.cons_succ]

/- English proof (translation)
Establish `e : (![A, B] : Fin 2 → α) = Fin.snoc (![A] : Fin 1 → α) B`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[e, Fin.append_snoc, Fin.append_right_eq_snoc]`. Both sides reduce to the same expression.
-/
theorem append_pair_eq {n : ℕ} (L : Fin n → α) (A B : α) :
    (Fin.append L ![A, B] : Fin (n + 2) → α) = Fin.snoc (Fin.snoc L A : Fin (n + 1) → α) B := by
  have e : (![A, B] : Fin 2 → α) = Fin.snoc (![A] : Fin 1 → α) B := by
    funext i
    fin_cases i <;> rfl
  rw [e, Fin.append_snoc, Fin.append_right_eq_snoc]
  rfl

end Tuples

section Smooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `j`. Consider the cases of `j using Fin.cases with`. Consider the case `zero => simpa using hA`. Consider the case `succ i => simpa using hL i`.
-/
theorem smooth_cons {n : ℕ} {A : HermLine ι} {L : Fin n → HermLine ι} (hA : IsSmoothHerm A)
    (hL : ∀ j, IsSmoothHerm (L j)) : ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (n + 1) → HermLine ι) j) := by
  intro j
  cases j using Fin.cases with
  | zero => simpa using hA
  | succ i => simpa using hL i

/- English proof (translation)
Introduce `j`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last => simpa using hA`. Consider the case `cast i => simpa using hL i`.
-/
theorem smooth_snoc {n : ℕ} {A : HermLine ι} {L : Fin n → HermLine ι} (hA : IsSmoothHerm A)
    (hL : ∀ j, IsSmoothHerm (L j)) : ∀ j, IsSmoothHerm ((Fin.snoc L A : Fin (n + 1) → HermLine ι) j) := by
  intro j
  cases j using Fin.lastCases with
  | last => simpa using hA
  | cast i => simpa using hL i

end Smooth

section FibreSquare

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

/- English proof (translation)
Establish `hfun : X'.h = fun z => X.h (fun p => z (T.yyEmb j p))` using `funext hp.2`. Unfold `IsSmoothHerm`. Rewrite using `[hfun]`. Establish `hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, T.wwIdx ι ν κ k) → ℂ => fun p => z (T.yyEmb j p))` using `contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (T.yyEmb j p)`. Use `hX.comp hlin.contDiffOn ?_` and prove the remaining obligations.

Introduce `z hz k`. Apply the tactic sequence `fin_cases j <;> cases k`. Take `⟨i, hi⟩` from `hz .base`. Conclude with `⟨i, hi⟩`. Take `⟨i, hi⟩` from `hz .det`.

Conclude with `⟨i, hi⟩`. Take `⟨i, hi⟩` from `hz .line0; exact ⟨i, by simpa [T.yyEmb] using hi⟩`. Take `⟨i, hi⟩` from `hz .base`. Conclude with `⟨i, hi⟩`. Take `⟨i, hi⟩` from `hz .det`.

Conclude with `⟨i, hi⟩`. Take `⟨i, hi⟩` from `hz .line1; exact ⟨i, by simpa [T.yyEmb] using hi⟩`.
-/
theorem isSmoothHerm_pull (j : Fin 2) {X : HermLine (T.yyIdx ι ν κ)} {X' : HermLine (T.wwIdx ι ν κ)}
    (hX : IsSmoothHerm X) (hp : IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) X X') : IsSmoothHerm X' := by
  have hfun : X'.h = fun z => X.h (fun p => z (T.yyEmb j p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hfun]
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, T.wwIdx ι ν κ k) → ℂ => fun p => z (T.yyEmb j p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (T.yyEmb j p)
  refine hX.comp hlin.contDiffOn ?_
  intro z hz k
  fin_cases j <;> cases k
  · obtain ⟨i, hi⟩ := hz .base; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .det; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .line0; exact ⟨i, by simpa [T.yyEmb] using hi⟩
  · obtain ⟨i, hi⟩ := hz .base; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .det; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .line1; exact ⟨i, by simpa [T.yyEmb] using hi⟩

/- English proof (translation)
Rewrite using `[RingHom.comap_ker, RingHom.comap_ker, RingHom.ext_int ((T.multiConeMap c).comp C) ((T.multiConeMap c').comp C)]`.
-/
theorem comap_C_ker_multiConeMap {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c c' : (Σ k, ι k) → Φ) :
    (RingHom.ker (T.multiConeMap c)).comap (C : ℤ →+* MRing ι) =
      (RingHom.ker (T.multiConeMap c')).comap (C : ℤ →+* MRing ι) := by
  rw [RingHom.comap_ker, RingHom.comap_ker,
    RingHom.ext_int ((T.multiConeMap c).comp C) ((T.multiConeMap c').comp C)]

end FibreSquare

end DiagRAux

open DiagRAux

section Main

/- English proof (translation)
Introduce `I hI D S X X₀ X₁ L hXa hX hp0 hp1 hL`. Establish `hF : IsIntersectionFamily (I T.WBlk S.WIdx)` using `hI T.WBlk S.WIdx`. Establish `hW : IsArithVar S.WW (D + 2)` using `S.arithWW`. Establish `hWp : S.WW.IsPrime` using `hW.2.1.1`. Establish `hs0 : IsSmoothHerm X₀` using `isSmoothHerm_pull 0 hX hp0`.

Establish `hs1 : IsSmoothHerm X₁` using `isSmoothHerm_pull 1 hX hp1`. Establish `hdeg : ∀ k, 2 * T.llDeg k = -(X₀.a k + X₁.a k)`. Establish `a0 : ∀ k, X₀.a k = I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY k` using `fun k => by rw [hp0.1, hXa]`. Establish `a1 : ∀ k, X₁.a k = I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY k` using `fun k => by rw [hp1.1, hXa]`. Establish `p0b : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .base = 3` using `pullDeg_segreBlockEmbedding 0 T.twoXiDegY .base`.

Establish `p0d : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .det = -1` using `pullDeg_segreBlockEmbedding 0 T.twoXiDegY .det`. Establish `p0l0 : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .line0 = -2` using `pullDeg_segreBlockEmbedding 0 T.twoXiDegY .line`. Establish `p0l1 : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .line1 = 0` using `pullDeg_otherLine 0 T.twoXiDegY`. Establish `p1b : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .base = 3` using `pullDeg_segreBlockEmbedding 1 T.twoXiDegY .base`. Establish `p1d : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .det = -1` using `pullDeg_segreBlockEmbedding 1 T.twoXiDegY .det`.

Establish `p1l0 : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .line0 = 0` using `pullDeg_otherLine 1 T.twoXiDegY`. Establish `p1l1 : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .line1 = -2` using `pullDeg_segreBlockEmbedding 1 T.twoXiDegY .line`. Introduce `k`. Rewrite using `[a0, a1]`. Consider the cases of `k`.

Rewrite using `[p0b, p1b]`. Simplify using `[T.llDeg, T.unitDeg]`. Rewrite using `[p0d, p1d]`. Simplify using `[T.llDeg, T.unitDeg]`. Rewrite using `[p0l0, p1l0]`.

Simplify using `[T.llDeg, T.unitDeg]`. Rewrite using `[p0l1, p1l1]`. Simplify using `[T.llDeg, T.unitDeg]`. Use `set X₁i := hermZpow X₁ (-1) with hX₁i`. Use `set M := X₀.tensor X₁i with hM`.

Use `set Q := X₀.tensor X₁ with hQ`. Use `set LL := halfInvLine X₀ X₁ T.llDeg hdeg with hLL`. Establish `hs1i : IsSmoothHerm X₁i` using `isSmoothHerm_inv hs1`. Establish `hsM : IsSmoothHerm M` using `isSmoothHerm_tensor hs0 hs1i`. Establish `hsQ : IsSmoothHerm Q` using `isSmoothHerm_tensor hs0 hs1`.

Establish `hsLL : IsSmoothHerm LL` using `isSmoothHerm_halfInvLine hs0 hs1 _ hdeg`. Use `set T1 := X₁.tensor X₁i with hT1`. Use `set T2 := Q.tensor (LL.tensor LL) with hT2`. Establish `hsT1 : IsSmoothHerm T1` using `isSmoothHerm_tensor hs1 hs1i`. Establish `hsT2 : IsSmoothHerm T2` using `isSmoothHerm_tensor hsQ (isSmoothHerm_tensor hsLL hsLL)`.

Establish `aT1 : T1.a = 0`. Simplify using `only [hT1, HermLine.tensor, hX₁i, hermZpow_neg_one_a, add_neg_cancel]`. Establish `hT1h : ∀ z : (Σ k, S.WIdx k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T1.h z = 1`. Introduce `z hz`. Simplify using `only [hT1, HermLine.tensor, hX₁i, hermZpow_neg_one_h]`.

Conclude with `mul_inv_cancel₀ (X₁.pos z hz).ne'`. Establish `aT2 : T2.a = 0`. Use function extensionality and compare the values at `k`. Use `hdeg k` as an intermediate fact. Simplify using `only [hT2, hQ, hLL, HermLine.tensor, halfInvLine, Pi.add_apply, Pi.zero_apply]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT2h : ∀ z : (Σ k, S.WIdx k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T2.h z = 1`. Introduce `z hz`. Establish `hpos : 0 < X₀.h z * X₁.h z` using `mul_pos (X₀.pos z hz) (X₁.pos z hz)`. Simplify using `only [hT2, hQ, hLL, HermLine.tensor]`.

Rewrite using `[halfInvLine_h_of_pos _ _ _ _ z hz, ← Real.rpow_add hpos]`. Evaluate the numerical expressions. Rewrite using `[Real.rpow_neg_one]`. Conclude with `mul_inv_cancel₀ hpos.ne'`. Use `set G : HermLine S.WIdx → HermLine S.WIdx → ℝ := fun A B => I T.WBlk S.WIdx S.WW (D + 2) (Fin.snoc (Fin.cons A L : Fin (D + 1) → HermLine S.WIdx) B) with hG`.

Establish `G_add : ∀ {A B C'}, IsSmoothHerm A → IsSmoothHerm B → IsSmoothHerm C' → G A (B.tensor C') = G A B + G A C'` using `fun hA hB hC => hF.2.1 S.WW (D + 1) _ _ _ hW (smooth_cons hA hL) hB hC`. Establish `G_symm : ∀ {A B}, IsSmoothHerm A → IsSmoothHerm B → G A B = G B A`. Introduce `A B hA hB`. Use `hF.1 S.WW (D + 2) (Fin.snoc (Fin.cons B L : Fin (D + 1) → HermLine S.WIdx) A) (Equiv.swap 0 (Fin.last (D + 1))) hW (smooth_snoc hA (smooth_cons hB hL))` as an intermediate fact. Rewrite `this` using `[snoc_cons_comp_swap]`.

Conclude with `this`. Establish `G_triv : ∀ {A B}, IsSmoothHerm A → IsSmoothHerm B → B.a = 0 → (∀ z : (Σ k, S.WIdx k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = 1) → G A B = 0` using `fun hA hB ha h1 => I_snoc_triv hF hW (smooth_cons hA hL) hB ha fun z hz => h1 z hz.1`. Establish `e1 : G M Q = G Q X₀ + G Q X₁i` using `by rw [G_symm hsM hsQ]; exact G_add hsQ hs0 hs1i`. Establish `e2 : G Q X₁ + G Q X₁i = 0` using `by rw [← G_add hsQ hs1 hs1i]; exact G_triv hsQ hsT1 aT1 hT1h`. Establish `e3 : G Q X₀ = G X₀ X₀ + G X₀ X₁` using `by rw [G_symm hsQ hs0]; exact G_add hs0 hs0 hs1`.

Establish `e4 : G Q X₁ = G X₁ X₀ + G X₁ X₁` using `by rw [G_symm hsQ hs1]; exact G_add hs1 hs0 hs1`. Establish `e5 : G X₀ X₁ = G X₁ X₀` using `G_symm hs0 hs1`. Establish `e6 : G M Q + G M LL + G M LL = 0`. Rewrite using `[add_assoc, ← G_add hsM hsLL hsLL, ← G_add hsM hsQ (isSmoothHerm_tensor hsLL hsLL)]`. Conclude with `G_triv hsM hsT2 aT2 hT2h`.

Establish `hgW : S.g ∉ S.WW`. Establish `hh : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) S.h ≠ 0` using `(not_mem_ker_iff_aeval_ne _ S.h _ S.h_deg).1 S.h_nmem`. Use `(not_mem_ker_iff_aeval_ne _ S.g _ S.g_deg).2 ?_` and prove the remaining obligations. Rewrite using `[S.quot]`. Use `mul_ne_zero ?_ hh` and prove the remaining obligations.

Conclude with `sub_ne_zero.2 (S.indep.injective.ne (by decide))`. Establish `hrat : IsRatSectionOn S.WW LL S.g S.h` using `⟨_, _, S.g_deg, S.h_deg, hgW, S.h_nmem, fun k => by`. Apply the tactic sequence `cases k <;> simp [T.wwDeg, T.llDeg, T.unitDeg, hLL, halfInvLine]⟩`. Establish `e7 : G M LL = recRRat (I T.WBlk S.WIdx) S.WW (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) LL S.g S.h` using `hR T.WBlk S.WIdx (I T.WBlk S.WIdx) hF S.WW (D + 1) _ LL S.g S.h hW (smooth_cons hsM hL) hsLL hrat`. Establish `hdiv` using `(hDD S.Ω S.ι S.ν S.κ S.E S.Φ S.x S.B S.e S.φ S.δ S.dualSec S.dualGen S.detGen S.chart S.a S.indep).2 S.n S.g S.h S.g_deg S.h_deg S.h_nmem S.quot`.

Establish `hΔhor : IsHorizontal S.Diag`. Establish `h` using `hW.2.2.1`. Unfold `IsHorizontal at h ⊢`. Rewrite using `[← h]`. Conclude with `comap_C_ker_multiConeMap _ _`.

Establish `hΔmem : S.Diag ∈ divSupp S.WW S.g`. Use `mem_divSupp_of_divCycle_ne_zero fun h0 => ?_` and prove the remaining obligations. Use `congrArg (fun z => z S.Diag) hdiv` as an intermediate fact. Simplify using `only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply, h0, Finsupp.single_eq_same] at this`. Use linear arithmetic over natural numbers and integers.

Establish `hΔ : IsArithVar S.Diag (D + 1)` using `(divSuppArith T.WBlk S.WIdx S.WW (D + 1) (HermLine.ofMetrics (fun k => maxMetric ℂ (S.WIdx k)) (fun k => (T.wwDeg S.n 1 k : ℤ))) S.g S.Diag hW ⟨T.wwDeg S.n 1, fun _ => rfl, S.g_deg, hgW⟩ hΔmem).1 hΔhor`. Establish `e8 : cycR (I T.WBlk S.WIdx) S.WW (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) S.g - cycR (I T.WBlk S.WIdx) S.WW (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) S.h = I T.WBlk S.WIdx S.Diag (D + 1) (Fin.cons M L)` using `cycR_sub_eq _ _ _ _ _ _ hdiv hΔhor`. Establish `e9 : I T.WBlk S.WIdx S.Diag (D + 1) (Fin.cons M L) = 0`. Establish `hrot` using `hF.1 S.Diag (D + 1) (Fin.cons M L) (finRotate (D + 1)) hΔ (smooth_cons hsM hL)`. Establish `hsnoc : (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) ∘ finRotate (D + 1) = Fin.snoc L M` using `(Fin.snoc_eq_cons_rotate L M).symm`.

Rewrite `hrot` using `[hsnoc]`. Rewrite using `[← hrot]`. Establish `a1` using `hF.2.1 S.Diag D L X₀ X₁i hΔ hL hs0 hs1i`. Establish `a2` using `hF.2.1 S.Diag D L X₁ X₁i hΔ hL hs1 hs1i`. Establish `a3` using `I_snoc_triv hF hΔ hL hsT1 aT1 fun z hz => hT1h z hz.1`.

Establish `a4` using `hPI I hI D S X X₀ X₁ L hX hp0 hp1 hL`. Rewrite using `[hM, a1]`. Rewrite `a3` using `[hT1]`. Rewrite `a2` using `[a3]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e10 : ptsIntegral S.WW (pot (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx)) (logNormRat LL S.g S.h) = diagInt S.WW S.g S.h X₀ X₁ L`. Unfold `diagInt`. Rewrite using `[ptsIntegral_congr_mcPts S.WW (φ' := Fin.cons (α := fun _ => ((Σ k, T.wwIdx S.ι S.ν S.κ k) → ℂ) → ℝ) (fun z => Real.log (X₀.h z) - Real.log (X₁.h z)) (pot L)) (g' := logNormRat LL S.g S.h) ?_ (fun _ _ => rfl)]`. Use `hZ T.WBlk S.WIdx S.WW (D + 1) (S.g * S.h) _ _ _ _ hW (exHomog_mul S.g_deg S.h_deg) (fun hm => (hWp.mem_or_mem hm).elim hgW S.h_nmem) ?_` and prove the remaining obligations. Introduce `z hz hne`.

Establish `hz'` using `hz.1`. Rewrite `hne` using `[map_mul, eval_mul]`. Establish `hgz : ‖eval z (map (Int.castRingHom ℂ) S.g)‖ ≠ 0` using `norm_ne_zero_iff.2 (left_ne_zero_of_mul hne)`. Establish `hhz : ‖eval z (map (Int.castRingHom ℂ) S.h)‖ ≠ 0` using `norm_ne_zero_iff.2 (right_ne_zero_of_mul hne)`. Establish `h0` using `X₀.pos z hz'`.

Establish `h1` using `X₁.pos z hz'`. Unfold `logNormRat diagLogNorm`. Rewrite using `[hLL, halfInvLine_h_of_pos _ _ _ _ z hz', Real.log_div (div_ne_zero hgz hhz) (Real.rpow_pos_of_pos (mul_pos h0 h1) _).ne', Real.log_rpow (mul_pos h0 h1), Real.log_mul h0.ne' h1.ne']`. Expand and normalize the polynomial expressions, which then agree. Introduce `j z hz`.

Consider the cases of `j using Fin.cases with`. Consider the case `zero`. Simplify using `only [pot, Fin.cons_zero, hM, HermLine.tensor, hX₁i, hermZpow_neg_one_h]`. Rewrite using `[Real.log_mul (X₀.pos z hz.1).ne' (inv_ne_zero (X₁.pos z hz.1).ne'), Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `succ i => simp [pot]`. Establish `hrotG : ∀ A, IsSmoothHerm A → I T.WBlk S.WIdx S.WW (D + 2) (Fin.append L ![A, A]) = G A A`. Introduce `A hA`. Rewrite using `[append_pair_eq]`. Establish `hrot` using `hF.1 S.WW (D + 2) (Fin.cons A (Fin.snoc L A : Fin (D + 1) → HermLine S.WIdx)) (finRotate (D + 2)) hW (smooth_cons hA (smooth_snoc hA hL))`.

Establish `hs : (Fin.cons A (Fin.snoc L A : Fin (D + 1) → HermLine S.WIdx) : Fin (D + 2) → HermLine S.WIdx) ∘ finRotate (D + 2) = Fin.snoc (Fin.snoc L A : Fin (D + 1) → HermLine S.WIdx) A` using `(Fin.snoc_eq_cons_rotate _ A).symm`. Rewrite `hrot` using `[hs, Fin.cons_snoc_eq_snoc_cons]`. Conclude with `hrot`. Rewrite using `[hrotG X₀ hs0, hrotG X₁ hs1]`. Establish `e11 : G M LL = I T.WBlk S.WIdx S.Diag (D + 1) (Fin.cons M L) - ptsIntegral S.WW (pot (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx)) (logNormRat LL S.g S.h)`.

Rewrite using `[e7, recRRat, e8]`. Rewrite `e11` using `[e9, e10]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem DiagR.proof (hR : RatR.Statement) (hDD : DiagDiv.Statement) (hPI : DiagPullI.Statement)
    (hZ : ZeroSetNull.Statement) : DiagR.Statement := by
  intro I hI D S X X₀ X₁ L hXa hX hp0 hp1 hL
  have hF : IsIntersectionFamily (I T.WBlk S.WIdx) := hI T.WBlk S.WIdx
  have hW : IsArithVar S.WW (D + 2) := S.arithWW
  have hWp : S.WW.IsPrime := hW.2.1.1
  have hs0 : IsSmoothHerm X₀ := isSmoothHerm_pull 0 hX hp0
  have hs1 : IsSmoothHerm X₁ := isSmoothHerm_pull 1 hX hp1

  have hdeg : ∀ k, 2 * T.llDeg k = -(X₀.a k + X₁.a k) := by
    have a0 : ∀ k, X₀.a k = I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY k := fun k => by rw [hp0.1, hXa]
    have a1 : ∀ k, X₁.a k = I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY k := fun k => by rw [hp1.1, hXa]
    have p0b : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .base = 3 := pullDeg_segreBlockEmbedding 0 T.twoXiDegY .base
    have p0d : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .det = -1 := pullDeg_segreBlockEmbedding 0 T.twoXiDegY .det
    have p0l0 : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .line0 = -2 := pullDeg_segreBlockEmbedding 0 T.twoXiDegY .line
    have p0l1 : I1.pullDeg (diagonalBlockIndex 0) T.twoXiDegY .line1 = 0 := pullDeg_otherLine 0 T.twoXiDegY
    have p1b : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .base = 3 := pullDeg_segreBlockEmbedding 1 T.twoXiDegY .base
    have p1d : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .det = -1 := pullDeg_segreBlockEmbedding 1 T.twoXiDegY .det
    have p1l0 : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .line0 = 0 := pullDeg_otherLine 1 T.twoXiDegY
    have p1l1 : I1.pullDeg (diagonalBlockIndex 1) T.twoXiDegY .line1 = -2 := pullDeg_segreBlockEmbedding 1 T.twoXiDegY .line
    intro k
    rw [a0, a1]
    cases k
    · rw [p0b, p1b]; simp [T.llDeg, T.unitDeg]
    · rw [p0d, p1d]; simp [T.llDeg, T.unitDeg]
    · rw [p0l0, p1l0]; simp [T.llDeg, T.unitDeg]
    · rw [p0l1, p1l1]; simp [T.llDeg, T.unitDeg]

  set X₁i := hermZpow X₁ (-1) with hX₁i
  set M := X₀.tensor X₁i with hM
  set Q := X₀.tensor X₁ with hQ
  set LL := halfInvLine X₀ X₁ T.llDeg hdeg with hLL
  have hs1i : IsSmoothHerm X₁i := isSmoothHerm_inv hs1
  have hsM : IsSmoothHerm M := isSmoothHerm_tensor hs0 hs1i
  have hsQ : IsSmoothHerm Q := isSmoothHerm_tensor hs0 hs1
  have hsLL : IsSmoothHerm LL := isSmoothHerm_halfInvLine hs0 hs1 _ hdeg

  set T1 := X₁.tensor X₁i with hT1
  set T2 := Q.tensor (LL.tensor LL) with hT2
  have hsT1 : IsSmoothHerm T1 := isSmoothHerm_tensor hs1 hs1i
  have hsT2 : IsSmoothHerm T2 := isSmoothHerm_tensor hsQ (isSmoothHerm_tensor hsLL hsLL)
  have aT1 : T1.a = 0 := by
    simp only [hT1, HermLine.tensor, hX₁i, hermZpow_neg_one_a, add_neg_cancel]
  have hT1h : ∀ z : (Σ k, S.WIdx k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T1.h z = 1 := by
    intro z hz
    simp only [hT1, HermLine.tensor, hX₁i, hermZpow_neg_one_h]
    exact mul_inv_cancel₀ (X₁.pos z hz).ne'
  have aT2 : T2.a = 0 := by
    funext k
    have := hdeg k
    simp only [hT2, hQ, hLL, HermLine.tensor, halfInvLine, Pi.add_apply, Pi.zero_apply]
    linarith
  have hT2h : ∀ z : (Σ k, S.WIdx k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T2.h z = 1 := by
    intro z hz
    have hpos : 0 < X₀.h z * X₁.h z := mul_pos (X₀.pos z hz) (X₁.pos z hz)
    simp only [hT2, hQ, hLL, HermLine.tensor]
    rw [halfInvLine_h_of_pos _ _ _ _ z hz, ← Real.rpow_add hpos]
    norm_num
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hpos.ne'

  set G : HermLine S.WIdx → HermLine S.WIdx → ℝ :=
    fun A B => I T.WBlk S.WIdx S.WW (D + 2) (Fin.snoc (Fin.cons A L : Fin (D + 1) → HermLine S.WIdx) B)
    with hG
  have G_add : ∀ {A B C'}, IsSmoothHerm A → IsSmoothHerm B → IsSmoothHerm C' →
      G A (B.tensor C') = G A B + G A C' := fun hA hB hC =>
    hF.2.1 S.WW (D + 1) _ _ _ hW (smooth_cons hA hL) hB hC
  have G_symm : ∀ {A B}, IsSmoothHerm A → IsSmoothHerm B → G A B = G B A := by
    intro A B hA hB
    have := hF.1 S.WW (D + 2) (Fin.snoc (Fin.cons B L : Fin (D + 1) → HermLine S.WIdx) A)
      (Equiv.swap 0 (Fin.last (D + 1))) hW (smooth_snoc hA (smooth_cons hB hL))
    rw [snoc_cons_comp_swap] at this
    exact this
  have G_triv : ∀ {A B}, IsSmoothHerm A → IsSmoothHerm B → B.a = 0 →
      (∀ z : (Σ k, S.WIdx k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = 1) → G A B = 0 :=
    fun hA hB ha h1 => I_snoc_triv hF hW (smooth_cons hA hL) hB ha fun z hz => h1 z hz.1

  have e1 : G M Q = G Q X₀ + G Q X₁i := by rw [G_symm hsM hsQ]; exact G_add hsQ hs0 hs1i
  have e2 : G Q X₁ + G Q X₁i = 0 := by rw [← G_add hsQ hs1 hs1i]; exact G_triv hsQ hsT1 aT1 hT1h
  have e3 : G Q X₀ = G X₀ X₀ + G X₀ X₁ := by rw [G_symm hsQ hs0]; exact G_add hs0 hs0 hs1
  have e4 : G Q X₁ = G X₁ X₀ + G X₁ X₁ := by rw [G_symm hsQ hs1]; exact G_add hs1 hs0 hs1
  have e5 : G X₀ X₁ = G X₁ X₀ := G_symm hs0 hs1

  have e6 : G M Q + G M LL + G M LL = 0 := by
    rw [add_assoc, ← G_add hsM hsLL hsLL, ← G_add hsM hsQ (isSmoothHerm_tensor hsLL hsLL)]
    exact G_triv hsM hsT2 aT2 hT2h

  have hgW : S.g ∉ S.WW := by
    have hh : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) S.h ≠ 0 :=
      (not_mem_ker_iff_aeval_ne _ S.h _ S.h_deg).1 S.h_nmem
    refine (not_mem_ker_iff_aeval_ne _ S.g _ S.g_deg).2 ?_
    rw [S.quot]
    refine mul_ne_zero ?_ hh
    exact sub_ne_zero.2 (S.indep.injective.ne (by decide))
  have hrat : IsRatSectionOn S.WW LL S.g S.h :=
    ⟨_, _, S.g_deg, S.h_deg, hgW, S.h_nmem, fun k => by
      cases k <;> simp [T.wwDeg, T.llDeg, T.unitDeg, hLL, halfInvLine]⟩
  have e7 : G M LL = recRRat (I T.WBlk S.WIdx) S.WW (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) LL S.g S.h :=
    hR T.WBlk S.WIdx (I T.WBlk S.WIdx) hF S.WW (D + 1) _ LL S.g S.h hW (smooth_cons hsM hL) hsLL hrat

  have hdiv := (hDD S.Ω S.ι S.ν S.κ S.E S.Φ S.x S.B S.e S.φ S.δ S.dualSec S.dualGen S.detGen S.chart S.a
    S.indep).2 S.n S.g S.h S.g_deg S.h_deg S.h_nmem S.quot
  have hΔhor : IsHorizontal S.Diag := by
    have h := hW.2.2.1
    unfold IsHorizontal at h ⊢
    rw [← h]
    exact comap_C_ker_multiConeMap _ _
  have hΔmem : S.Diag ∈ divSupp S.WW S.g := by
    refine mem_divSupp_of_divCycle_ne_zero fun h0 => ?_
    have := congrArg (fun z => z S.Diag) hdiv
    simp only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply, h0,
      Finsupp.single_eq_same] at this
    omega
  have hΔ : IsArithVar S.Diag (D + 1) :=
    (divSuppArith T.WBlk S.WIdx S.WW (D + 1)
      (HermLine.ofMetrics (fun k => maxMetric ℂ (S.WIdx k)) (fun k => (T.wwDeg S.n 1 k : ℤ))) S.g S.Diag hW
      ⟨T.wwDeg S.n 1, fun _ => rfl, S.g_deg, hgW⟩ hΔmem).1 hΔhor
  have e8 : cycR (I T.WBlk S.WIdx) S.WW (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) S.g -
      cycR (I T.WBlk S.WIdx) S.WW (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) S.h =
      I T.WBlk S.WIdx S.Diag (D + 1) (Fin.cons M L) :=
    cycR_sub_eq _ _ _ _ _ _ hdiv hΔhor
  have e9 : I T.WBlk S.WIdx S.Diag (D + 1) (Fin.cons M L) = 0 := by
    have hrot := hF.1 S.Diag (D + 1) (Fin.cons M L) (finRotate (D + 1)) hΔ (smooth_cons hsM hL)
    have hsnoc : (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx) ∘ finRotate (D + 1) = Fin.snoc L M :=
      (Fin.snoc_eq_cons_rotate L M).symm
    rw [hsnoc] at hrot
    rw [← hrot]
    have a1 := hF.2.1 S.Diag D L X₀ X₁i hΔ hL hs0 hs1i
    have a2 := hF.2.1 S.Diag D L X₁ X₁i hΔ hL hs1 hs1i
    have a3 := I_snoc_triv hF hΔ hL hsT1 aT1 fun z hz => hT1h z hz.1
    have a4 := hPI I hI D S X X₀ X₁ L hX hp0 hp1 hL
    rw [hM, a1]
    rw [hT1] at a3
    rw [a3] at a2
    linarith

  have e10 : ptsIntegral S.WW (pot (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx)) (logNormRat LL S.g S.h) =
      diagInt S.WW S.g S.h X₀ X₁ L := by
    unfold diagInt
    rw [ptsIntegral_congr_mcPts S.WW
      (φ' := Fin.cons (α := fun _ => ((Σ k, T.wwIdx S.ι S.ν S.κ k) → ℂ) → ℝ)
        (fun z => Real.log (X₀.h z) - Real.log (X₁.h z)) (pot L))
      (g' := logNormRat LL S.g S.h) ?_ (fun _ _ => rfl)]
    · refine hZ T.WBlk S.WIdx S.WW (D + 1) (S.g * S.h) _ _ _ _ hW (exHomog_mul S.g_deg S.h_deg)
        (fun hm => (hWp.mem_or_mem hm).elim hgW S.h_nmem) ?_
      intro z hz hne
      have hz' := hz.1
      rw [map_mul, eval_mul] at hne
      have hgz : ‖eval z (map (Int.castRingHom ℂ) S.g)‖ ≠ 0 := norm_ne_zero_iff.2 (left_ne_zero_of_mul hne)
      have hhz : ‖eval z (map (Int.castRingHom ℂ) S.h)‖ ≠ 0 := norm_ne_zero_iff.2 (right_ne_zero_of_mul hne)
      have h0 := X₀.pos z hz'
      have h1 := X₁.pos z hz'
      unfold logNormRat diagLogNorm
      rw [hLL, halfInvLine_h_of_pos _ _ _ _ z hz',
        Real.log_div (div_ne_zero hgz hhz) (Real.rpow_pos_of_pos (mul_pos h0 h1) _).ne',
        Real.log_rpow (mul_pos h0 h1), Real.log_mul h0.ne' h1.ne']
      ring
    · intro j z hz
      cases j using Fin.cases with
      | zero =>
        simp only [pot, Fin.cons_zero, hM, HermLine.tensor, hX₁i, hermZpow_neg_one_h]
        rw [Real.log_mul (X₀.pos z hz.1).ne' (inv_ne_zero (X₁.pos z hz.1).ne'), Real.log_inv]
        ring
      | succ i => simp [pot]

  have hrotG : ∀ A, IsSmoothHerm A →
      I T.WBlk S.WIdx S.WW (D + 2) (Fin.append L ![A, A]) = G A A := by
    intro A hA
    rw [append_pair_eq]
    have hrot := hF.1 S.WW (D + 2)
      (Fin.cons A (Fin.snoc L A : Fin (D + 1) → HermLine S.WIdx)) (finRotate (D + 2)) hW
      (smooth_cons hA (smooth_snoc hA hL))
    have hs : (Fin.cons A (Fin.snoc L A : Fin (D + 1) → HermLine S.WIdx) : Fin (D + 2) → HermLine S.WIdx) ∘
        finRotate (D + 2) = Fin.snoc (Fin.snoc L A : Fin (D + 1) → HermLine S.WIdx) A :=
      (Fin.snoc_eq_cons_rotate _ A).symm
    rw [hs, Fin.cons_snoc_eq_snoc_cons] at hrot
    exact hrot
  rw [hrotG X₀ hs0, hrotG X₁ hs1]
  have e11 : G M LL = I T.WBlk S.WIdx S.Diag (D + 1) (Fin.cons M L) -
      ptsIntegral S.WW (pot (Fin.cons M L : Fin (D + 1) → HermLine S.WIdx)) (logNormRat LL S.g S.h) := by
    rw [e7, recRRat, e8]
  rw [e9, e10] at e11
  linarith

end Main

end

end GroundTheory.Heights₂.Heights.Inter
