import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortConnIndep

/- English proof (translation)
Consider the cases of `s with | @mk s1 _ =>`. Consider the cases of `t with | @mk t1 _ =>`. Consider the cases of `s1 with | @mk s2 _ =>`. Consider the cases of `t1 with | @mk t2 _ =>`. Consider the cases of `s2 with | @mk s3 _ =>`.

Consider the cases of `t2 with | @mk t3 _ =>`. Establish `: s3 = t3`. Consider the cases of `s3`. Consider the cases of `t3`. Reduce the equality to equality of the corresponding arguments.

Conclude with `funext h`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R)
    (h : ∀ a : R, @star R s.toStarMul.toInvolutiveStar.toStar a = @star R t.toStarMul.toInvolutiveStar.toStar a) :
    s = t := by
  cases s with | @mk s1 _ =>
  cases t with | @mk t1 _ =>
  cases s1 with | @mk s2 _ =>
  cases t1 with | @mk t2 _ =>
  cases s2 with | @mk s3 _ =>
  cases t2 with | @mk t3 _ =>
  have : s3 = t3 := by
    cases s3; cases t3; congr; exact funext h
  subst this
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Use `letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra`. Establish `hU` using `thExprUniq_of_chartIndep2 hC`. Take `⟨M, hM, hMP, hsupp⟩` from `GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP`. Establish `key0 : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) → ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)), ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) * ∏ b, nab y K (G b) (colOf m b) = ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) …`. Introduce and unpack `K k rfl G`.

Conclude with `hU E H Dw l Xo c nab nab' h h' S y k n G a _ hMP`. Establish `key` using `key0 _ (N ^ 2) (Nat.cast_pow N 2).symm F`. Rewrite `key` using `[hsupp]`. Simplify using `only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S), _root_.mul_assoc, ← Finset.mul_sum] at key`. Establish `hu : IsUnit (algebraMap c.F S (M : c.F))` using `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _`.

Conclude with `hu.mul_left_cancel key`.
-/
theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hU := thExprUniq_of_chartIndep2 hC
  obtain ⟨M, hM, hMP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key0 : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a _ hMP
  have key := key0 _ (N ^ 2) (Nat.cast_pow N 2).symm F
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S),
    _root_.mul_assoc, ← Finset.mul_sum] at key
  have hu : IsUnit (algebraMap c.F S (M : c.F)) :=
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _
  exact hu.mul_left_cancel key

/- English proof (translation)
Take `⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩` from `hv`. Use `⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7.trans ?_⟩` and prove the remaining obligations. Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun i _ => sum_eq hC nab nab' h h' y' a P hP N (F q i)`.
-/
theorem shortValAt_of (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (hv : ShortValAt Xo c nab w Λ β N P y v) : ShortValAt Xo c nab' w Λ β N P y v := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7.trans ?_⟩
  congr 1
  refine finsum_congr fun q => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_eq hC nab nab' h h' y' a P hP N (F q i)

end GlobalTheory.ShortConnIndep

namespace GlobalTheory

/- English proof (translation)
Introduce `hC E _ _ _ H Dw l Xo c n d nab bad nV ⟨s, hs⟩ t nab' ht a`. Establish `hst : s = t` using `ShortConnIndep.starRing_eq s t fun x => (hs.1 x).trans (ht.1 x).symm`. Substitute `hst` using the available equality. Establish `hmap` using `(admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a`. Use `Set.ext fun f => ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩`. Use `⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩` and prove the remaining obligations. Introduce `k i1 i2 i3 i4 hk y y₂ hy`. Take `⟨v, hv, he⟩` from `@hr k i1 i2 i3 i4 hk y y₂ hy`. Conclude with `⟨v, ShortConnIndep.shortValAt_of hC nab' d.nab₂ ht hs _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩`.

Introduce and unpack `⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩`. Use `⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩` and prove the remaining obligations. Introduce `k i1 i2 i3 i4 hk y y₂ hy`. Take `⟨v, hv, he⟩` from `@hr k i1 i2 i3 i4 hk y y₂ hy`. Conclude with `⟨v, ShortConnIndep.shortValAt_of hC d.nab₂ nab' hs ht _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩`.
-/
theorem shortGen_indep_connection : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (nab : NabV Xo c) (bad nV : ℕ), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (_ : StarRing (𝓞 E)) (nab' : NabV d.Xo₂ d.c₂), IsNab d.Xo₂ d.c₂ nab' → ∀ a, shortGen Xo c nab bad nV a n { d with nab₂ := nab' } = shortGen Xo c nab bad nV a n d := by
  intro hC E _ _ _ H Dw l Xo c n d nab bad nV ⟨s, hs⟩ t nab' ht a
  have hst : s = t := ShortConnIndep.starRing_eq s t fun x => (hs.1 x).trans (ht.1 x).symm
  subst hst
  have hmap := (admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC nab' d.nab₂ ht hs _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC d.nab₂ nab' hs ht _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩

end GlobalTheory
