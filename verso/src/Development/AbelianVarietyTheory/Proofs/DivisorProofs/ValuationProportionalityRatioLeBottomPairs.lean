import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresentaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.LemmaC

open GlobalTheory.NormVal

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `hi`.
-/
theorem integralOver_cast {D : D7} {p m n : ℕ} (e : n = m) (h : GA D n) (hi : IntegralOver D p h) :
    IntegralOver D p (e ▸ h : GA D m) := by
  subst e; exact hi

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨h', rfl, id⟩`.
-/
theorem exists_cast_eq {D : D7} {p m n : ℕ} (e : n = m) (h' : GA D m) :
    ∃ h : GA D n, (e ▸ h : GA D m) = h' ∧ (IntegralOver D p h' → IntegralOver D p h) := by
  subst e; exact ⟨h', rfl, id⟩

/- English proof (translation)
Establish `hm : ((n : ℤ) : ℂ) ∈ Qbar` using `intCast_mem _ n`. Use `⟨hm, fun lam => ?_⟩` and prove the remaining obligations. Rewrite using `[lamC_of_mem lam hm]`. Establish `e1 : (⟨(n : ℂ), hm⟩ : Qbar) = (n : Qbar)` using `Subtype.ext (by simp)`. Rewrite using `[e1, map_intCast]`.

Conclude with `IsUltrametricDist.norm_intCast_le_one _ n`.
-/
theorem bd_intCast (p : ℕ) [Fact p.Prime] (n : ℤ) : Bd p 1 ((n : ℤ) : ℂ) := by
  have hm : ((n : ℤ) : ℂ) ∈ Qbar := intCast_mem _ n
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have e1 : (⟨(n : ℂ), hm⟩ : Qbar) = (n : Qbar) := Subtype.ext (by simp)
  rw [e1, map_intCast]
  exact IsUltrametricDist.norm_intCast_le_one _ n

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D N B Q S del_vp b hI hE hC K _ _ _ σ w p _ hw δ t0 Q₁ Q₂ hQ₁ hQ₂ P₁ P₁' P₂ P₂' hs₁ hs₁' hs₂ hs₂' hd₁ hd₂ b₁ b₂ v M₁ M₂ hr₁ hr₂ hb₂ hv hv1 γ z z' hγ hz hz' hz0 hz0'`. Establish `hp : p.Prime` using `Fact.out`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast hp.one_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Use `set e : ℝ := del_vp p with he`.

Use `set r : ℝ := (p : ℝ) ^ e with hr`. Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hgam : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B → ∀ g, Bd p r ((gam D P.J g : ℂ)⁻¹)` using `fun P hQ' hS g => by`. Take `⟨-, h2, -⟩` from `hC δ t0 p _ hQ' P hS`. Conclude with `(Bd.inv_nat (h2 g).1 dvd_rfl).mono (Real.rpow_le_rpow_of_exponent_le hp1 (h2 g).2)`.

Establish `hco : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B → ∀ g, IntegralOver D p g → ∀ T, Bd p r (P.coord g T)` using `fun P hQ' hS g hg T => (hC δ t0 p _ hQ' P hS).2.2 g hg T`. Establish `hb₁ : b₁ ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : P₁.norm = 0`. Unfold `Pair.norm`.

Use `finsum_eq_zero_of_forall_eq_zero fun q => ?_` and prove the remaining obligations. Establish `: P₁.sq q.out = 0`. Unfold `Pair.sq`. Use `Finset.sum_eq_zero fun T _ => ?_` and prove the remaining obligations. Use `hr₁ q.out T` as an intermediate fact.

Rewrite `this` using `[zero_mul, map_eq_zero]`. Rewrite using `[this, norm_zero]`. Evaluate the numerical expressions. Rewrite using `[this, mul_zero]`. Apply `hz0` to reduce the goal to its premises.

Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[hz, h0, map_zero, Complex.ofReal_zero]`. Establish `hγ0 : γ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hγ` using `[map_zero, zero_mul, zero_mul]`.

Conclude with `hb₁ hγ`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Rewrite `hγ` using `[mul_zero]`. Conclude with `hb₁ hγ`.

Establish `hA : Bd p (r * (r * (1 * r))) ((P₁.norm : ℂ) * b₁⁻¹)`. Take `⟨h1, -, -⟩` from `hC δ t0 p Q₁ hQ₁ P₁ hs₁`. Use `choose s hs1 hs2 using h1`. Rewrite using `[(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₁ P₁.crv P₁.pt0 P₁ P₁.level_pos).2.2.2.1 s hs1]`. Use `finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₁⁻¹)) ?_ (fun x y hx hy => ?_) (fun q => ?_)` and prove the remaining obligations.

Use the proof step `beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)`. Use `beta_reduce at hx hy ⊢`. Rewrite using `[Complex.ofReal_add, add_mul]`. Conclude with `hx.add hy`. Use `beta_reduce`.

Rewrite using `[Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]`. Use `Bd.mul (hgam P₁ hQ₁ hs₁ _) ?_` and prove the remaining obligations. Unfold `Pair.sq`. Rewrite using `[Complex.ofReal_sum, Finset.sum_mul]`. Use `Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)` and prove the remaining obligations.

Establish `e1 : ((‖P₁.coord (s q) T‖ ^ 2 : ℝ) : ℂ) * b₁⁻¹ = P₁.coord (s q) T * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁.symm ▸ s q) T'`. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj', hr₁]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Use `(hco P₁ hQ₁ hs₁ _ (hs2 q) T).mul ?_` and prove the remaining obligations.

Use `Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)` and prove the remaining obligations. Conclude with `(bd_intCast p _).mul (hco P₁' hQ₁ hs₁' _ (integralOver_cast hd₁.symm _ (hs2 q)) T')`. Establish `hB : Bd p (r * (r * (1 * r))) ((P₂'.norm : ℂ) * b₂)`. Take `⟨h1, -, -⟩` from `hC δ t0 p Q₂ hQ₂ P₂' hs₂'`. Use `choose s hs1 hs2 using h1`.

Rewrite using `[(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₂ P₂'.crv P₂'.pt0 P₂' P₂'.level_pos).2.2.2.1 s hs1]`. Use `finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₂)) ?_ (fun x y hx hy => ?_) (fun q => ?_)` and prove the remaining obligations. Use the proof step `beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)`. Use `beta_reduce at hx hy ⊢`. Rewrite using `[Complex.ofReal_add, add_mul]`.

Conclude with `hx.add hy`. Use `beta_reduce`. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]`. Use `Bd.mul (hgam P₂' hQ₂ hs₂' _) ?_` and prove the remaining obligations. Unfold `Pair.sq`.

Rewrite using `[Complex.ofReal_sum, Finset.sum_mul]`. Use `Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)` and prove the remaining obligations. Take `⟨h, hh, hi⟩` from `exists_cast_eq (p := p) hd₂.symm (s q)`. Establish `e1 : ((‖P₂'.coord (s q) T'‖ ^ 2 : ℝ) : ℂ) * b₂ = (starRingEnd ℂ) (P₂'.coord (s q) T') * ∑ T, (M₂ T' T : ℂ) * (starRingEnd ℂ) (P₂.coord h T)`. Rewrite using `[← hr₂ h T', hh, Complex.ofReal_pow, ← Complex.mul_conj']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `(hco P₂' hQ₂ hs₂' _ (hs2 q) T').conj.mul ?_` and prove the remaining obligations. Use `Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)` and prove the remaining obligations. Conclude with `(bd_intCast p _).mul (hco P₂ hQ₂ hs₂ _ (hi (hs2 q)) T).conj`.

Use `set x : K := z * z' * γ⁻¹ with hx`. Establish `hx0 : x ≠ 0` using `mul_ne_zero (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0)`. Establish `hσx : σ x = ((P₁.norm : ℂ) * b₁⁻¹) * ((P₂'.norm : ℂ) * b₂) * v`. Establish `hσγ : σ γ ≠ 0` using `(map_ne_zero σ).2 hγ0`. Rewrite using `[hx, map_mul, map_mul, map_inv₀, hz, hz', hγ]`.

Clear the denominators using the available nonvanishing facts. Establish `hX : Bd p (r * (r * (1 * r)) * (r * (r * (1 * r))) * 1) (σ x)`. Rewrite using `[hσx]`. Conclude with `(hA.mul hB).mul ⟨hv, fun lam => (hv1 lam).le⟩`. Establish `hpow : r * (r * (1 * r)) * (r * (r * (1 * r))) * 1 = (p : ℝ) ^ (6 * e)`.

Rewrite using `[mul_comm 6 e, Real.rpow_mul hp0.le, hr]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ x p w (6 * e) hx0 hw fun lam => (hX.2 lam).trans (le_of_eq hpow)`. Establish `hvx : (Formalism.DivisionValues.vw w x : ℝ) = Formalism.DivisionValues.vw w z + Formalism.DivisionValues.vw w z' - Formalism.DivisionValues.vw w γ`.

Rewrite using `[hx, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0), Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hz0 hz0', Formalism.DivisionValues.ValuationRepresentative.vw_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE.wt_eq hp w hw]`. Rewrite `key` using `[hvx]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vw_le_of_bottom_pairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  intro D N B Q S del_vp b hI hE hC K _ _ _ σ w p _ hw δ t0 Q₁ Q₂ hQ₁ hQ₂ P₁ P₁' P₂ P₂' hs₁ hs₁' hs₂ hs₂' hd₁ hd₂ b₁ b₂ v M₁ M₂ hr₁ hr₂ hb₂ hv hv1 γ z z' hγ hz hz' hz0 hz0'
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := del_vp p with he
  set r : ℝ := (p : ℝ) ^ e with hr
  have hr0 : 0 ≤ r := by positivity

  have hgam : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, Bd p r ((gam D P.J g : ℂ)⁻¹) := fun P hQ' hS g => by
    obtain ⟨-, h2, -⟩ := hC δ t0 p _ hQ' P hS
    exact (Bd.inv_nat (h2 g).1 dvd_rfl).mono (Real.rpow_le_rpow_of_exponent_le hp1 (h2 g).2)

  have hco : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, IntegralOver D p g → ∀ T, Bd p r (P.coord g T) := fun P hQ' hS g hg T =>
    (hC δ t0 p _ hQ' P hS).2.2 g hg T

  have hb₁ : b₁ ≠ 0 := by
    rintro rfl
    have h0 : P₁.norm = 0 := by
      unfold Pair.norm
      refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
      have : P₁.sq q.out = 0 := by
        unfold Pair.sq
        refine Finset.sum_eq_zero fun T _ => ?_
        have := hr₁ q.out T
        rw [zero_mul, map_eq_zero] at this
        rw [this, norm_zero]; norm_num
      rw [this, mul_zero]
    apply hz0
    apply σ.injective
    rw [hz, h0, map_zero, Complex.ofReal_zero]
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, zero_mul] at hγ
    exact hb₁ hγ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hγ
    exact hb₁ hγ

  have hA : Bd p (r * (r * (1 * r))) ((P₁.norm : ℂ) * b₁⁻¹) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₁ hQ₁ P₁ hs₁
    choose s hs1 hs2 using h1
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₁ P₁.crv P₁.pt0 P₁ P₁.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₁⁻¹)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₁ hQ₁ hs₁ _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      have e1 : ((‖P₁.coord (s q) T‖ ^ 2 : ℝ) : ℂ) * b₁⁻¹ =
          P₁.coord (s q) T * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁.symm ▸ s q) T' := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', hr₁]
        field_simp
      rw [e1]
      refine (hco P₁ hQ₁ hs₁ _ (hs2 q) T).mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      exact (bd_intCast p _).mul (hco P₁' hQ₁ hs₁' _ (integralOver_cast hd₁.symm _ (hs2 q)) T')

  have hB : Bd p (r * (r * (1 * r))) ((P₂'.norm : ℂ) * b₂) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₂ hQ₂ P₂' hs₂'
    choose s hs1 hs2 using h1
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₂ P₂'.crv P₂'.pt0 P₂' P₂'.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₂)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₂' hQ₂ hs₂' _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      obtain ⟨h, hh, hi⟩ := exists_cast_eq (p := p) hd₂.symm (s q)
      have e1 : ((‖P₂'.coord (s q) T'‖ ^ 2 : ℝ) : ℂ) * b₂ =
          (starRingEnd ℂ) (P₂'.coord (s q) T') * ∑ T, (M₂ T' T : ℂ) * (starRingEnd ℂ) (P₂.coord h T) := by
        rw [← hr₂ h T', hh, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
      rw [e1]
      refine (hco P₂' hQ₂ hs₂' _ (hs2 q) T').conj.mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      exact (bd_intCast p _).mul (hco P₂ hQ₂ hs₂ _ (hi (hs2 q)) T).conj

  set x : K := z * z' * γ⁻¹ with hx
  have hx0 : x ≠ 0 := mul_ne_zero (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0)
  have hσx : σ x = ((P₁.norm : ℂ) * b₁⁻¹) * ((P₂'.norm : ℂ) * b₂) * v := by
    have hσγ : σ γ ≠ 0 := (map_ne_zero σ).2 hγ0
    rw [hx, map_mul, map_mul, map_inv₀, hz, hz', hγ]
    field_simp
  have hX : Bd p (r * (r * (1 * r)) * (r * (r * (1 * r))) * 1) (σ x) := by
    rw [hσx]
    exact (hA.mul hB).mul ⟨hv, fun lam => (hv1 lam).le⟩
  have hpow : r * (r * (1 * r)) * (r * (r * (1 * r))) * 1 = (p : ℝ) ^ (6 * e) := by
    rw [mul_comm 6 e, Real.rpow_mul hp0.le, hr]
    norm_num
    ring
  have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ x p w (6 * e) hx0 hw fun lam =>
    (hX.2 lam).trans (le_of_eq hpow)
  have hvx : (Formalism.DivisionValues.vw w x : ℝ) = Formalism.DivisionValues.vw w z + Formalism.DivisionValues.vw w z' - Formalism.DivisionValues.vw w γ := by
    rw [hx, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0),
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hz0 hz0', Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    push_cast; ring
  rw [hE.wt_eq hp w hw]
  rw [hvx] at key
  linarith

end GlobalTheory.NormSum.LemmaC
