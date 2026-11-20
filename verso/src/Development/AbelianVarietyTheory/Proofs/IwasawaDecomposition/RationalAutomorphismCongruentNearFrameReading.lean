import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.NearCong

open WithZero

/- English proof (translation)
Introduce `r s`. Establish `he : exp (-(N : ℤ)) ≤ 1`. Rewrite using `[← exp_zero, exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `e : A * C - 1 = (A - 1) * (C - 1) + (A - 1) + (C - 1)` using `by noncomm_ring`.

Rewrite using `[e, Matrix.add_apply, Matrix.add_apply]`. Use `v.map_add_le (v.map_add_le ?_ (hA r s)) (hC r s)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `v.map_sum_le fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_cong {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {n : ℕ} (N : ℕ) (A C : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r s, v ((A - 1) r s) ≤ exp (-(N : ℤ))) (hC : ∀ r s, v ((C - 1) r s) ≤ exp (-(N : ℤ))) :
    ∀ r s, v ((A * C - 1) r s) ≤ exp (-(N : ℤ)) := by
  intro r s
  have he : exp (-(N : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have e : A * C - 1 = (A - 1) * (C - 1) + (A - 1) + (C - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine v.map_add_le (v.map_add_le ?_ (hA r s)) (hC r s)
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul]
  calc v ((A - 1) r k) * v ((C - 1) k s) ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hA r k) ((hC k s).trans he)
    _ = exp (-(N : ℤ)) := mul_one _

section Rat
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Introduce `x hx`. Establish `hgi : g⁻¹ ∈ Formalism.L2.Col.GLint E n P` using `inv_mem hg`. Establish `e1 : (g⁻¹ * g') x = g⁻¹ (g' x)` using `rfl`. Establish `e2 : g⁻¹ (g x) = x` using `by show (g⁻¹ * g) x = x`. Rewrite using `[inv_mul_cancel]`.

Both sides reduce to the same expression. Establish `e : (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) = g⁻¹ ((((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x))`. Rewrite using `[map_smul, map_sub, e1, e2]`. Rewrite using `[e]`. Conclude with `(hgi _).2 (hC x hx)`.
-/
theorem congE_inv_mul (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hC : CongE P c g' g) : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) ∈ Formalism.L2.Col.stdAt E n P := by
  intro x hx
  have hgi : g⁻¹ ∈ Formalism.L2.Col.GLint E n P := inv_mem hg
  have e1 : (g⁻¹ * g') x = g⁻¹ (g' x) := rfl
  have e2 : g⁻¹ (g x) = x := by
    show (g⁻¹ * g) x = x
    rw [inv_mul_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) = g⁻¹ ((((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x)) := by
    rw [map_smul, map_sub, e1, e2]
  rw [e]
  exact (hgi _).2 (hC x hx)

/- English proof (translation)
Establish `hx : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P`. Rewrite using `[GlobalTheory.TwistRowType.mem_stdAt]`. Introduce `k`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`.

Conclude with `(GlobalTheory.TwistRowType.intSub P).one_mem`. Conclude with `(GlobalTheory.TwistRowType.intSub P).zero_mem`. Establish `h1` using `(GlobalTheory.TwistRowType.mem_stdAt P _).1 (hh _ hx) r`. Rewrite `h1` using `[GlobalTheory.UnramCompletion.intAt_iff]`. Rewrite `h1` using `[Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply, map_mul, map_inv₀, map_pow, hq]`.

Establish `e : LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s = h (Pi.single s 1) r - (if r = s then 1 else 0)`. Rewrite using `[LinearMap.toMatrix'_apply, Matrix.one_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Generalize the expression as in `P.valuation E (h (Pi.single s 1) r - if r = s then 1 else 0) = y at h1`.

Establish `hE : (exp (-1 : ℤ) ^ c)⁻¹ = exp (c : ℤ)`. Rewrite using `[← WithZero.exp_nsmul, ← WithZero.exp_neg]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hE]`.

Establish `hm : exp (-(c : ℤ)) * exp (c : ℤ) = 1` using `by rw [← exp_add]; simp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_entry (P : HeightOneSpectrum (𝓞 E)) (hq : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ)) (c : ℕ)
    (h : Sp E n ≃ₗ[E] Sp E n)
    (hh : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (h x - x) ∈ Formalism.L2.Col.stdAt E n P) (r s : Fin n) :
    P.valuation E (LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s) ≤ exp (-(c : ℤ)) := by
  have hx : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    rw [GlobalTheory.TwistRowType.mem_stdAt]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact (GlobalTheory.TwistRowType.intSub P).one_mem
    · exact (GlobalTheory.TwistRowType.intSub P).zero_mem
  have h1 := (GlobalTheory.TwistRowType.mem_stdAt P _).1 (hh _ hx) r
  rw [GlobalTheory.UnramCompletion.intAt_iff] at h1
  rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply, map_mul, map_inv₀, map_pow, hq] at h1
  have e : LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s = h (Pi.single s 1) r - (if r = s then 1 else 0) := by
    rw [LinearMap.toMatrix'_apply, Matrix.one_apply]; rfl
  rw [e]
  generalize P.valuation E (h (Pi.single s 1) r - if r = s then 1 else 0) = y at h1
  have hE : (exp (-1 : ℤ) ^ c)⁻¹ = exp (c : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]; congr 1; simp
  rw [hE] at h1
  have hm : exp (-(c : ℤ)) * exp (c : ℤ) = 1 := by rw [← exp_add]; simp
  calc y = (exp (-(c : ℤ)) * exp (c : ℤ)) * y := by rw [hm, one_mul]
    _ = exp (-(c : ℤ)) * (exp (c : ℤ) * y) := mul_assoc _ _ _
    _ ≤ exp (-(c : ℤ)) * 1 := mul_le_mul' le_rfl h1
    _ = exp (-(c : ℤ)) := mul_one _

end Rat

section Core
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x`.
-/
theorem vAlg' (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

/- English proof (translation)
The claim follows from `adAt_inclE F P _`.
-/
theorem adAt_ratA (P : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin n) E) (r s : Fin n) :
    adAt F P (((GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) :=
  adAt_inclE F P _

/- English proof (translation)
Establish `hq' : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ)`. Rewrite using `[← vAlg', map_natCast]`. Conclude with `hq`. Establish `e : x⁻¹ * GlobalTheory.TwU.ratA F (G g') = (x⁻¹ * GlobalTheory.TwU.ratA F (G g)) * GlobalTheory.TwU.ratA F (G (g⁻¹ * g'))`. Rewrite using `[mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel_left]`.

Rewrite `h` using `[hiff]`. Rewrite using `[hiff, e]`. Establish `hdc : exp (-(d : ℤ)) ≤ exp (-(c : ℤ))` using `by rw [exp_le_exp]; omega`. Establish `key` using `mul_cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) c ((adAt F P).mapMatrix ((x⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))) ((adAt F P).mapMatrix ((GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) : GL (Fin n) (AfE F E)) : Matrix (Fin …`. Introduce `r s`.

Use `key r s` as an intermediate fact. Rewrite `this` using `[← map_mul, ← Units.val_mul]`. Then use the resulting hypothesis. Use `show Valued.v (adAt F P _ - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ _`. Rewrite using `[adAt_ratA, hG]`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) r s)`.

Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Rewrite using `[h1, ← map_sub, vAlg']`. Apply the tactic sequence `exact val_entry P hq' c _ (congE_inv_mul P c g g' hg hC) r s`.
-/
theorem core (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = exp (-1 : ℤ))
    (hiff : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔
      ∀ r s, Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(N : ℤ)))
    (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (c d : ℕ) (hcd : c ≤ d) (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : GlobalTheory.TwU.CongAt P d (x⁻¹ * GlobalTheory.TwU.ratA F (G g))) (hC : CongE P c g' g) :
    GlobalTheory.TwU.CongAt P c (x⁻¹ * GlobalTheory.TwU.ratA F (G g')) := by
  have hq' : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ) := by
    rw [← vAlg', map_natCast]
    exact hq
  have e : x⁻¹ * GlobalTheory.TwU.ratA F (G g') = (x⁻¹ * GlobalTheory.TwU.ratA F (G g)) * GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) := by
    rw [mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hiff] at h
  rw [hiff, e]
  have hdc : exp (-(d : ℤ)) ≤ exp (-(c : ℤ)) := by rw [exp_le_exp]; omega
  have key := mul_cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) c
    ((adAt F P).mapMatrix ((x⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    ((adAt F P).mapMatrix ((GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    (fun r s => (h r s).trans hdc) (fun r s => ?_)
  · intro r s
    have := key r s
    rwa [← map_mul, ← Units.val_mul] at this
  · show Valued.v (adAt F P _ - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ _
    rw [adAt_ratA, hG]
    have h1 : (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) r s) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, ← map_sub, vAlg']
    exact val_entry P hq' c _ (congE_inv_mul P c g g' hg hC) r s

end Core

/- English proof (translation)
Introduce `B X I hI l Z a i fb dep dep' P κ g g' hg hdep hIn hC`. Unfold `GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn ⊢`. Take `⟨hseam, hq, -⟩` from `GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a 0 0 P 1`. Establish `hiff` using `fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a ((I.rec7 l Z).R.N i) N P z).2.2`. Rewrite `hIn`, `hiff`, the goal using `[hseam]`.

Establish `i1 : NumberField ↥(I.rec7 l Z).host.F` using `inferInstance`. Establish `i2 : NumberField (I.rec7 l Z).host.E` using `inferInstance`. Conclude with `@core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) (dep' P) (dep P) hdep _ g g' hg hIn hC`.
-/
theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  intro B X I hI l Z a i fb dep dep' P κ g g' hg hdep hIn hC
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn ⊢
  obtain ⟨hseam, hq, -⟩ := GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a 0 0 P 1
  have hiff := fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a ((I.rec7 l Z).R.N i) N P z).2.2
  rw [hseam] at hIn hiff ⊢
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact @core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) (dep' P) (dep P) hdep _ g g' hg hIn hC

end GlobalTheory.Mem.Col2.AdT.NearCong
