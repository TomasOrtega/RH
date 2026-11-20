import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkFiberStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open PositivityTheory.Rg.BcB.F.Tail.BS
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JacEigAt

/- English proof (translation)
Unfold `qV`. Conclude with `Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`.
-/
theorem qV_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qV E w := by
  unfold qV
  exact Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

/- English proof (translation)
Establish `h` using `GlobalTheory.LocLanglands.resCard_eq_normV w`. Simplify `h` using `[GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem card_residue_eq_qV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card 𝓀[w.adicCompletion E] = qV E w := by
  have h := GlobalTheory.LocLanglands.resCard_eq_normV w
  simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a` using `by ext; simp`. Establish `h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a` using `by ext; simp`. Establish `ha` using `a.2`. Simplify using `only [modExp, Fintype.card_unique, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, h1, h2, Fin.card_Ioi, Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers.
-/
theorem modExp_points (n : ℕ) (a : Fin n) :
    modExp (fun _ : Fin n => Unit) a = (n : ℤ) - 1 - 2 * (a : ℕ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have ha := a.2
  simp only [modExp, Fintype.card_unique, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, h1, h2,
    Fin.card_Ioi, Fin.card_Iio]
  omega

/- English proof (translation)
Establish `h1 : GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = GlobalTheory.SplitWeil.nabs k ϖ ^ m`. Simplify using `[GlobalTheory.SplitWeil.nabs]`. Rewrite using `[h1, GlobalTheory.LGrp.nabs_eq_zpow, h, _root_.zpow_neg, zpow_one, _root_.inv_zpow, _root_.zpow_neg]`.
-/
theorem nabs_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (h : ord k ϖ = 1) (m : ℤ) :
    GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) := by
  have h1 : GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = GlobalTheory.SplitWeil.nabs k ϖ ^ m := by
    simp [GlobalTheory.SplitWeil.nabs]
  rw [h1, GlobalTheory.LGrp.nabs_eq_zpow, h, _root_.zpow_neg, zpow_one, _root_.inv_zpow, _root_.zpow_neg]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]`.
-/
theorem prod_zpow_sum {ι : Type} (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, r ^ f a = r ^ ∑ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

/- English proof (translation)
Establish `hq : (0 : ℝ) < qV E w` using `by exact_mod_cast qV_pos w`. Use `set r : ℝ := Real.sqrt (qV E w : ℝ) with hr`. Establish `hr0 : 0 < r` using `Real.sqrt_pos.2 hq`. Establish `hrq : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = r ^ (2 : ℤ)`. Establish `: (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = qV E w`.

Simplify using `[GlobalTheory.SplitWeil.resCard, card_residue_eq_qV]`. Rewrite using `[this, hr, zpow_ofNat, Real.sq_sqrt hq.le]`. Establish `hs : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[hs, val_absPow_ofReal, nabs_zpow ϖ h, hrq, ← _root_.zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hr0.le]`. Establish `: (((2 * -m : ℤ) : ℝ)) * ((e : ℝ) / 2) = ((-(e * m) : ℤ) : ℝ)` using `by push_cast; ring`.

Rewrite using `[this, Real.rpow_intCast]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem absPow_term {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (e m : ℤ) :
    (absPow (w.adicCompletion E) ((e : ℂ) / 2) (ϖ ^ m) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (-(e * m)) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  set r : ℝ := Real.sqrt (qV E w : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hrq : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = r ^ (2 : ℤ) := by
    have : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = qV E w := by
      simp [GlobalTheory.SplitWeil.resCard, card_residue_eq_qV]
    rw [this, hr, zpow_ofNat, Real.sq_sqrt hq.le]
  have hs : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hs, val_absPow_ofReal, nabs_zpow ϖ h, hrq, ← _root_.zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hr0.le]
  have : (((2 * -m : ℤ) : ℝ)) * ((e : ℝ) / 2) = ((-(e * m) : ℤ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_intCast]
  push_cast
  rfl

/- English proof (translation)
Establish `hq : (0 : ℝ) < qV E w` using `by exact_mod_cast qV_pos w`. Establish `hr : (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ≠ 0`. Conclude with `(Real.sqrt_pos.2 hq).ne'` after adjusting the coercions. Establish `hd : ∀ i, GeneralLinearGroup.det (leviTorus (w.adicCompletion E) (Fin n) (fun i => ϖ ^ x i) i) = ϖ ^ x i` using `fun i => congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv fun i => ϖ ^ x i) i`. Rewrite using `[Units.val_inv_eq_inv_val, deltaHalf_apply, Units.coe_prod]`.

Simplify using `only [hd, absPow_term w ϖ h, modExp_points]`. Rewrite using `[prod_zpow_sum _ _ hr, ← _root_.zpow_neg, Finset.sum_neg_distrib, neg_neg]`.
-/
theorem deltaHalf_inv {E : Type} [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (x : Fin n → ℤ) :
    (((deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
        (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i))⁻¹ : ℂˣ) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hr : (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hd : ∀ i, GeneralLinearGroup.det
      (leviTorus (w.adicCompletion E) (Fin n) (fun i => ϖ ^ x i) i) = ϖ ^ x i :=
    fun i => congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv fun i => ϖ ^ x i) i
  rw [Units.val_inv_eq_inv_val, deltaHalf_apply, Units.coe_prod]
  simp only [hd, absPow_term w ϖ h, modExp_points]
  rw [prod_zpow_sum _ _ hr, ← _root_.zpow_neg, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.JacEigAt

open GlobalTheory.CompanionTheory.JacEigAt in
/- English proof (translation)
Introduce `E _ _ _ n w V _ _ π hπ ϖ hϖ ξ c x hx u hu heig`. Establish `hord : ord (w.adicCompletion E) ϖ = 1` using `(GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ`. Establish `h` using `GlobalTheory.T.jacquet_hecke_jacHk (w.adicCompletion E) n V π hπ ϖ hord x hx u hu`. Establish `hq : (0 : ℝ) < qV E w` using `by exact_mod_cast qV_pos w`. Establish `hqh : qh w ≠ 0`.

Unfold `qh`. Conclude with `(Real.sqrt_pos.2 hq).ne'` after adjusting the coercions. Establish `hcard : ((Nat.card 𝓀[w.adicCompletion E] : ℕ) : ℂ) = qh w ^ (2 : ℤ)`. Rewrite using `[card_residue_eq_qV, qh, zpow_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt hq.le]`. Simplify using the standard rewrite rules.

Use `set S : ℤ := ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i with hS`. Establish `h' : (Submodule.Quotient.mk (hkS π (iwGL n w) (dcos n w (tdiag ϖ x)) u) : Jacquet π (unipB (w.adicCompletion E) (Fin n))) = ((Nat.card 𝓀[w.adicCompletion E] : ℂ) ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)` using `h`. Rewrite `h'` using `[heig, Submodule.Quotient.mk_smul, hcard, ← _root_.zpow_mul]`. Establish `hj : jacB π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) = (qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)`. Use `jac_mk (points (Fin n)) π (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i) u` as an intermediate fact.

Rewrite `this` using `[deltaHalf_inv n w ϖ hord x]`. Conclude with `this`. Establish `e2 : qh w ^ (2 * S) = qh w ^ S * qh w ^ S`. Rewrite using `[two_mul, zpow_add₀ hqh]`. Establish `hS0 : qh w ^ S ≠ 0` using `zpow_ne_zero _ hqh`.

Rewrite `h'` using `[e2]`. Rewrite using `[hj]`. Establish `h3 : (qh w ^ S) • ((qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)) = (qh w ^ S) • ((c * pw ξ x) • (Submodule.Quotient.mk u : Jacquet π (unipB (w.adicCompletion E) (Fin n))))`. Rewrite using `[smul_smul, ← h', smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `smul_right_injective _ hS0 h3`.
-/
theorem GlobalTheory.CompanionTheory.JacEigAt.jacEig : JacEig := by
  intro E _ _ _ n w V _ _ π hπ ϖ hϖ ξ c x hx u hu heig
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  have h := GlobalTheory.T.jacquet_hecke_jacHk (w.adicCompletion E) n V π hπ ϖ hord x hx u hu
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hqh : qh w ≠ 0 := by
    unfold qh
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hcard : ((Nat.card 𝓀[w.adicCompletion E] : ℕ) : ℂ) = qh w ^ (2 : ℤ) := by
    rw [card_residue_eq_qV, qh, zpow_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt hq.le]
    simp
  set S : ℤ := ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i with hS
  have h' : (Submodule.Quotient.mk (hkS π (iwGL n w) (dcos n w (tdiag ϖ x)) u) :
      Jacquet π (unipB (w.adicCompletion E) (Fin n))) =
      ((Nat.card 𝓀[w.adicCompletion E] : ℂ) ^ S) •
        jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) := h
  rw [heig, Submodule.Quotient.mk_smul, hcard, ← _root_.zpow_mul] at h'
  have hj : jacB π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) =
      (qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) := by
    have := jac_mk (points (Fin n)) π (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i) u
    rw [deltaHalf_inv n w ϖ hord x] at this
    exact this
  have e2 : qh w ^ (2 * S) = qh w ^ S * qh w ^ S := by
    rw [two_mul, zpow_add₀ hqh]
  have hS0 : qh w ^ S ≠ 0 := zpow_ne_zero _ hqh
  rw [e2] at h'
  rw [hj]
  have h3 : (qh w ^ S) • ((qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)) =
      (qh w ^ S) • ((c * pw ξ x) • (Submodule.Quotient.mk u : Jacquet π (unipB (w.adicCompletion E) (Fin n)))) := by
    rw [smul_smul, ← h', smul_smul]
    congr 1
    ring
  exact smul_right_injective _ hS0 h3

end
