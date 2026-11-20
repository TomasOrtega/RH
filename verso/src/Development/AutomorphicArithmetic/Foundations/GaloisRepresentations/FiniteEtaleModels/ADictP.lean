import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory GlobalTheory.HeckeApprox

namespace UpperTheory.Gal.FiniteEtaleModels.SimilarityMultiplicityForm

variable {p : ℕ} [Fact p.Prime]

private def Mult (g : ℤ) (a : AfP p) : Prop := ∃ t : AfP p, IsIntAf t ∧ a = (g : AfP p) * t

/- English proof (translation)
Take `⟨s, hs, rfl⟩` from `ha`. Take `⟨t, ht, rfl⟩` from `hb`. Conclude with `⟨s + t, isInt_add hs ht, by rw [mul_add]⟩`.
-/
private theorem Mult.add {g : ℤ} {a b : AfP p} (ha : Mult g a) (hb : Mult g b) : Mult g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, isInt_add hs ht, by rw [mul_add]⟩

/- English proof (translation)
Use `⟨0, ?_, by rw [mul_zero]⟩` and prove the remaining obligations. Simplify using `using isInt_natCast (p := p) 0`.
-/
private theorem Mult.zero (g : ℤ) : Mult g (0 : AfP p) := by
  refine ⟨0, ?_, by rw [mul_zero]⟩
  simpa using isInt_natCast (p := p) 0

/- English proof (translation)
Take `⟨t, ht, rfl⟩` from `ha`. Use `⟨-t, ?_, by rw [mul_neg]⟩` and prove the remaining obligations. Simplify using `using isInt_sub (isInt_natCast (p := p) 0) ht`.
-/
private theorem Mult.neg {g : ℤ} {a : AfP p} (ha : Mult g a) : Mult g (-a) := by
  obtain ⟨t, ht, rfl⟩ := ha
  refine ⟨-t, ?_, by rw [mul_neg]⟩
  simpa using isInt_sub (isInt_natCast (p := p) 0) ht

/- English proof (translation)
Establish `gen : ∀ (a b : AfP p) (x y : D.La), IsIntAf a → IsIntAf b → Mult g (fAf D (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) (b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y)))`. Introduce `a b x y ha hb`. Take `⟨k, hk⟩` from `hg x y`. Use `⟨a * b * k, isInt_mul (isInt_mul ha hb) (isInt_intCast k), ?_⟩` and prove the remaining obligations. Establish `e1 : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x`.

Rewrite using `[inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Establish `e2 : b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = b • inAf D y`. Rewrite using `[inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[e1, e2, LinearMap.map_smul₂, LinearMap.map_smul, form_inAf, hk]`. Use `push_cast`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `step : ∀ (b : AfP p) (y : D.La), IsIntAf b → ∀ u ∈ LaHat D, Mult g (fAf D u (b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y)))`. Introduce `b y hb u hu`. Unfold `LaHat at hu`.

Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, x, ha, rfl⟩` from `hz`. Conclude with `gen a b x y ha hb`. Consider the case `zero`.

Simplify using `using Mult.zero (p := p) g`. Consider the case `add z z' _ _ h1 h2`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `Mult.add h1 h2`. Consider the case `neg z _ h`.

Rewrite using `[map_neg, LinearMap.neg_apply]`. Conclude with `Mult.neg h`. Unfold `LaHat at hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨b, y, hb, rfl⟩` from `hz`. Conclude with `step b y hb v hv`. Consider the case `zero`. Simplify using `using Mult.zero (p := p) g`. Consider the case `add z z' _ _ h1 h2`.

Rewrite using `[map_add]`. Conclude with `Mult.add h1 h2`. Consider the case `neg z _ h`. Rewrite using `[map_neg]`. Conclude with `Mult.neg h`.
-/
private theorem mult_form (D : Datum p) (g : ℤ) (hg : ∀ x y, g ∣ D.EF x y) {v w : AfP p ⊗[ℚ] VQ D}
    (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : Mult g (fAf D v w) := by
  have gen : ∀ (a b : AfP p) (x y : D.La), IsIntAf a → IsIntAf b →
      Mult g (fAf D (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) (b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y))) := by
    intro a b x y ha hb
    obtain ⟨k, hk⟩ := hg x y
    refine ⟨a * b * k, isInt_mul (isInt_mul ha hb) (isInt_intCast k), ?_⟩
    have e1 : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    have e2 : b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = b • inAf D y := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e1, e2, LinearMap.map_smul₂, LinearMap.map_smul, form_inAf, hk]
    push_cast
    simp only [smul_eq_mul]
    ring
  have step : ∀ (b : AfP p) (y : D.La), IsIntAf b → ∀ u ∈ LaHat D,
      Mult g (fAf D u (b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y))) := by
    intro b y hb u hu
    unfold LaHat at hu
    induction hu using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      exact gen a b x y ha hb
    | zero =>
      simpa using Mult.zero (p := p) g
    | add z z' _ _ h1 h2 =>
      rw [map_add, LinearMap.add_apply]
      exact Mult.add h1 h2
    | neg z _ h =>
      rw [map_neg, LinearMap.neg_apply]
      exact Mult.neg h
  unfold LaHat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, y, hb, rfl⟩ := hz
    exact step b y hb v hv
  | zero =>
    simpa using Mult.zero (p := p) g
  | add z z' _ _ h1 h2 =>
    rw [map_add]
    exact Mult.add h1 h2
  | neg z _ h =>
    rw [map_neg]
    exact Mult.neg h

/- English proof (translation)
Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Establish `hrank : 0 < Module.finrank ℤ D.La`. Rewrite using `[D.rankLa]`. Conclude with `Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos`.

Use `haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos hrank`. Take `⟨x, hx⟩` from `exists_ne (0 : D.La)`. Establish `hne : D.EF x ≠ 0` using `fun h => hx (D.nondeg (by rw [h, map_zero]))`. Take `⟨y, hy⟩` from `DFunLike.ne_iff.mp hne`. Conclude with `⟨x, y, by simpa using hy⟩`.
-/
private theorem form_ne (D : Datum p) : ∃ x y, D.EF x y ≠ 0 := by
  haveI := D.freeLa
  haveI := D.finLa
  have hrank : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos
  haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have hne : D.EF x ≠ 0 := fun h => hx (D.nondeg (by rw [h, map_zero]))
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, y, by simpa using hy⟩

/- English proof (translation)
Set `I : Ideal ℤ` to `Ideal.span {z | ∃ x y, D.EF x y = z}`. Set `g : ℤ` to `Submodule.IsPrincipal.generator I`. Establish `hI : Ideal.span {g} = I` using `Ideal.span_singleton_generator I`. Establish `hg : ∀ x y, g ∣ D.EF x y`. Introduce `x y`.

Establish `h : D.EF x y ∈ I` using `Ideal.subset_span ⟨x, y, rfl⟩`. Rewrite `h` using `[← hI, Ideal.mem_span_singleton]`. Conclude with `h`. Establish `hg0 : g ≠ 0`. Introduce `h0`.

Take `⟨x, y, hxy⟩` from `form_ne D`. Establish `h` using `hg x y`. Rewrite `h` using `[h0, zero_dvd_iff]`. Conclude with `hxy h`. Establish `hP : ∀ z ∈ I, Mult g (mu * (z : AfP p))`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, y, rfl⟩` from `hz`. Rewrite using `[← form_inAf, ← hsim]`.

Conclude with `mult_form D g hg (hint _ (inAf_mem D x)) (hint _ (inAf_mem D y))`. Consider the case `zero`. Simplify using `using Mult.zero (p := p) g`. Consider the case `add a b _ _ ha hb`. Rewrite using `[Int.cast_add, mul_add]`.

Conclude with `Mult.add ha hb`. Consider the case `smul k a _ ha`. Take `⟨t, ht, he⟩` from `ha`. Use `⟨k * t, isInt_mul (isInt_intCast k) ht, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, Int.cast_mul, mul_left_comm, he]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht, he⟩` from `hP g (Submodule.IsPrincipal.generator_mem I)`. Establish `hu : IsUnit (g : AfP p)`. Establish `hq : IsUnit (algebraMap ℚ (AfP p) (g : ℚ))` using `(isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)).map _`. Simplify using `using hq`.

Establish `hmt : mu = t` using `hu.mul_left_cancel (by rw [mul_comm (g : AfP p) mu, he])`. Rewrite using `[hmt]`. Conclude with `ht`.
-/
private theorem int_of_sim (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (mu : AfP p)
    (hint : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D) (hsim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w) : IsIntAf mu := by
  let I : Ideal ℤ := Ideal.span {z | ∃ x y, D.EF x y = z}
  let g : ℤ := Submodule.IsPrincipal.generator I
  have hI : Ideal.span {g} = I := Ideal.span_singleton_generator I
  have hg : ∀ x y, g ∣ D.EF x y := by
    intro x y
    have h : D.EF x y ∈ I := Ideal.subset_span ⟨x, y, rfl⟩
    rw [← hI, Ideal.mem_span_singleton] at h
    exact h
  have hg0 : g ≠ 0 := by
    intro h0
    obtain ⟨x, y, hxy⟩ := form_ne D
    have h := hg x y
    rw [h0, zero_dvd_iff] at h
    exact hxy h
  have hP : ∀ z ∈ I, Mult g (mu * (z : AfP p)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      rw [← form_inAf, ← hsim]
      exact mult_form D g hg (hint _ (inAf_mem D x)) (hint _ (inAf_mem D y))
    | zero =>
      simpa using Mult.zero (p := p) g
    | add a b _ _ ha hb =>
      rw [Int.cast_add, mul_add]
      exact Mult.add ha hb
    | smul k a _ ha =>
      obtain ⟨t, ht, he⟩ := ha
      refine ⟨k * t, isInt_mul (isInt_intCast k) ht, ?_⟩
      rw [smul_eq_mul, Int.cast_mul, mul_left_comm, he]
      ring
  obtain ⟨t, ht, he⟩ := hP g (Submodule.IsPrincipal.generator_mem I)
  have hu : IsUnit (g : AfP p) := by
    have hq : IsUnit (algebraMap ℚ (AfP p) (g : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)).map _
    simpa using hq
  have hmt : mu = t := hu.mul_left_cancel (by rw [mul_comm (g : AfP p) mu, he])
  rw [hmt]
  exact ht

end UpperTheory.Gal.FiniteEtaleModels.SimilarityMultiplicityForm

open UpperTheory.Gal.FiniteEtaleModels.SimilarityMultiplicityForm in
/- English proof (translation)
Introduce `hMU p _ D G L h κ c' hκ hκp hc' hI hpre hsim`. Take `⟨_, hMU2⟩` from `hMU p D G L`. Take `⟨t, t', ht, ht', htt, hct⟩` from `hsim`. Set `h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)` to `κ • L.actG h⁻¹`. Establish `hinv : ∀ v, L.actG h⁻¹ (L.actG h v) = v`.

Introduce `v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `hint : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D`. Introduce `v hv`. Take `⟨v', hv', he⟩` from `hpre v hv`.

Establish `e : h₀ v = v'`. Simplify using `only [h₀, LinearMap.smul_apply]`. Rewrite using `[← map_nsmul, ← he, hinv]`. Rewrite using `[e]`. Conclude with `hv'`.

Take `⟨f, hf⟩` from `T.lattice_endomorphism_integral_approximation p D h₀ hint`. Establish `hs0` using `T.harrisTaylor_action_form_eq_similitude_mul p D G L h⁻¹`. Establish `hone : ((h⁻¹ : G.GAf).val.2 : AfP p) * (h.val.2 : AfP p) = 1` using `by simp`. Set `mu : AfP p` to `(κ : AfP p) ^ 2 * ((h⁻¹ : G.GAf).val.2 : AfP p)`. Establish `hsim0 : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w`.

Introduce `v w`. Simplify using `only [h₀, LinearMap.smul_apply, mu]`. Rewrite using `[map_nsmul, map_nsmul, LinearMap.smul_apply]`. Simplify using `only [fAf]`. Rewrite using `[hs0]`.

Simplify using `only [nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmu : IsIntAf mu` using `int_of_sim D h₀ mu hint hsim0`. Establish `hprod : mu * ((c' : AfP p) * t) = ((κ ^ 2 : ℕ) : AfP p)`. Rewrite using `[← hct]`.

Simplify using `only [mu]`. Rewrite using `[_root_.mul_assoc, hone, _root_.mul_one]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨c, ε, ε', hcp, _, hε, hε', hεε, hmuc⟩` from `T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ((c' : AfP p) * t) (κ ^ 2) (pow_pos hκ 2) (Nat.Coprime.pow_left 2 hκp) hmu (isInt_mul (isInt_natCast c') ht) hprod`.

Establish `hcc : κ ^ 2 = c * c'`. Use `hMU2 (κ ^ 2) (c * c') (ε * t) (ε' * t') (Nat.Coprime.pow_left 2 hκp) (Nat.Coprime.mul hcp hc') (isInt_mul hε ht) (isInt_mul hε' ht') ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hprod, hmuc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcomm : ∀ (a : D.O) v, h₀ (actAf D a v) = actAf D a (h₀ v)`. Introduce `a v`. Simplify using `only [h₀, LinearMap.smul_apply]`. Rewrite using `[actG_actAf, map_nsmul]`.

Establish `hlin : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, (f n) (a • x) = a • (f n) x + n • z`. Introduce `n hn hnp a x`. Take `⟨w1, hw1, he1⟩` from `hf n hn hnp (a • x)`. Take `⟨w2, hw2, he2⟩` from `hf n hn hnp x`. Establish `key : inAf D ((f n) (a • x) - a • (f n) x) = n • (actAf D a w2 - w1)`.

Rewrite using `[inAf_sub, ← actAf_inAf, smul_sub]`. Establish `e3 : inAf D ((f n) (a • x)) = actAf D a (h₀ (inAf D x)) - n • w1`. Rewrite using `[← hcomm, actAf_inAf, he1, add_sub_cancel_right]`. Rewrite using `[e3, he2, map_add, map_nsmul]`. Normalize the expressions using the abelian group laws.

Establish `hmem : actAf D a w2 - w1 ∈ LaHat D` using `(LaHat D).sub_mem (actAf_mem_laHat D a hw2) hw1`. Take `⟨z, hz⟩` from `LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key`. Conclude with `⟨z, by rw [← hz, add_sub_cancel]⟩`. Establish `hcompat : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x : D.La, ∃ z, (f (n * m)) x = (f n) x + n • z`. Introduce `n m hn hm hnmp x`.

Establish `hnp : n.Coprime p` using `Nat.Coprime.coprime_mul_right hnmp`. Take `⟨w1, hw1, he1⟩` from `hf (n * m) (Nat.mul_pos hn hm) hnmp x`. Take `⟨w2, hw2, he2⟩` from `hf n hn hnp x`. Establish `key : inAf D ((f (n * m)) x - (f n) x) = n • (w2 - m • w1)`. Establish `e3 : inAf D ((f (n * m)) x) = inAf D ((f n) x) + n • w2 - (n * m) • w1`.

Rewrite using `[← he2, he1, add_sub_cancel_right]`. Rewrite using `[inAf_sub, e3, smul_sub, ← mul_smul]`. Normalize the expressions using the abelian group laws. Establish `hmem : w2 - m • w1 ∈ LaHat D` using `(LaHat D).sub_mem hw2 ((LaHat D).nsmul_mem hw1 m)`. Take `⟨z, hz⟩` from `LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key`.

Conclude with `⟨z, by rw [← hz, add_sub_cancel]⟩`. Take `⟨u, hu1, hu2⟩` from `T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε`. Establish `hform : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La, (n : ℤ) ∣ D.EF ((f n) x) ((f n) y) - c * u n * D.EF x y`. Introduce `n hn hnp x y`. Take `⟨_, β, hβ, hεβ⟩` from `hu2 n hn hnp`.

Take `⟨w1, hw1, he1⟩` from `hf n hn hnp x`. Take `⟨w2, hw2, he2⟩` from `hf n hn hnp y`. Establish `ex : inAf D ((f n) x) = h₀ (inAf D x) - n • w1` using `by rw [he1, add_sub_cancel_right]`. Establish `ey : inAf D ((f n) y) = h₀ (inAf D y) - n • w2` using `by rw [he2, add_sub_cancel_right]`. Establish `hA` using `formInt_laHat p D _ _ (hint _ (inAf_mem D x)) hw2`.

Establish `hB` using `formInt_laHat p D _ _ hw1 (hint _ (inAf_mem D y))`. Establish `hC` using `formInt_laHat p D _ _ hw1 hw2`. Use `IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _ ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w2 - fAf D w1 (h₀ (inAf D y)) + (n : AfP p) * fAf D w1 w2) (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _)) hA) hB) (isInt_mul ( …` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← form_inAf D ((f n) x) ((f n) y), ← form_inAf D x y, ex, ey]`.

Simplify using `only [map_sub, LinearMap.sub_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Rewrite using `[hsim0, hmuc, hεβ]`. Expand and normalize the polynomial expressions, which then agree. Use `clear hs0 hone hpre hMU2 htt hprod`. Use `⟨f, u, c, hcc.symm, ?_, ?_⟩` and prove the remaining obligations.

Establish `hIh : ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D` using `hI`. Use `⟨hlin, fun n m hn hm hnm => ⟨hcompat n m hn hm hnm, hu1 n m hn hm hnm⟩, fun n hn hnp => ⟨(hu2 n hn hnp).1, hform n hn hnp⟩, ?_⟩` and prove the remaining obligations. Introduce `n hn hnp x`. Express the relevant statement in the definitionally equal form `D.La at x`. Take `⟨y, w, hw, hyw⟩` from `exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hIh _ (inAf_mem D x))`.

Take `⟨w', hw', he'⟩` from `hf n hn hnp y`. Establish `hh : h₀ (L.actG h (inAf D x)) = κ • inAf D x`. Simplify using `only [h₀, LinearMap.smul_apply]`. Rewrite using `[hinv]`. Rewrite `hh` using `[hyw, map_add, map_nsmul, he']`.

Establish `key : inAf D ((f n) y - κ • x) = n • (-(w' + h₀ w))`. Rewrite using `[inAf_sub, inAf_nsmul, ← hh, smul_neg, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hmem : -(w' + h₀ w) ∈ LaHat D` using `(LaHat D).neg_mem ((LaHat D).add_mem hw' (hint w hw))`. Take `⟨z, hz⟩` from `LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key`.

Conclude with `⟨y, z, eq_add_of_sub_eq' hz⟩`. Introduce `n hn hnp x`. Take `⟨w, hw, he⟩` from `hf n hn hnp x`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← he]`.

Simplify using `only [h₀, LinearMap.smul_apply]`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.dictP_holds :
    MultUnit → DictP := by
  intro hMU p _ D G L h κ c' hκ hκp hc' hI hpre hsim
  obtain ⟨_, hMU2⟩ := hMU p D G L
  obtain ⟨t, t', ht, ht', htt, hct⟩ := hsim
  let h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := κ • L.actG h⁻¹
  have hinv : ∀ v, L.actG h⁻¹ (L.actG h v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hint : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := by
    intro v hv
    obtain ⟨v', hv', he⟩ := hpre v hv
    have e : h₀ v = v' := by
      simp only [h₀, LinearMap.smul_apply]
      rw [← map_nsmul, ← he, hinv]
    rw [e]
    exact hv'
  obtain ⟨f, hf⟩ := T.lattice_endomorphism_integral_approximation p D h₀ hint
  have hs0 := T.harrisTaylor_action_form_eq_similitude_mul p D G L h⁻¹
  have hone : ((h⁻¹ : G.GAf).val.2 : AfP p) * (h.val.2 : AfP p) = 1 := by simp
  let mu : AfP p := (κ : AfP p) ^ 2 * ((h⁻¹ : G.GAf).val.2 : AfP p)
  have hsim0 : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w := by
    intro v w
    simp only [h₀, LinearMap.smul_apply, mu]
    rw [map_nsmul, map_nsmul, LinearMap.smul_apply]
    dsimp only [fAf]
    rw [hs0]
    simp only [nsmul_eq_mul]
    ring
  have hmu : IsIntAf mu := int_of_sim D h₀ mu hint hsim0
  have hprod : mu * ((c' : AfP p) * t) = ((κ ^ 2 : ℕ) : AfP p) := by
    rw [← hct]
    simp only [mu]
    rw [_root_.mul_assoc, hone, _root_.mul_one]
    push_cast
    rfl
  obtain ⟨c, ε, ε', hcp, _, hε, hε', hεε, hmuc⟩ :=
    T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ((c' : AfP p) * t) (κ ^ 2) (pow_pos hκ 2) (Nat.Coprime.pow_left 2 hκp) hmu
      (isInt_mul (isInt_natCast c') ht) hprod
  have hcc : κ ^ 2 = c * c' := by
    refine hMU2 (κ ^ 2) (c * c') (ε * t) (ε' * t') (Nat.Coprime.pow_left 2 hκp)
      (Nat.Coprime.mul hcp hc') (isInt_mul hε ht) (isInt_mul hε' ht') ?_ ?_
    · calc ε * t * (ε' * t') = (ε * ε') * (t * t') := by ring
        _ = 1 := by rw [hεε, htt, _root_.mul_one]
    · rw [← hprod, hmuc]
      push_cast
      ring
  have hcomm : ∀ (a : D.O) v, h₀ (actAf D a v) = actAf D a (h₀ v) := by
    intro a v
    simp only [h₀, LinearMap.smul_apply]
    rw [actG_actAf, map_nsmul]
  have hlin : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, (f n) (a • x) = a • (f n) x + n • z := by
    intro n hn hnp a x
    obtain ⟨w1, hw1, he1⟩ := hf n hn hnp (a • x)
    obtain ⟨w2, hw2, he2⟩ := hf n hn hnp x
    have key : inAf D ((f n) (a • x) - a • (f n) x) = n • (actAf D a w2 - w1) := by
      rw [inAf_sub, ← actAf_inAf, smul_sub]
      have e3 : inAf D ((f n) (a • x)) = actAf D a (h₀ (inAf D x)) - n • w1 := by
        rw [← hcomm, actAf_inAf, he1, add_sub_cancel_right]
      rw [e3, he2, map_add, map_nsmul]
      abel
    have hmem : actAf D a w2 - w1 ∈ LaHat D := (LaHat D).sub_mem (actAf_mem_laHat D a hw2) hw1
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  have hcompat : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x : D.La, ∃ z, (f (n * m)) x = (f n) x + n • z := by
    intro n m hn hm hnmp x
    have hnp : n.Coprime p := Nat.Coprime.coprime_mul_right hnmp
    obtain ⟨w1, hw1, he1⟩ := hf (n * m) (Nat.mul_pos hn hm) hnmp x
    obtain ⟨w2, hw2, he2⟩ := hf n hn hnp x
    have key : inAf D ((f (n * m)) x - (f n) x) = n • (w2 - m • w1) := by
      have e3 : inAf D ((f (n * m)) x) = inAf D ((f n) x) + n • w2 - (n * m) • w1 := by
        rw [← he2, he1, add_sub_cancel_right]
      rw [inAf_sub, e3, smul_sub, ← mul_smul]
      abel
    have hmem : w2 - m • w1 ∈ LaHat D := (LaHat D).sub_mem hw2 ((LaHat D).nsmul_mem hw1 m)
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  obtain ⟨u, hu1, hu2⟩ := T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε
  have hform : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La, (n : ℤ) ∣ D.EF ((f n) x) ((f n) y) - c * u n * D.EF x y := by
    intro n hn hnp x y
    obtain ⟨_, β, hβ, hεβ⟩ := hu2 n hn hnp
    obtain ⟨w1, hw1, he1⟩ := hf n hn hnp x
    obtain ⟨w2, hw2, he2⟩ := hf n hn hnp y
    have ex : inAf D ((f n) x) = h₀ (inAf D x) - n • w1 := by rw [he1, add_sub_cancel_right]
    have ey : inAf D ((f n) y) = h₀ (inAf D y) - n • w2 := by rw [he2, add_sub_cancel_right]
    have hA := formInt_laHat p D _ _ (hint _ (inAf_mem D x)) hw2
    have hB := formInt_laHat p D _ _ hw1 (hint _ (inAf_mem D y))
    have hC := formInt_laHat p D _ _ hw1 hw2
    refine IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _
      ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w2 - fAf D w1 (h₀ (inAf D y))
        + (n : AfP p) * fAf D w1 w2)
      (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _)) hA) hB)
        (isInt_mul (isInt_natCast n) hC)) ?_
    push_cast
    rw [← form_inAf D ((f n) x) ((f n) y), ← form_inAf D x y, ex, ey]
    simp only [map_sub, LinearMap.sub_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    rw [hsim0, hmuc, hεβ]
    ring
  clear hs0 hone hpre hMU2 htt hprod
  refine ⟨f, u, c, hcc.symm, ?_, ?_⟩
  · have hIh : ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D := hI
    refine ⟨hlin, fun n m hn hm hnm => ⟨hcompat n m hn hm hnm, hu1 n m hn hm hnm⟩,
      fun n hn hnp => ⟨(hu2 n hn hnp).1, hform n hn hnp⟩, ?_⟩
    intro n hn hnp x
    change D.La at x
    obtain ⟨y, w, hw, hyw⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hIh _ (inAf_mem D x))
    obtain ⟨w', hw', he'⟩ := hf n hn hnp y
    have hh : h₀ (L.actG h (inAf D x)) = κ • inAf D x := by
      simp only [h₀, LinearMap.smul_apply]
      rw [hinv]
    rw [hyw, map_add, map_nsmul, he'] at hh
    have key : inAf D ((f n) y - κ • x) = n • (-(w' + h₀ w)) := by
      rw [inAf_sub, inAf_nsmul, ← hh, smul_neg, smul_add]
      abel
    have hmem : -(w' + h₀ w) ∈ LaHat D := (LaHat D).neg_mem ((LaHat D).add_mem hw' (hint w hw))
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key
    exact ⟨y, z, eq_add_of_sub_eq' hz⟩
  · intro n hn hnp x
    obtain ⟨w, hw, he⟩ := hf n hn hnp x
    refine ⟨w, hw, ?_⟩
    rw [← he]
    simp only [h₀, LinearMap.smul_apply]

end
