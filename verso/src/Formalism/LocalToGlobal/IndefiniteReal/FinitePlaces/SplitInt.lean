import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `heps : e * phiE w 1 = e` using `by rw [← hs, mul_add, h1, h2, add_zero]`. Establish `hcc : cA D e * cA D e = cA D e` using `by rw [← map_mul, h1]`. Take `⟨u, hu0⟩ : ∃ u : AE D, u = incA D D.host.sqrtMinusD` from `⟨_, rfl⟩`. Establish `hadj0 : star D.host.sqrtMinusD ≠ D.host.sqrtMinusD`. Rewrite using `[star_sqrt]`.

Introduce `h`. Establish `: D.host.sqrtMinusD = 0` using `by linear_combination -h / 2`. Conclude with `Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero D.host this`. Establish `ht0 : algebraMap D.host.F D.host.E 0 = D.host.sqrtMinusD + star D.host.sqrtMinusD` using `by rw [star_sqrt]; simp`. Establish `hN0 : algebraMap D.host.F D.host.E (D.host.d : D.host.F) = D.host.sqrtMinusD * star D.host.sqrtMinusD`.

Rewrite using `[star_sqrt, mul_neg, sqrt_sq, neg_neg, map_natCast]`. Establish `hadj` using `adjoin_top_of D.host.sqrtMinusD 0 (D.host.d : D.host.F) ht0 hN0 hadj0`. Establish `hinj : Function.Injective (algebraMap (AF D.host.F) (AE D))`. Introduce `x y h`. Apply `Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F) (B := D.host.E) (FaithfulSMul.algebraMap_injective D.host.F D.host.E)` to reduce the goal to its premises.

Rewrite `h` using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply]`. Conclude with `h`. Take `⟨a, ha0⟩ : ∃ a : AE D, a = e - cA D e` from `⟨_, rfl⟩`. Establish `hca : cA D a = -a` using `by rw [ha0, map_sub, cA_cA]; ring`. Establish `hcu : cA D u = -u` using `by rw [hu0, cA_incA, star_sqrt, map_neg]`.

Take `⟨r, hr⟩` from `fixed_AE hadj (z := a * u) (by rw [map_mul, hca, hcu]; ring)`. Establish `haa : a * a = phiE w 1`. Rewrite using `[ha0, ← hs]`. Take the linear combination `h1 + hcc - 2 * h2`. Establish `hu2 : u * u = algebraMap D.host.F (AE D) (-(D.host.d : D.host.F))`.

Rewrite using `[hu0, ← map_mul, sqrt_sq, show -(D.host.d : D.host.E) = algebraMap D.host.F D.host.E (-(D.host.d : D.host.F)) by simp, incA_alg]`. Establish `hrr : r * r = sA w (algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) * 1)`. Apply `hinj` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Take `⟨s, hsdef⟩ : ∃ s, s = evalV D.host.F w (sndA D.host.F r)` from `⟨_, rfl⟩`.

Establish `hss : s * s = algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F))`. Use `congrArg (fun x : AF D.host.F => evalV D.host.F w (sndA D.host.F x)) hrr` as an intermediate fact. Simplify using `only [map_mul, mul_one] at this`. Rewrite using `[hsdef]`. Conclude with `this.trans (sglV_same w _)`.

Establish `hroot : s ^ 2 - ((0 : D.host.F) : w.adicCompletion D.host.F) * s + ((D.host.d : D.host.F) : w.adicCompletion D.host.F) = 0`. Rewrite using `[← algebraMap_adic_eq, ← algebraMap_adic_eq, map_zero, sq, hss, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ι, hι, -⟩` from `emb_exists w D.host.sqrtMinusD 0 (D.host.d : D.host.F) ht0 hN0 hadj0 s hroot`. Conclude with `⟨s, ι, hss, hι⟩`.
-/
theorem split_emb {w : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    (hs : e + cA D e = phiE w 1) :
    ∃ (s : w.adicCompletion D.host.F) (ι : D.host.E →ₐ[D.host.F] w.adicCompletion D.host.F),
      s * s = algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) ∧ ι D.host.sqrtMinusD = s := by
  have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  obtain ⟨u, hu0⟩ : ∃ u : AE D, u = incA D D.host.sqrtMinusD := ⟨_, rfl⟩
  have hadj0 : star D.host.sqrtMinusD ≠ D.host.sqrtMinusD := by
    rw [star_sqrt]; intro h
    have : D.host.sqrtMinusD = 0 := by linear_combination -h / 2
    exact Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero D.host this
  have ht0 : algebraMap D.host.F D.host.E 0 = D.host.sqrtMinusD + star D.host.sqrtMinusD := by rw [star_sqrt]; simp
  have hN0 : algebraMap D.host.F D.host.E (D.host.d : D.host.F) = D.host.sqrtMinusD * star D.host.sqrtMinusD := by
    rw [star_sqrt, mul_neg, sqrt_sq, neg_neg, map_natCast]
  have hadj := adjoin_top_of D.host.sqrtMinusD 0 (D.host.d : D.host.F) ht0 hN0 hadj0
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) := by
    intro x y h
    apply Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (FaithfulSMul.algebraMap_injective D.host.F D.host.E)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply] at h
    exact h
  obtain ⟨a, ha0⟩ : ∃ a : AE D, a = e - cA D e := ⟨_, rfl⟩
  have hca : cA D a = -a := by rw [ha0, map_sub, cA_cA]; ring
  have hcu : cA D u = -u := by rw [hu0, cA_incA, star_sqrt, map_neg]
  obtain ⟨r, hr⟩ := fixed_AE hadj (z := a * u) (by rw [map_mul, hca, hcu]; ring)
  have haa : a * a = phiE w 1 := by
    rw [ha0, ← hs]; linear_combination h1 + hcc - 2 * h2
  have hu2 : u * u = algebraMap D.host.F (AE D) (-(D.host.d : D.host.F)) := by
    rw [hu0, ← map_mul, sqrt_sq, show -(D.host.d : D.host.E) = algebraMap D.host.F D.host.E (-(D.host.d : D.host.F)) by simp,
      incA_alg]
  have hrr : r * r = sA w (algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) * 1) := by
    apply hinj
    calc algebraMap (AF D.host.F) (AE D) (r * r) = (a * u) * (a * u) := by rw [map_mul, ← hr]
      _ = (a * a) * (u * u) := by ring
      _ = algebraMap D.host.F (AE D) (-(D.host.d : D.host.F)) * phiE w 1 := by rw [haa, hu2]; ring
      _ = phiE w (algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) * 1) := phiE_smul w _ 1
  obtain ⟨s, hsdef⟩ : ∃ s, s = evalV D.host.F w (sndA D.host.F r) := ⟨_, rfl⟩
  have hss : s * s = algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) := by
    have := congrArg (fun x : AF D.host.F => evalV D.host.F w (sndA D.host.F x)) hrr
    simp only [map_mul, mul_one] at this
    rw [hsdef]; exact this.trans (sglV_same w _)
  have hroot : s ^ 2 - ((0 : D.host.F) : w.adicCompletion D.host.F) * s +
      ((D.host.d : D.host.F) : w.adicCompletion D.host.F) = 0 := by
    rw [← algebraMap_adic_eq, ← algebraMap_adic_eq, map_zero, sq, hss, map_neg]; ring
  obtain ⟨ι, hι, -⟩ := emb_exists w D.host.sqrtMinusD 0 (D.host.d : D.host.F) ht0 hN0 hadj0 s hroot
  exact ⟨s, ι, hss, hι⟩

def valIdeal {w : HeightOneSpectrum (𝓞 D.host.F)} (ι : D.host.E →ₐ[D.host.F] w.adicCompletion D.host.F) :
    Ideal (𝓞 D.host.E) where
  carrier := {x | Valued.v (ι (x : D.host.E)) < 1}
  add_mem' := fun {x y} hx hy => by
    show Valued.v (ι ((x + y : 𝓞 D.host.E) : D.host.E)) < 1
    rw [show ((x + y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) + (y : D.host.E) from rfl, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  zero_mem' := by
    show Valued.v (ι ((0 : 𝓞 D.host.E) : D.host.E)) < 1
    rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, Valuation.map_zero]; exact zero_lt_one
  smul_mem' := fun c {x} hx => by
    show Valued.v (ι ((c • x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [show ((c • x : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * (x : D.host.E) from rfl, map_mul, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (val_emb_le w ι c)) hx

/- English proof (translation)
Introduce `h`. Establish `h1 : (1 : 𝓞 D.host.E) ∈ valIdeal ι` using `h ▸ Submodule.mem_top`. Express the relevant statement in the definitionally equal form `Valued.v (ι ((1 : 𝓞 D.host.E) : D.host.E)) < 1 at h1`. Rewrite `h1` using `[show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, map_one, Valuation.map_one]`. Conclude with `lt_irrefl _ h1`.

Use the proof step `mem_or_mem' := by`. Introduce `x y hxy`. Express the relevant statement in the definitionally equal form `Valued.v (ι ((x * y : 𝓞 D.host.E) : D.host.E)) < 1 at hxy`. Rewrite `hxy` using `[show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * (y : D.host.E) from rfl, map_mul, Valuation.map_mul]`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Take `⟨hx, hy⟩` from `hc`. Express the relevant statement in the definitionally equal form `¬ Valued.v (ι (x : D.host.E)) < 1 at hx`. Express the relevant statement in the definitionally equal form `¬ Valued.v (ι (y : D.host.E)) < 1 at hy`. Use `push Not at hx hy`.

Conclude with `absurd hxy (not_lt.2 (one_le_mul hx hy))`.
-/
theorem valIdeal_prime {w : HeightOneSpectrum (𝓞 D.host.F)} (ι : D.host.E →ₐ[D.host.F] w.adicCompletion D.host.F) :
    (valIdeal ι).IsPrime where
  ne_top' := by
    intro h
    have h1 : (1 : 𝓞 D.host.E) ∈ valIdeal ι := h ▸ Submodule.mem_top
    change Valued.v (ι ((1 : 𝓞 D.host.E) : D.host.E)) < 1 at h1
    rw [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, map_one, Valuation.map_one] at h1
    exact lt_irrefl _ h1
  mem_or_mem' := by
    intro x y hxy
    change Valued.v (ι ((x * y : 𝓞 D.host.E) : D.host.E)) < 1 at hxy
    rw [show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * (y : D.host.E) from rfl, map_mul,
      Valuation.map_mul] at hxy
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    change ¬ Valued.v (ι (x : D.host.E)) < 1 at hx
    change ¬ Valued.v (ι (y : D.host.E)) < 1 at hy
    push Not at hx hy
    exact absurd hxy (not_lt.2 (one_le_mul hx hy))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Valued.v (ι ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E)) < 1`. Rewrite using `[algebraMap_O, AlgHom.commutes]`. Conclude with `(val_coe_lt_one_iff w f).2 hf`.
-/
theorem algebraMap_mem_valIdeal {w : HeightOneSpectrum (𝓞 D.host.F)}
    (ι : D.host.E →ₐ[D.host.F] w.adicCompletion D.host.F) {f : 𝓞 D.host.F} (hf : f ∈ w.asIdeal) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f ∈ valIdeal ι := by
  change Valued.v (ι ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E)) < 1
  rw [algebraMap_O, AlgHom.commutes]
  exact (val_coe_lt_one_iff w f).2 hf

def plOf {w : HeightOneSpectrum (𝓞 D.host.F)} (ι : D.host.E →ₐ[D.host.F] w.adicCompletion D.host.F) :
    HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := valIdeal ι
  isPrime := valIdeal_prime ι
  ne_bot := by
    obtain ⟨n, hnw, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro h
    have := algebraMap_mem_valIdeal ι hnw
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)] at this
    exact hn0 this

/- English proof (translation)
Establish `hc : IsCoprime (p : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)`. Take `⟨a, b, hab⟩` from `hc.map (Int.castRingHom (𝓞 D.host.F))`. Apply `hI` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Simplify using `only [eq_intCast, Int.cast_natCast]`.

Conclude with `add_mem (I.mul_mem_left _ hpI) (I.mul_mem_left _ hqI)`.
-/
theorem not_two_primes_F {I : Ideal (𝓞 D.host.F)} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpI : (p : 𝓞 D.host.F) ∈ I) (hqI : (q : 𝓞 D.host.F) ∈ I) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 D.host.F))
  apply hI
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact add_mem (I.mul_mem_left _ hpI) (I.mul_mem_left _ hqI)

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `hc`. Take `⟨n, hnw, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Establish `hnl : w.intValuation n < 1` using `(HeightOneSpectrum.intValuation_lt_one_iff_mem w n).2 hnw`. Establish `key : ∀ x : 𝓞 D.host.E, Valued.v (ι (x : D.host.E) - ι (star (x : D.host.E))) < 1`. Introduce `x`.

Take `⟨b, hb⟩` from `Formalism.L2.S.Pv.PsiTrCore.exists_approx (sglV w (ι (x : D.host.E))) (fun v => by`. Distinguish the cases in `hv : v = w`. Substitute `hv; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (by` using the available equality. Rewrite using `[show (sglV v (ι (x : D.host.E))) v = evalV D.host.F v (sglV v (ι (x : D.host.E))) from rfl, sglV_same]`. Conclude with `val_emb_le v ι x)`.

Rewrite using `[show (sglV w (ι (x : D.host.E))) v = evalV D.host.F v (sglV w (ι (x : D.host.E))) from rfl, sglV_ne w _ hv]`. Conclude with `zero_mem _) n hn0`. Establish `hbw : Valued.v (ι (x : D.host.E) - algebraMap D.host.F (w.adicCompletion D.host.F) (b : D.host.F)) < 1`. Use `hb w` as an intermediate fact. Rewrite `this` using `[show (sglV w (ι (x : D.host.E))) w = evalV D.host.F w (sglV w (ι (x : D.host.E))) from rfl, sglV_same]`.

Conclude with `lt_of_le_of_lt this hnl`. Establish `hy : x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ (plOf ι).asIdeal`. Express the relevant statement in the definitionally equal form `Valued.v (ι ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E)) < 1`. Rewrite using `[show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) - algebraMap D.host.F D.host.E (b : D.host.F) from rfl, map_sub, AlgHom.commutes]`. Conclude with `hbw`.

Take `⟨c, hcP, hce⟩` from `hc _ hy`. Express the relevant statement in the definitionally equal form `Valued.v (ι (c : D.host.E)) < 1 at hcP`. Rewrite `hcP` using `[hce, show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) - algebraMap D.host.F D.host.E (b : D.host.F) from rfl, star_sub, show star (algebraMap D.host.F D.host.E (b : D.host.F)) = algebraMap D.host.F D.host.E (b : D.host.F) from (D.sp.cm …`. Rewrite using `[show ι (x : D.host.E) - ι (star (x : D.host.E)) = (ι (x : D.host.E) - algebraMap D.host.F (w.adicCompletion D.host.F) (b : D.host.F)) - (ι (star (x : D.host.E)) - algebraMap D.host.F (w.adicCompletion D.host.F) (b : D.host.F)) by ring]`. Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hbw hcP)`.

Establish `hd : Valued.v s < 1`. Use `key ⟨alphaH D.host, alphaH_integral D.host⟩` as an intermediate fact. Establish `hsa` using `star_alphaH D.host`. Express the relevant statement in the definitionally equal form `Valued.v (ι (alphaH D.host) - ι (star (alphaH D.host))) < 1 at this`. Rewrite `this` using `[hsa, ← map_sub, show alphaH D.host - (1 - alphaH D.host) = D.host.sqrtMinusD by unfold alphaH; ring, hι]`.

Conclude with `this`. Establish `hdw : ((D.host.d : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal`. Use `(val_coe_lt_one_iff w _).1 ?_` and prove the remaining obligations. Establish `h2 : Valued.v (s * s) < 1`. Rewrite using `[Valuation.map_mul]`.

Conclude with `mul_lt_one_of_lt_of_le hd (le_of_lt hd)`. Rewrite `h2` using `[hs, map_neg, Valuation.map_neg]`. Rewrite using `[← algebraMap_adic_eq, show (((D.host.d : ℕ) : 𝓞 D.host.F) : D.host.F) = (D.host.d : D.host.F) by push_cast; rfl]`. Conclude with `h2`. Take `⟨aq, haq⟩ : ∃ aq : D.host.E, aq = (D.host.sqq : D.host.E)` from `⟨_, rfl⟩`.

Establish `haq2 : aq * aq = -(D.host.q : D.host.E)`. Rewrite using `[haq, ← sq]`. Conclude with `D.host.sqq_sq`. Establish `hsaq : star aq = -aq` using `by rw [haq, Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.BasicNotions.Examples₂.conj_aE]`. Establish `hq8 : D.host.q % 8 = 3` using `D.host.hyp.2.2.1`.

Establish `hβi : IsIntegral ℤ ((1 + aq) / 2)`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((D.host.q + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, algebraMap_int_eq, eq_intCast, Int.cast_natCast]`. Establish `h4 : ((D.host.q + 1) / 4 : ℕ) * 4 = D.host.q + 1` using `by omega`. Establish `h4' : ((((D.host.q + 1) / 4 : ℕ) : D.host.E)) * 4 = (D.host.q : D.host.E) + 1` using `by exact_mod_cast h4`.

Take the linear combination `(1 / 4 : D.host.E) * haq2 + (1 / 4 : D.host.E) * h4'`. Establish `hq : Valued.v (ι aq) < 1`. Use `key ⟨(1 + aq) / 2, hβi⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `Valued.v (ι ((1 + aq) / 2) - ι (star ((1 + aq) / 2))) < 1 at this`. Rewrite using `[show star ((1 + aq) / 2) = (1 - aq) / 2 by`.

Rewrite using `[star_div₀, star_add, star_one, hsaq, show star (2 : D.host.E) = 2 from star_ofNat 2]`. Use the proof step `ring,`. Use the proof step `← map_sub, show (1 + aq) / 2 - (1 - aq) / 2 = aq by ring] at this`. Conclude with `this`. Establish `hqw : ((D.host.q : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal`.

Use `(val_coe_lt_one_iff w _).1 ?_` and prove the remaining obligations. Establish `h2 : Valued.v (ι aq * ι aq) < 1`. Rewrite using `[Valuation.map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hq (le_of_lt hq)`. Rewrite `h2` using `[← map_mul, haq2, map_neg, Valuation.map_neg, show ((D.host.q : ℕ) : D.host.E) = algebraMap D.host.F D.host.E (D.host.q : D.host.F) by simp, AlgHom.commutes]`.

Rewrite using `[← algebraMap_adic_eq, show (((D.host.q : ℕ) : 𝓞 D.host.F) : D.host.F) = (D.host.q : D.host.F) by push_cast; rfl]`. Conclude with `h2`. Conclude with `not_two_primes_F w.isPrime.ne_top D.host.hyp.2.1 D.host.hyp.1 (fun h => D.host.hypOdd.2.2.1 h.symm) hdw hqw`.
-/
theorem plOf_split {w : HeightOneSpectrum (𝓞 D.host.F)} (ι : D.host.E →ₐ[D.host.F] w.adicCompletion D.host.F)
    (s : w.adicCompletion D.host.F) (hs : s * s = algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)))
    (hι : ι D.host.sqrtMinusD = s) : ¬ Lev.IsConjPl (D := D) (plOf ι) (plOf ι) := by
  intro hc
  obtain ⟨n, hnw, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hnl : w.intValuation n < 1 := (HeightOneSpectrum.intValuation_lt_one_iff_mem w n).2 hnw
  have key : ∀ x : 𝓞 D.host.E, Valued.v (ι (x : D.host.E) - ι (star (x : D.host.E))) < 1 := by
    intro x
    obtain ⟨b, hb⟩ := Formalism.L2.S.Pv.PsiTrCore.exists_approx (sglV w (ι (x : D.host.E)))
      (fun v => by
        by_cases hv : v = w
        · subst hv; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (by
            rw [show (sglV v (ι (x : D.host.E))) v = evalV D.host.F v (sglV v (ι (x : D.host.E))) from rfl, sglV_same]
            exact val_emb_le v ι x)
        · rw [show (sglV w (ι (x : D.host.E))) v = evalV D.host.F v (sglV w (ι (x : D.host.E))) from rfl, sglV_ne w _ hv]
          exact zero_mem _) n hn0
    have hbw : Valued.v (ι (x : D.host.E) - algebraMap D.host.F (w.adicCompletion D.host.F) (b : D.host.F)) < 1 := by
      have := hb w
      rw [show (sglV w (ι (x : D.host.E))) w = evalV D.host.F w (sglV w (ι (x : D.host.E))) from rfl, sglV_same] at this
      exact lt_of_le_of_lt this hnl
    have hy : x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ (plOf ι).asIdeal := by
      change Valued.v (ι ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E)) < 1
      rw [show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) =
        (x : D.host.E) - algebraMap D.host.F D.host.E (b : D.host.F) from rfl, map_sub, AlgHom.commutes]
      exact hbw
    obtain ⟨c, hcP, hce⟩ := hc _ hy
    change Valued.v (ι (c : D.host.E)) < 1 at hcP
    rw [hce, show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) =
        (x : D.host.E) - algebraMap D.host.F D.host.E (b : D.host.F) from rfl, star_sub,
      show star (algebraMap D.host.F D.host.E (b : D.host.F)) = algebraMap D.host.F D.host.E (b : D.host.F) from
        (D.sp.cm.fixed _).2 ⟨_, rfl⟩, map_sub, AlgHom.commutes] at hcP
    rw [show ι (x : D.host.E) - ι (star (x : D.host.E)) =
      (ι (x : D.host.E) - algebraMap D.host.F (w.adicCompletion D.host.F) (b : D.host.F)) -
      (ι (star (x : D.host.E)) - algebraMap D.host.F (w.adicCompletion D.host.F) (b : D.host.F)) by ring]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hbw hcP)

  have hd : Valued.v s < 1 := by
    have := key ⟨alphaH D.host, alphaH_integral D.host⟩
    have hsa := star_alphaH D.host
    change Valued.v (ι (alphaH D.host) - ι (star (alphaH D.host))) < 1 at this
    rw [hsa, ← map_sub, show alphaH D.host - (1 - alphaH D.host) = D.host.sqrtMinusD by unfold alphaH; ring, hι] at this
    exact this
  have hdw : ((D.host.d : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal := by
    refine (val_coe_lt_one_iff w _).1 ?_
    have h2 : Valued.v (s * s) < 1 := by
      rw [Valuation.map_mul]; exact mul_lt_one_of_lt_of_le hd (le_of_lt hd)
    rw [hs, map_neg, Valuation.map_neg] at h2
    rw [← algebraMap_adic_eq, show (((D.host.d : ℕ) : 𝓞 D.host.F) : D.host.F) = (D.host.d : D.host.F) by push_cast; rfl]
    exact h2

  obtain ⟨aq, haq⟩ : ∃ aq : D.host.E, aq = (D.host.sqq : D.host.E) := ⟨_, rfl⟩
  have haq2 : aq * aq = -(D.host.q : D.host.E) := by
    rw [haq, ← sq]; exact D.host.sqq_sq
  have hsaq : star aq = -aq := by rw [haq, Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.BasicNotions.Examples₂.conj_aE]
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hβi : IsIntegral ℤ ((1 + aq) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((D.host.q + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    have h4 : ((D.host.q + 1) / 4 : ℕ) * 4 = D.host.q + 1 := by omega
    have h4' : ((((D.host.q + 1) / 4 : ℕ) : D.host.E)) * 4 = (D.host.q : D.host.E) + 1 := by exact_mod_cast h4
    linear_combination (1 / 4 : D.host.E) * haq2 + (1 / 4 : D.host.E) * h4'
  have hq : Valued.v (ι aq) < 1 := by
    have := key ⟨(1 + aq) / 2, hβi⟩
    change Valued.v (ι ((1 + aq) / 2) - ι (star ((1 + aq) / 2))) < 1 at this
    rw [show star ((1 + aq) / 2) = (1 - aq) / 2 by
      rw [star_div₀, star_add, star_one, hsaq, show star (2 : D.host.E) = 2 from star_ofNat 2]; ring,
      ← map_sub, show (1 + aq) / 2 - (1 - aq) / 2 = aq by ring] at this
    exact this
  have hqw : ((D.host.q : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal := by
    refine (val_coe_lt_one_iff w _).1 ?_
    have h2 : Valued.v (ι aq * ι aq) < 1 := by
      rw [Valuation.map_mul]; exact mul_lt_one_of_lt_of_le hq (le_of_lt hq)
    rw [← map_mul, haq2, map_neg, Valuation.map_neg,
      show ((D.host.q : ℕ) : D.host.E) = algebraMap D.host.F D.host.E (D.host.q : D.host.F) by simp, AlgHom.commutes] at h2
    rw [← algebraMap_adic_eq, show (((D.host.q : ℕ) : 𝓞 D.host.F) : D.host.F) = (D.host.q : D.host.F) by push_cast; rfl]
    exact h2
  exact not_two_primes_F w.isPrime.ne_top D.host.hyp.2.1 D.host.hyp.1
    (fun h => D.host.hypOdd.2.2.1 h.symm) hdw hqw

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨h1, h2, w, ε, hpl, hsε⟩` from `he`. Rewrite `hsε` using `[placeIdem_eq hpl]`. Express the relevant statement in the definitionally equal form `e + cA D e = phiE w 1 at hsε`. Take `⟨s, ι, hs, hι⟩` from `split_emb h1 h2 hsε`. Establish `hsp` using `plOf_split ι s hs hι`.

Establish `hle : w.asIdeal ≤ (belowPl (plOf ι)).asIdeal` using `fun f hf => algebraMap_mem_valIdeal ι hf`. Establish `hbel : belowPl (plOf ι) = w` using `(HeightOneSpectrum.ext (w.isMaximal.eq_of_le (belowPl (plOf ι)).isPrime.ne_top hle)).symm`. Rewrite `hsε` using `[← hbel]`. Take `⟨e₀, ι₀, he₀, -, hs₀, hz, hκ⟩` from `idem_data (plOf ι) hsp (belowPl (plOf ι)) rfl`. Break down `idem_class (plOf ι) hsp e₀ ι₀ hs₀ hz hκ he₀.1.1 he₀.1.2.1 e h1 h2 hsε with h | h` into its components or cases.

Rewrite using `[h]`. Conclude with `idemAt_int he₀`. Rewrite using `[h, finPart_cA]`. Conclude with `cF_int (idemAt_int he₀)`.
-/
theorem splitIdem_int {e : AE D} (he : IsSplitIdem D e) : finPart D e ∈ intAE D := by
  obtain ⟨h1, h2, w, ε, hpl, hsε⟩ := he
  rw [placeIdem_eq hpl] at hsε
  change e + cA D e = phiE w 1 at hsε
  obtain ⟨s, ι, hs, hι⟩ := split_emb h1 h2 hsε
  have hsp := plOf_split ι s hs hι
  have hle : w.asIdeal ≤ (belowPl (plOf ι)).asIdeal := fun f hf => algebraMap_mem_valIdeal ι hf
  have hbel : belowPl (plOf ι) = w :=
    (HeightOneSpectrum.ext (w.isMaximal.eq_of_le (belowPl (plOf ι)).isPrime.ne_top hle)).symm
  rw [← hbel] at hsε
  obtain ⟨e₀, ι₀, he₀, -, hs₀, hz, hκ⟩ := idem_data (plOf ι) hsp (belowPl (plOf ι)) rfl
  rcases idem_class (plOf ι) hsp e₀ ι₀ hs₀ hz hκ he₀.1.1 he₀.1.2.1 e h1 h2 hsε with h | h
  · rw [h]; exact idemAt_int he₀
  · rw [h, finPart_cA]; exact cF_int (idemAt_int he₀)

/- English proof (translation)
Establish `: u.map (fun a => e * a) = e • u` using `by ext i j; rfl`. Rewrite using `[this]`. Conclude with `latO_smul_mem S T ΛS ΛT (splitIdem_int he) hu`.
-/
theorem latO_map_splitIdem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {e : AE D} (he : IsSplitIdem D e) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    u.map (fun a => e * a) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True) := by
  have : u.map (fun a => e * a) = e • u := by ext i j; rfl
  rw [this]
  exact latO_smul_mem S T ΛS ΛT (splitIdem_int he) hu

end Formalism.IndefR.Fin

end
