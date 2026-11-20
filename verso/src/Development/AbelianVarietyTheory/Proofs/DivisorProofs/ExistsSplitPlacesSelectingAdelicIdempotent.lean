import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfIdem

open GlobalTheory.SplitIdem

section Local

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Establish `h : y * y ∈ v.adicCompletionIntegers F`. Rewrite using `[hy]`. Conclude with `neg_mem (natCast_mem _ d)`. Break down `ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers F) y with h1 | h1` into its components or cases. Conclude with `h1`.

Distinguish the cases in `h0 : y = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Use `mul_mem h h1` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel₀ h0, mul_one]`. Then use the resulting hypothesis.
-/
theorem sqrt_mem (d : ℕ) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (hy : y * y = -(d : Fv F v)) :
    y ∈ v.adicCompletionIntegers F := by
  have h : y * y ∈ v.adicCompletionIntegers F := by
    rw [hy]; exact neg_mem (natCast_mem _ d)
  rcases ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers F) y with h1 | h1
  · exact h1
  · by_cases h0 : y = 0
    · rw [h0]; exact zero_mem _
    · have := mul_mem h h1
      rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

/- English proof (translation)
Use `⟨⟨fun v => if h : ∃ y : Fv F v, y * y = -(d : Fv F v) then h.choose else 0, Filter.Eventually.of_forall fun v => ?_⟩, ⟨fun v => if ∃ y : Fv F v, y * y = -(d : Fv F v) then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : ∃ y : Fv F v, y * y = -(d : Fv F v)`. Simplify using `only [h, dif_pos]`. Conclude with `sqrt_mem F d v _ h.choose_spec`. Simplify using `only [h, dif_neg, not_false_iff]`.

Conclude with `zero_mem _`. Distinguish the cases in `h : ∃ y : Fv F v, y * y = -(d : Fv F v)`. Simplify using `only [h, if_true]`. Conclude with `one_mem _`. Simplify using `only [h, if_false]`.

Conclude with `zero_mem _`. Distinguish the cases in `h : ∃ y : Fv F v, y * y = -(d : Fv F v)`. Use `left`. Use `⟨if_pos h, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x : Fv F v, x = h.choose → x * x = -(d : Fv F v)` using `fun x hx => hx ▸ h.choose_spec`.

Conclude with `e _ (dif_pos h)`. Use `right`. Conclude with `⟨if_neg h, dif_neg h, fun y hy => h ⟨y, hy⟩⟩`.
-/
theorem exists_sqrt_adele (d : ℕ) : ∃ s ι : Af F, ∀ v,
    (evalV F v ι = 1 ∧ evalV F v s * evalV F v s = -(d : Fv F v)) ∨
    (evalV F v ι = 0 ∧ evalV F v s = 0 ∧ ∀ y : Fv F v, y * y ≠ -(d : Fv F v)) := by
  classical
  refine ⟨⟨fun v => if h : ∃ y : Fv F v, y * y = -(d : Fv F v) then h.choose else 0,
      Filter.Eventually.of_forall fun v => ?_⟩,
    ⟨fun v => if ∃ y : Fv F v, y * y = -(d : Fv F v) then 1 else 0,
      Filter.Eventually.of_forall fun v => ?_⟩, fun v => ?_⟩
  · by_cases h : ∃ y : Fv F v, y * y = -(d : Fv F v)
    · simp only [h, dif_pos]; exact sqrt_mem F d v _ h.choose_spec
    · simp only [h, dif_neg, not_false_iff]; exact zero_mem _
  · by_cases h : ∃ y : Fv F v, y * y = -(d : Fv F v)
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _
  · by_cases h : ∃ y : Fv F v, y * y = -(d : Fv F v)
    · left
      refine ⟨if_pos h, ?_⟩
      have e : ∀ x : Fv F v, x = h.choose → x * x = -(d : Fv F v) := fun x hx => hx ▸ h.choose_spec
      exact e _ (dif_pos h)
    · right
      exact ⟨if_neg h, dif_neg h, fun y hy => h ⟨y, hy⟩⟩

/- English proof (translation)
The claim follows from `Prod.ext (mul_zero _) rfl`.
-/
theorem pair_mul (α β : Af F) : pairA F 0 α * pairA F 0 β = pairA F 0 (α * β) :=
  Prod.ext (mul_zero _) rfl

/- English proof (translation)
The claim follows from `Prod.ext (zero_mul _) rfl`.
-/
theorem pair_mul' (α : Af F) (b : AF F) : pairA F 0 α * b = pairA F 0 (α * sndA F b) :=
  Prod.ext (zero_mul _) rfl

/- English proof (translation)
The claim follows from `Prod.ext neg_zero rfl`.
-/
theorem pair_neg (α : Af F) : -pairA F 0 α = pairA F 0 (-α) :=
  Prod.ext neg_zero rfl

/- English proof (translation)
Use `af_ext F fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[map_mul, map_mul, h]`. Rewrite using `[map_mul, map_mul, h0 w hw, zero_mul, zero_mul]`.
-/
theorem place_ext {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h0 : ∀ v', v' ≠ v → evalV F v' α = 0)
    {x y : Af F} (h : evalV F v x = evalV F v y) : α * x = α * y := by
  refine af_ext F fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, map_mul, h]
  · rw [map_mul, map_mul, h0 w hw, zero_mul, zero_mul]

end Local

/- English proof (translation)
Rewrite using `[star_eq_conj, D.host.conj_sqrtMinusD]`.
-/
theorem star_delta (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  rw [star_eq_conj, D.host.conj_sqrtMinusD]

/- English proof (translation)
The claim follows from `D.host.hyp.2.1.pos.ne'`.
-/
theorem d_ne_zero (D : D7) : D.host.d ≠ 0 := D.host.hyp.2.1.pos.ne'

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul a x`. Take `⟨u, w, rfl⟩` from `h x`. Use `⟨u • a, w • a, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_add, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`.

Conclude with `⟨a + a', b + b', by rw [map_add, map_add]; ring⟩`.
-/
theorem tensor_decomp {F A E : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E] (δ : E)
    (h : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • δ) (z : A ⊗[F] E) :
    ∃ a b : A, z = algebraMap A (A ⊗[F] E) a + algebraMap A (A ⊗[F] E) b * ((1 : A) ⊗ₜ[F] δ) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨u, w, rfl⟩ := h x
    refine ⟨u • a, w • a, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    simp
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := A) (B := E) (algebraMap F E).injective`.
-/
theorem tensor_inj {F A E : Type} [Field F] [CommRing A] [Algebra F A] [Field E] [Algebra F E] :
    Function.Injective (algebraMap A (A ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := A) (B := E) (algebraMap F E).injective

/- English proof (translation)
Establish `h` using `congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E) h`. Rewrite `h` using `[pow_two, map_mul, map_neg, map_natCast]`. Conclude with `h`.
-/
theorem tensor_sq {F A E : Type} [Field F] [CommRing A] [Algebra F A] [Field E] [Algebra F E] (δ : E) (n : ℕ)
    (h : δ ^ 2 = -(n : E)) : ((1 : A) ⊗ₜ[F] δ) * ((1 : A) ⊗ₜ[F] δ) = -(n : A ⊗[F] E) := by
  have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E) h
  rw [pow_two, map_mul, map_neg, map_natCast] at h
  exact h

/- English proof (translation)
Establish `hδ : D.host.sqrtMinusD ≠ 0`. Introduce `h`. Use `D.host.sqrtMinusD_sq` as an intermediate fact. Rewrite `this` using `[h]`. Apply `d_ne_zero D` to reduce the goal to its premises.

Establish `h2 : (D.host.d : D.host.E) = 0` using `by linear_combination this`. Conclude with `h2` after adjusting the coercions. Establish `h2 : star (2 : D.host.E) = 2` using `star_ofNat 2`. Take `⟨u, hu⟩` from `(D.sp.cm.fixed ((x + star x) / 2)).1 (by`. Express the relevant statement in the definitionally equal form `star _ = _`.

Rewrite using `[star_div₀, star_add, star_star, h2, add_comm])`. Take `⟨w, hw⟩` from `(D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by`. Express the relevant statement in the definitionally equal form `star _ = _`. Rewrite using `[star_div₀, star_sub, star_star, star_mul', h2, star_delta]`. Clear the denominators using the available nonvanishing facts.

Use the proof step `ring)`. Use `⟨u, w, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, hu, hw]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem field_decomp (D : D7) (x : D.host.E) :
    ∃ u w : D.host.F, x = u • (1 : D.host.E) + w • D.host.sqrtMinusD := by
  have hδ : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have := D.host.sqrtMinusD_sq
    rw [h] at this
    apply d_ne_zero D
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination this
    exact_mod_cast h2
  have h2 : star (2 : D.host.E) = 2 := star_ofNat 2
  obtain ⟨u, hu⟩ := (D.sp.cm.fixed ((x + star x) / 2)).1 (by
    change star _ = _
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨w, hw⟩ := (D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by
    change star _ = _
    rw [star_div₀, star_sub, star_star, star_mul', h2, star_delta]
    field_simp
    ring)
  refine ⟨u, w, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, hu, hw]
  field_simp
  ring

/- English proof (translation)
Take `⟨s, ι, hsι⟩` from `exists_sqrt_adele F n`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : ∃ h : AF F, h * (2 * n) = 1 := by`. Establish `hd : (2 * n : F) ≠ 0` using `mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hn0)`. Use `congrArg (algebraMap F (AF F)) (inv_mul_cancel₀ hd)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_natCast, map_ofNat, map_one]`.

Conclude with `⟨_, this⟩`. Establish `hH : j h * (2 * n) = 1`. Use `congrArg j hh` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_natCast, map_ofNat, map_one]`. Then use the resulting hypothesis. Establish `hII : j (pairA _ 0 ι) * j (pairA _ 0 ι) = j (pairA _ 0 ι)`.

Rewrite using `[← map_mul, pair_mul]`. Use `congr 2`. Use `af_ext _ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Apply the tactic sequence `rcases hsι w with h | h <;> simp [h.1]`.

Establish `hIS : j (pairA _ 0 ι) * j (pairA _ 0 s) = j (pairA _ 0 s)`. Rewrite using `[← map_mul, pair_mul]`. Use `congr 2`. Use `af_ext _ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Break down `hsι w with h | h` into its components or cases. Simplify using `[h.1]`. Simplify using `[h.2.1]`. Establish `hSS : j (pairA _ 0 s) * j (pairA _ 0 s) = -(j (pairA _ 0 ι) * n)`. Rewrite using `[← map_natCast j, ← map_mul, ← map_mul, ← map_neg, pair_mul, pair_mul', pair_neg]`.

Use `congr 2`. Use `af_ext _ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_neg, map_mul, map_natCast, map_natCast]`. Break down `hsι w with h | h` into its components or cases. Rewrite using `[h.1, h.2, one_mul]`.

Simplify using `[h.2.1, h.1]`. Take `⟨ε, hε⟩ : ∃ ε : T, ε = j h * (j (pairA _ 0 ι) * n - j (pairA _ 0 s) * δ)` from `⟨_, rfl⟩`. Establish `hcε : c ε = j h * (j (pairA _ 0 ι) * n + j (pairA _ 0 s) * δ)`. Rewrite using `[hε, map_mul, map_sub, map_mul, map_mul, hcj, hcj, hcj, hcδ, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinfε : p ε = 0`. Rewrite using `[hε, map_mul, map_sub, map_mul, map_mul, hinf, hinf]`. Simplify using the standard rewrite rules. Generalize the expression as in `hI : j (pairA _ 0 ι) = I at hII hIS hSS hε hcε`. Generalize the expression as in `hS : j (pairA _ 0 s) = S at hIS hSS hε hcε`.

Generalize the expression as in `hd : (n : T) = d at hH hSS hε hcε hδ2`. Generalize the expression as in `hHH : j h = H at hH hε hcε`. Establish `h2 : ε * c ε = 0`. Rewrite using `[hcε, hε]`. Take the linear combination `H * H * d * d * hII - H * H * δ * δ * hSS + H * H * I * d * hδ2`.

Establish `h3 : ε + c ε = I`. Rewrite using `[hcε, hε]`. Take the linear combination `I * hH`. Establish `h4 : I * ε = ε`. Rewrite using `[hε]`.

Take the linear combination `H * d * hII - H * δ * hIS`. Establish `h1 : ε * ε = ε`. Take the linear combination `ε * h3 - h2 + h4`. Use `⟨ε, h1, h2, hinfε, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `e ⟨he1, he2, v, η, ⟨α, rfl, hα1, hα0⟩, he3⟩`.

Take `⟨a, b, hab⟩` from `hdec e`. Establish `hce : c e = j a - j b * δ`. Rewrite using `[hab, map_add, map_mul, hcj, hcj, hcδ]`. Expand and normalize the polynomial expressions, which then agree. Establish `he4 : c e * c e = c e` using `by rw [← map_mul, he1]`.

Take `⟨B, hB⟩ : ∃ B : AF F, B = 2 * n * b` from `⟨_, rfl⟩`. Establish `hjB : j B = -δ * (e - c e)`. Rewrite using `[hB, map_mul, map_mul, map_ofNat, map_natCast, hd, hce]`. Take the linear combination `2 * j b * hδ2 + δ * hab`. Establish `hB1 : pairA _ 0 α * B = B` using `hinj (by`.

Rewrite using `[map_mul, ← he3, hjB]`. Take the linear combination `-δ * he1 + δ * he4)`. Establish `hB2 : B * B = -(pairA _ 0 α * n)` using `hinj (by`. Rewrite using `[map_mul, map_neg, map_mul, map_natCast, hd, ← he3, hjB]`. Take the linear combination `δ * δ * he1 + δ * δ * he4 - 2 * δ * δ * he2 + (e + c e) * hδ2)`.

Establish `hB3 : evalV _ v (sndA _ B) * evalV _ v (sndA _ B) = -(n : Fv F v)`. Rewrite using `[← map_mul, ← map_mul, hB2, map_neg, map_neg, map_mul, map_mul, map_natCast, map_natCast]`. Express the relevant statement in the definitionally equal form `-(evalV _ v α * _) = _`. Rewrite using `[hα1, one_mul]`. Break down `hsι v with ⟨hι, hs⟩ | ⟨-, -, hn⟩` into its components or cases.

Use `swap`. Conclude with `absurd hB3 (hn _)`. Establish `hNI : (e + c e) * I = e + c e`. Rewrite using `[he3, ← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]`. Establish `hcc : c (c ε) = ε`.

Rewrite using `[hcε, hε, ← hHH, ← hI, ← hS, ← hd, map_mul, map_add, map_mul, map_mul, hcj, hcj, hcj, hcδ, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_self_eq_mul_self_iff.1 (hB3.trans hs.symm) with hp | hp` into its components or cases. Use `right`. Establish `: j B = (e + c e) * S`.

Rewrite using `[he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', place_ext _ hα0 hp]`. Establish `h5 : c e = (e + c e) * ε`. Rewrite using `[hε]`. Take the linear combination `-(c e) * hH - H * d * hNI - H * δ * this + H * δ * hjB - H * (e - c e) * hδ2`. Prove the components needed by the constructor for the conclusion.

Take the linear combination `-e * h5 + (1 - ε) * he2 - ε * he1`. Take the linear combination `-(c e) * h5 + (1 - ε) * he4 - ε * he2`. Use `left`. Establish `: j B = -((e + c e) * S)`. Rewrite using `[he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', ← map_neg, pair_neg, ← mul_neg, place_ext _ hα0 (y := -s) (by rw [hp, map_neg])]`.

Establish `h5 : e = (e + c e) * ε`. Rewrite using `[hε]`. Take the linear combination `-e * hH - H * d * hNI + H * δ * this - H * δ * hjB + H * (e - c e) * hδ2`. Prove the components needed by the constructor for the conclusion. Take the linear combination `-e * h5 + (1 - ε) * he1 - ε * he2`.

Take the linear combination `-(c e) * h5 + (1 - ε) * he2 - ε * he4`. Introduce and unpack `v η ⟨⟨α, rfl, hα1, hα0⟩, hn⟩`. Break down `hsι v with ⟨hι, -⟩ | ⟨hι, -, -⟩` into its components or cases. It suffices to derive a contradiction. Establish `hNI : j (pairA _ 0 α) * I = j (pairA _ 0 α)`.

Rewrite using `[← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]`. Establish `hNN : j (pairA _ 0 α) * j (pairA _ 0 α) = j (pairA _ 0 α)`. Rewrite using `[← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hα1, map_one]), mul_one]`. Establish `hsum : j (pairA _ 0 α) * ε + c (j (pairA _ 0 α) * ε) = j (pairA _ 0 α)`. Rewrite using `[map_mul, hcj, ← mul_add, h3, hNI]`.

Use `hn ⟨j (pairA _ 0 α) * ε, ⟨?_, ?_, v, _, ⟨α, rfl, hα1, hα0⟩, hsum⟩, hsum⟩` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm, hNN, h1]`. Rewrite using `[map_mul, hcj, mul_mul_mul_comm, h2, mul_zero]`. Establish `hNI : j (pairA _ 0 α) * I = 0`. Rewrite using `[← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 0) (by rw [hι, map_zero]), mul_zero]`.

Conclude with `map_zero j`. Rewrite using `[← h4, ← mul_assoc, hNI, zero_mul]`.
-/
theorem exists_half_abstract {F T T' : Type} [Field F] [NumberField F] [CommRing T] [CommRing T']
    (j : AF F →+* T) (c : T →+* T) (p : T →+* T') (δ : T) (n : ℕ) (hn0 : n ≠ 0) (hinj : Function.Injective j)
    (hcj : ∀ a, c (j a) = j a) (hcδ : c δ = -δ) (hδ2 : δ * δ = -(n : T))
    (hdec : ∀ z, ∃ a b, z = j a + j b * δ) (hinf : ∀ α, p (j (pairA F 0 α)) = 0) :
    ∃ ε : T, ε * ε = ε ∧ ε * c ε = 0 ∧ p ε = 0 ∧
      (∀ e, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, (∃ α : Af F, η = pairA F 0 α ∧ evalV F v α = 1 ∧
          ∀ v', v' ≠ v → evalV F v' α = 0) ∧ e + c e = j η) →
        (ε * e = e ∧ ε * c e = 0) ∨ (ε * e = 0 ∧ ε * c e = c e)) ∧
      ∀ v η, ((∃ α : Af F, η = pairA F 0 α ∧ evalV F v α = 1 ∧ ∀ v', v' ≠ v → evalV F v' α = 0) ∧
        ¬ ∃ e : T, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, (∃ α : Af F, η = pairA F 0 α ∧ evalV F v α = 1 ∧
          ∀ v', v' ≠ v → evalV F v' α = 0) ∧ e + c e = j η) ∧ e + c e = j η) → j η * ε = 0 := by
  obtain ⟨s, ι, hsι⟩ := exists_sqrt_adele F n
  obtain ⟨h, hh⟩ : ∃ h : AF F, h * (2 * n) = 1 := by
    have hd : (2 * n : F) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hn0)
    have := congrArg (algebraMap F (AF F)) (inv_mul_cancel₀ hd)
    rw [map_mul, map_mul, map_natCast, map_ofNat, map_one] at this
    exact ⟨_, this⟩
  have hH : j h * (2 * n) = 1 := by
    have := congrArg j hh
    rwa [map_mul, map_mul, map_natCast, map_ofNat, map_one] at this
  have hII : j (pairA _ 0 ι) * j (pairA _ 0 ι) = j (pairA _ 0 ι) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h <;> simp [h.1]
  have hIS : j (pairA _ 0 ι) * j (pairA _ 0 s) = j (pairA _ 0 s) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h
    · simp [h.1]
    · simp [h.2.1]
  have hSS : j (pairA _ 0 s) * j (pairA _ 0 s) = -(j (pairA _ 0 ι) * n) := by
    rw [← map_natCast j, ← map_mul, ← map_mul, ← map_neg, pair_mul, pair_mul', pair_neg]
    congr 2
    refine af_ext _ fun w => ?_
    rw [map_mul, map_neg, map_mul, map_natCast, map_natCast]
    rcases hsι w with h | h
    · rw [h.1, h.2, one_mul]
    · simp [h.2.1, h.1]
  obtain ⟨ε, hε⟩ : ∃ ε : T, ε = j h * (j (pairA _ 0 ι) * n - j (pairA _ 0 s) * δ) := ⟨_, rfl⟩
  have hcε : c ε = j h * (j (pairA _ 0 ι) * n + j (pairA _ 0 s) * δ) := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hcj, hcj, hcj, hcδ, map_natCast]; ring
  have hinfε : p ε = 0 := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hinf, hinf]; simp
  generalize hI : j (pairA _ 0 ι) = I at hII hIS hSS hε hcε
  generalize hS : j (pairA _ 0 s) = S at hIS hSS hε hcε
  generalize hd : (n : T) = d at hH hSS hε hcε hδ2
  generalize hHH : j h = H at hH hε hcε
  have h2 : ε * c ε = 0 := by
    rw [hcε, hε]
    linear_combination H * H * d * d * hII - H * H * δ * δ * hSS + H * H * I * d * hδ2
  have h3 : ε + c ε = I := by
    rw [hcε, hε]
    linear_combination I * hH
  have h4 : I * ε = ε := by
    rw [hε]
    linear_combination H * d * hII - H * δ * hIS
  have h1 : ε * ε = ε := by
    linear_combination ε * h3 - h2 + h4
  refine ⟨ε, h1, h2, hinfε, ?_, ?_⟩
  · rintro e ⟨he1, he2, v, η, ⟨α, rfl, hα1, hα0⟩, he3⟩
    obtain ⟨a, b, hab⟩ := hdec e
    have hce : c e = j a - j b * δ := by
      rw [hab, map_add, map_mul, hcj, hcj, hcδ]; ring
    have he4 : c e * c e = c e := by rw [← map_mul, he1]
    obtain ⟨B, hB⟩ : ∃ B : AF F, B = 2 * n * b := ⟨_, rfl⟩
    have hjB : j B = -δ * (e - c e) := by
      rw [hB, map_mul, map_mul, map_ofNat, map_natCast, hd, hce]
      linear_combination 2 * j b * hδ2 + δ * hab
    have hB1 : pairA _ 0 α * B = B := hinj (by
      rw [map_mul, ← he3, hjB]
      linear_combination -δ * he1 + δ * he4)
    have hB2 : B * B = -(pairA _ 0 α * n) := hinj (by
      rw [map_mul, map_neg, map_mul, map_natCast, hd, ← he3, hjB]
      linear_combination δ * δ * he1 + δ * δ * he4 - 2 * δ * δ * he2 + (e + c e) * hδ2)
    have hB3 : evalV _ v (sndA _ B) * evalV _ v (sndA _ B) = -(n : Fv F v) := by
      rw [← map_mul, ← map_mul, hB2, map_neg, map_neg, map_mul, map_mul, map_natCast, map_natCast]
      change -(evalV _ v α * _) = _
      rw [hα1, one_mul]
    rcases hsι v with ⟨hι, hs⟩ | ⟨-, -, hn⟩
    swap
    · exact absurd hB3 (hn _)
    have hNI : (e + c e) * I = e + c e := by
      rw [he3, ← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
    have hcc : c (c ε) = ε := by
      rw [hcε, hε, ← hHH, ← hI, ← hS, ← hd, map_mul, map_add, map_mul, map_mul, hcj, hcj, hcj, hcδ, map_natCast]; ring
    rcases mul_self_eq_mul_self_iff.1 (hB3.trans hs.symm) with hp | hp
    · right
      have : j B = (e + c e) * S := by
        rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', place_ext _ hα0 hp]
      have h5 : c e = (e + c e) * ε := by
        rw [hε]
        linear_combination -(c e) * hH - H * d * hNI - H * δ * this + H * δ * hjB - H * (e - c e) * hδ2
      constructor
      · linear_combination -e * h5 + (1 - ε) * he2 - ε * he1
      · linear_combination -(c e) * h5 + (1 - ε) * he4 - ε * he2
    · left
      have : j B = -((e + c e) * S) := by
        rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', ← map_neg, pair_neg, ← mul_neg,
          place_ext _ hα0 (y := -s) (by rw [hp, map_neg])]
      have h5 : e = (e + c e) * ε := by
        rw [hε]
        linear_combination -e * hH - H * d * hNI + H * δ * this - H * δ * hjB + H * (e - c e) * hδ2
      constructor
      · linear_combination -e * h5 + (1 - ε) * he1 - ε * he2
      · linear_combination -(c e) * h5 + (1 - ε) * he2 - ε * he4
  · rintro v η ⟨⟨α, rfl, hα1, hα0⟩, hn⟩
    rcases hsι v with ⟨hι, -⟩ | ⟨hι, -, -⟩
    · exfalso
      have hNI : j (pairA _ 0 α) * I = j (pairA _ 0 α) := by
        rw [← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
      have hNN : j (pairA _ 0 α) * j (pairA _ 0 α) = j (pairA _ 0 α) := by
        rw [← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hα1, map_one]), mul_one]
      have hsum : j (pairA _ 0 α) * ε + c (j (pairA _ 0 α) * ε) = j (pairA _ 0 α) := by
        rw [map_mul, hcj, ← mul_add, h3, hNI]
      refine hn ⟨j (pairA _ 0 α) * ε, ⟨?_, ?_, v, _, ⟨α, rfl, hα1, hα0⟩, hsum⟩, hsum⟩
      · rw [mul_mul_mul_comm, hNN, h1]
      · rw [map_mul, hcj, mul_mul_mul_comm, h2, mul_zero]
    · have hNI : j (pairA _ 0 α) * I = 0 := by
        rw [← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 0) (by rw [hι, map_zero]), mul_zero]
        exact map_zero j
      rw [← h4, ← mul_assoc, hNI, zero_mul]

/- English proof (translation)
Introduce `D`. Establish `hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x` using `fun _ _ => rfl`. Conclude with `exists_half_abstract (algebraMap (AF D.host.F) (AE D)) (cA D) (infPart D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] D.host.sqrtMinusD) D.host.d (d_ne_zero D) tensor_inj (fun a => (hcA a 1).trans (congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_one _))) ((hcA 1 _).trans ((congrArg (fun x => (1 : …`.
-/
theorem exists_half_idem : ∀ D : D7, ∃ ε : AE D, ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0 := by
  intro D
  have hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := fun _ _ => rfl
  exact exists_half_abstract (algebraMap (AF D.host.F) (AE D)) (cA D) (infPart D)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] D.host.sqrtMinusD) D.host.d (d_ne_zero D) tensor_inj
    (fun a => (hcA a 1).trans (congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_one _)))
    ((hcA 1 _).trans ((congrArg (fun x => (1 : AF D.host.F) ⊗ₜ[D.host.F] x) (star_delta D)).trans
      (TensorProduct.tmul_neg _ _)))
    (tensor_sq _ _ D.host.sqrtMinusD_sq) (tensor_decomp _ (field_decomp D))
    (fun _ => TensorProduct.zero_tmul (Ainf D.host.F) (1 : D.host.E))

end GlobalTheory.HalfIdem

end
