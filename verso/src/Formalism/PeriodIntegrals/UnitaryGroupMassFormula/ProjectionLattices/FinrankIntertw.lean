import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.GLP

open Representation

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of g => simp [Representation.asAlgebraHom_of, hf]`. Consider the case `add a b ha hb => simp [map_add, ha, hb]`. Consider the case `smul r a ha => simp [map_smul, ha]`.
-/
theorem intertw_alg {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (f : V →ₗ[K] W)
    (hf : ∀ g x, f (ρ g x) = σ g (f x)) (a : MonoidAlgebra K G) (x : V) :
    f (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (f x) := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, hf]
  | add a b ha hb => simp [map_add, ha, hb]
  | smul r a ha => simp [map_smul, ha]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hx ((Module.forall_dual_apply_eq_zero_iff K x).1 h)`. Use `⟨(φ x)⁻¹ • LinearMap.smulRight φ y, ?_⟩` and prove the remaining obligations.

Simplify using `[LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]`.
-/
theorem exists_end_map {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {x : W} (hx : x ≠ 0) (y : W) : ∃ b : Module.End K W, b x = y := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff K x).1 h)
  refine ⟨(φ x)⁻¹ • LinearMap.smulRight φ y, ?_⟩
  simp [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]

/- English proof (translation)
Establish `hc : F ∈ Subalgebra.center K (Module.End K (T.W s))`. Rewrite using `[Subalgebra.mem_center_iff]`. Introduce `b`. Take `⟨a, rfl⟩` from `T.irr s b`. Use extensionality with `x`.

Simplify using `only [Module.End.mul_apply]`. Conclude with `(intertw_alg (T.tau s) (T.tau s) F (fun g x => LinearMap.congr_fun (hF g) x) a x).symm`. Rewrite `hc` using `[Algebra.IsCentral.center_eq_bot]`. Take `⟨c, hc⟩` from `Algebra.mem_bot.1 hc`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem scalar_of_comm (T : GoodSet K G) (s : T.S) (F : Module.End K (T.W s))
    (hF : ∀ g, F * T.tau s g = T.tau s g * F) : ∃ c : K, F = algebraMap K _ c := by
  have hc : F ∈ Subalgebra.center K (Module.End K (T.W s)) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := T.irr s b
    ext x
    simp only [Module.End.mul_apply]
    exact (intertw_alg (T.tau s) (T.tau s) F (fun g x => LinearMap.congr_fun (hF g) x) a x).symm
  rw [Algebra.IsCentral.center_eq_bot] at hc
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hc
  exact ⟨c, hc.symm⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`.

Apply `hne` to reduce the goal to its premises. Use extensionality with `y`. Take `⟨b, hb⟩` from `exists_end_map (K := K) hx0 y`. Take `⟨a, rfl⟩` from `T.irr s b`. Rewrite using `[← hb, intertw_alg _ _ f hf a x, LinearMap.mem_ker.1 hx, map_zero]`.

Both sides reduce to the same expression. Establish `hsurj : Function.Surjective f`. Choose the witnesses or unpack the hypotheses as in `⟨y0, hy0⟩ : ∃ y0, f y0 ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hne (LinearMap.ext h)`. Introduce `z`. Take `⟨b, hb⟩` from `exists_end_map (K := K) hy0 z`. Take `⟨a, rfl⟩` from `T.irr t b`. Conclude with `⟨(T.tau s).asAlgebraHom a y0, by rw [intertw_alg _ _ f hf a y0, hb]⟩`.

Set `e` to `LinearEquiv.ofBijective f ⟨hinj, hsurj⟩`. Apply `hst` to reduce the goal to its premises. Apply `T.inj` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `: T.tau t g = e.conj (T.tau s g)`.

Use extensionality with `z`. Take `⟨x, rfl⟩` from `hsurj z`. Establish `hx : e.symm (f x) = x`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Simplify using `only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hx]`. Rewrite using `[← hf g x]`. Both sides reduce to the same expression. Simplify using `only`. Rewrite using `[this, LinearMap.trace_conj']`.
-/
theorem intertw_zero (T : GoodSet K G) {s t : T.S} (hst : s ≠ t) (f : T.W s →ₗ[K] T.W t)
    (hf : ∀ g x, f (T.tau s g x) = T.tau t g (f x)) : f = 0 := by
  by_contra hne
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    apply hne
    ext y
    obtain ⟨b, hb⟩ := exists_end_map (K := K) hx0 y
    obtain ⟨a, rfl⟩ := T.irr s b
    rw [← hb, intertw_alg _ _ f hf a x, LinearMap.mem_ker.1 hx, map_zero]
    rfl
  have hsurj : Function.Surjective f := by
    obtain ⟨y0, hy0⟩ : ∃ y0, f y0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    intro z
    obtain ⟨b, hb⟩ := exists_end_map (K := K) hy0 z
    obtain ⟨a, rfl⟩ := T.irr t b
    exact ⟨(T.tau s).asAlgebraHom a y0, by rw [intertw_alg _ _ f hf a y0, hb]⟩
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  apply hst
  apply T.inj
  funext g
  have : T.tau t g = e.conj (T.tau s g) := by
    ext z
    obtain ⟨x, rfl⟩ := hsurj z
    have hx : e.symm (f x) = x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hx]
    rw [← hf g x]
    rfl
  simp only
  rw [this, LinearMap.trace_conj']

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Establish `hne : (IntertwiningMap.id (T.tau s)) ≠ 0`. Introduce `h0`. Take `⟨x, hx⟩` from `exists_ne (0 : T.W s)`.

Apply `hx` to reduce the goal to its premises. Use `congrArg (fun f : IntertwiningMap (T.tau s) (T.tau s) => f x) h0` as an intermediate fact. Simplify using `using this`. Rewrite using `[finrank_eq_one_iff_of_nonzero' _ hne]`. Introduce `f`.

Take `⟨c, hc⟩` from `scalar_of_comm T s f.toLinearMap (fun g => f.isIntertwining' g)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[IntertwiningMap.toLinearMap_smul, LinearMap.smul_apply, IntertwiningMap.toLinearMap_id, LinearMap.id_apply, hc, Module.algebraMap_end_apply]`. Establish `: Subsingleton (IntertwiningMap (T.tau s) (T.tau t))` using `⟨fun f g => by ext1`.

Rewrite using `[intertw_zero T h f.toLinearMap (fun g x => LinearMap.congr_fun (f.isIntertwining' g) x), intertw_zero T h g.toLinearMap (fun g' x => LinearMap.congr_fun (g.isIntertwining' g') x)]⟩`. Conclude with `Module.finrank_zero_of_subsingleton`.
-/
theorem finrank_intertw (T : GoodSet K G) (s t : T.S) :
    Module.finrank K (IntertwiningMap (T.tau s) (T.tau t)) = if s = t then 1 else 0 := by
  split_ifs with h
  · subst h
    have hne : (IntertwiningMap.id (T.tau s)) ≠ 0 := by
      intro h0
      obtain ⟨x, hx⟩ := exists_ne (0 : T.W s)
      apply hx
      have := congrArg (fun f : IntertwiningMap (T.tau s) (T.tau s) => f x) h0
      simpa using this
    rw [finrank_eq_one_iff_of_nonzero' _ hne]
    intro f
    obtain ⟨c, hc⟩ := scalar_of_comm T s f.toLinearMap (fun g => f.isIntertwining' g)
    refine ⟨c, ?_⟩
    ext x
    rw [IntertwiningMap.toLinearMap_smul, LinearMap.smul_apply, IntertwiningMap.toLinearMap_id,
      LinearMap.id_apply, hc, Module.algebraMap_end_apply]
  · have : Subsingleton (IntertwiningMap (T.tau s) (T.tau t)) := ⟨fun f g => by
      ext1
      rw [intertw_zero T h f.toLinearMap (fun g x => LinearMap.congr_fun (f.isIntertwining' g) x),
        intertw_zero T h g.toLinearMap (fun g' x => LinearMap.congr_fun (g.isIntertwining' g') x)]⟩
    exact Module.finrank_zero_of_subsingleton

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.
-/
theorem card_ne_zero [CharZero K] : ((Fintype.card G : ℕ) : K) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

/- English proof (translation)
Establish `hG : ((Nat.card G : ℕ) : K) ≠ 0`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `card_ne_zero`. Use `haveI : Invertible ((Nat.card G : ℕ) : K) := invertibleOfNonzero hG`. Establish `h` using `Representation.card_inv_mul_sum_char_mul_char_eq_finrank (T.tau s) (T.tau t)`.

Rewrite `h` using `[finrank_intertw]`. Simplify using `only [Representation.character] at h`. Rewrite `h` using `[inv_mul_eq_iff_eq_mul₀ hG]`. Rewrite using `[h, Nat.card_eq_fintype_card]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem char_orth [CharZero K] (T : GoodSet K G) (s t : T.S) :
    ∑ g : G, LinearMap.trace K _ (T.tau t g) * LinearMap.trace K _ (T.tau s g⁻¹) =
      if s = t then ((Fintype.card G : ℕ) : K) else 0 := by
  have hG : ((Nat.card G : ℕ) : K) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact card_ne_zero
  haveI : Invertible ((Nat.card G : ℕ) : K) := invertibleOfNonzero hG
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (T.tau s) (T.tau t)
  rw [finrank_intertw] at h
  simp only [Representation.character] at h
  rw [inv_mul_eq_iff_eq_mul₀ hG] at h
  rw [h, Nat.card_eq_fintype_card]
  split_ifs <;> simp

def cS (T : GoodSet K G) (s : T.S) (x : G) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eS_eq (T : GoodSet K G) (s : T.S) :
    eS T s = ∑ x : G, cS T s x • MonoidAlgebra.of K G x := rfl

/- English proof (translation)
Rewrite using `[eS_eq, map_sum]`. Simplify using `[map_smul, Representation.asAlgebraHom_of]`.
-/
theorem asAlg_eS {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (T : GoodSet K G) (s : T.S) :
    ρ.asAlgebraHom (eS T s) = ∑ x : G, cS T s x • ρ x := by
  rw [eS_eq, map_sum]
  simp [map_smul, Representation.asAlgebraHom_of]

/- English proof (translation)
Use `Representation.char_conj (T.tau s) x⁻¹ h` as an intermediate fact. Simplify using `only [Representation.character] at this`. Simplify using `only [cS]`. Rewrite using `[show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group, this]`.
-/
theorem cS_conj (T : GoodSet K G) (s : T.S) (h x : G) : cS T s (h * x * h⁻¹) = cS T s x := by
  have := Representation.char_conj (T.tau s) x⁻¹ h
  simp only [Representation.character] at this
  simp only [cS]
  rw [show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group, this]

/- English proof (translation)
Rewrite using `[asAlg_eS, Finset.sum_mul, Finset.mul_sum]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, ← map_mul]`. Use `Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ fun x => ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]`. Establish `hc` using `cS_conj T s g⁻¹ x`.

Rewrite `hc` using `[inv_inv]`. Rewrite using `[hc]`. Use `congr 2`. Use `group`.
-/
theorem tau_eS_comm (T : GoodSet K G) (s t : T.S) (g : G) :
    (T.tau t).asAlgebraHom (eS T s) * T.tau t g = T.tau t g * (T.tau t).asAlgebraHom (eS T s) := by
  rw [asAlg_eS, Finset.sum_mul, Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, ← map_mul]
  refine Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  have hc := cS_conj T s g⁻¹ x
  rw [inv_inv] at hc
  rw [hc]
  congr 2
  group

/- English proof (translation)
The claim follows from `Module.finrank_pos`.
-/
theorem finrank_pos' (T : GoodSet K G) (s : T.S) : (0 : ℕ) < Module.finrank K (T.W s) :=
  Module.finrank_pos

/- English proof (translation)
Take `⟨c, hc⟩` from `scalar_of_comm T t _ (tau_eS_comm T s t)`. Establish `htr : LinearMap.trace K _ ((T.tau t).asAlgebraHom (eS T s)) = ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) * (if s = t then ((Fintype.card G : ℕ) : K) else 0)`. Rewrite using `[asAlg_eS, map_sum, ← char_orth T s t, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, cS]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `htr` using `[hc, Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id, smul_eq_mul]`. Establish `hd : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 (finrank_pos' T t).ne'`. Rewrite using `[hc]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite `htr` using `[if_pos rfl, div_mul_cancel₀ _ (card_ne_zero (K := K) (G := G))]`. Establish `: c = 1`. Use `mul_right_cancel₀ hd (htr.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`.

Rewrite using `[this, map_one]`. Rewrite `htr` using `[if_neg h, mul_zero]`. Establish `: c = 0`. Break down `mul_eq_zero.1 htr with h1 | h1` into its components or cases. Conclude with `h1`.

Conclude with `absurd h1 hd`. Rewrite using `[this, map_zero]`.
-/
theorem tau_eS [CharZero K] (T : GoodSet K G) (s t : T.S) :
    (T.tau t).asAlgebraHom (eS T s) = if s = t then 1 else 0 := by
  obtain ⟨c, hc⟩ := scalar_of_comm T t _ (tau_eS_comm T s t)
  have htr : LinearMap.trace K _ ((T.tau t).asAlgebraHom (eS T s)) =
      ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
        (if s = t then ((Fintype.card G : ℕ) : K) else 0) := by
    rw [asAlg_eS, map_sum, ← char_orth T s t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_eq_mul, cS]
    ring
  rw [hc, Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  have hd : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (finrank_pos' T t).ne'
  rw [hc]
  split_ifs with h
  · subst h
    rw [if_pos rfl, div_mul_cancel₀ _ (card_ne_zero (K := K) (G := G))] at htr
    have : c = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, map_one]
  · rw [if_neg h, mul_zero] at htr
    have : c = 0 := by
      rcases mul_eq_zero.1 htr with h1 | h1
      · exact h1
      · exact absurd h1 hd
    rw [this, map_zero]

/- English proof (translation)
Establish `key : ∑ x : G, cS T s x * cS T t (x⁻¹ * z) = ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) * LinearMap.trace K _ (T.tau t z⁻¹ * (T.tau t).asAlgebraHom (eS T s))`. Rewrite using `[asAlg_eS, Finset.mul_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, smul_eq_mul, ← map_mul]`. Simplify using `only [cS, mul_inv_rev, inv_inv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, tau_eS]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mul_one, cS]`.

Rewrite using `[mul_zero, map_zero, mul_zero]`.
-/
theorem coef_mul [CharZero K] (T : GoodSet K G) (s t : T.S) (z : G) :
    ∑ x : G, cS T s x * cS T t (x⁻¹ * z) = if s = t then cS T s z else 0 := by
  have key : ∑ x : G, cS T s x * cS T t (x⁻¹ * z) =
      ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
        LinearMap.trace K _ (T.tau t z⁻¹ * (T.tau t).asAlgebraHom (eS T s)) := by
    rw [asAlg_eS, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← map_mul]
    simp only [cS, mul_inv_rev, inv_inv]
    ring
  rw [key, tau_eS]
  split_ifs with h
  · subst h
    rw [mul_one, cS]
  · rw [mul_zero, map_zero, mul_zero]

/- English proof (translation)
Establish `h1 : eS T s * eS T t = ∑ z : G, (∑ x : G, cS T s x * cS T t (x⁻¹ * z)) • MonoidAlgebra.of K G z`. Rewrite using `[eS_eq, eS_eq, Finset.sum_mul_sum]`. Simplify using `only [smul_mul_smul_comm, ← map_mul]`. Repeatedly rewrite using `[Finset.sum_smul]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Conclude with `Fintype.sum_equiv (Equiv.mulLeft x) _ _ (fun y => by simp)`. Rewrite using `[h1]`. Repeatedly rewrite using `[coef_mul]`. Use `split_ifs with h`.

Rewrite using `[eS_eq]`. Simplify using the standard rewrite rules.
-/
theorem eS_mul_eS [CharZero K] (T : GoodSet K G) (s t : T.S) :
    eS T s * eS T t = if s = t then eS T s else 0 := by
  have h1 : eS T s * eS T t =
      ∑ z : G, (∑ x : G, cS T s x * cS T t (x⁻¹ * z)) • MonoidAlgebra.of K G z := by
    rw [eS_eq, eS_eq, Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm, ← map_mul]
    simp_rw [Finset.sum_smul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ (fun y => by simp)
  rw [h1]
  simp_rw [coef_mul]
  split_ifs with h
  · rw [eS_eq]
  · simp

/- English proof (translation)
Rewrite using `[eG, Finset.sum_mul_sum]`. Repeatedly rewrite using `[eS_mul_eS]`. Simplify using the standard rewrite rules.
-/
theorem eG_mul_eG [CharZero K] (T : GoodSet K G) : eG T * eG T = eG T := by
  rw [eG, Finset.sum_mul_sum]
  simp_rw [eS_mul_eS]
  simp

end PI.Dv.GLP
