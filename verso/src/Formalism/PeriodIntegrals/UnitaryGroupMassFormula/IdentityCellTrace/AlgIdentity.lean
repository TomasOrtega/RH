import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.ExistsSmulMem
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.IdCellInSW

section Alg

variable {E : Type} [Field E] [StarRing E] {r : ℕ}

/- English proof (translation)
Establish `key : ∀ a b, star (α a) * (α' b * G a b) + s a b * α' b * star (α a) + star (s b a) * star (α a) * α' b = 0`. Introduce `a b`. Use `hs a b` as an intermediate fact. Take the linear combination `(star (α a) * α' b) * this`. Establish `h1 : (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) = -(∑ a, star (α a) * β' a) + ∑ a, ∑ b, s a b * α' b * star (α a)`.

Simplify using `only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul]`. Use `congr 1`. Conclude with `congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)`. Establish `h2 : (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) = -(∑ a, α' a * star (β a)) + ∑ a, ∑ b, star (s b a) * star (α a) * α' b`. Simplify using `only [star_add, star_neg, star_sum, star_mul', add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul]`.

Use `congr 1`. Conclude with `congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[h1, h2]`. Establish `h3 : (∑ a, ∑ b, star (α a) * (α' b * G a b)) + (∑ a, ∑ b, s a b * α' b * star (α a)) + (∑ a, ∑ b, star (s b a) * star (α a) * α' b) = 0`.

Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun b _ => key a b`. Take the linear combination `h3`.
-/
theorem alg_identity (α α' β β' : Fin r → E) (G s : Fin r → Fin r → E)
    (hs : ∀ a b, G a b + s a b + star (s b a) = 0) :
    (∑ a, α' a * star (β a)) + (∑ a, star (α a) * β' a) +
      (∑ a, ∑ b, star (α a) * (α' b * G a b)) +
      (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) +
      (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) = 0 := by
  have key : ∀ a b, star (α a) * (α' b * G a b) + s a b * α' b * star (α a) +
      star (s b a) * star (α a) * α' b = 0 := by
    intro a b
    have := hs a b
    linear_combination (star (α a) * α' b) * this
  have h1 : (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) =
      -(∑ a, star (α a) * β' a) + ∑ a, ∑ b, s a b * α' b * star (α a) := by
    simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    exact congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)
  have h2 : (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) =
      -(∑ a, α' a * star (β a)) + ∑ a, ∑ b, star (s b a) * star (α a) * α' b := by
    simp only [star_add, star_neg, star_sum, star_mul', add_mul, neg_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    · exact congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)
    · rw [Finset.sum_comm]
  rw [h1, h2]
  have h3 : (∑ a, ∑ b, star (α a) * (α' b * G a b)) + (∑ a, ∑ b, s a b * α' b * star (α a)) +
      (∑ a, ∑ b, star (s b a) * star (α a) * α' b) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun b _ => key a b
  linear_combination h3

end Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

/- English proof (translation)
Simplify using `using Submodule.mul_mem_mul ha hb`.
-/
theorem one_mul_mem {a b : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) (hb : b ∈ (1 : Submodule (𝓞 E) E)) :
    a * b ∈ (1 : Submodule (𝓞 E) E) := by
  simpa using Submodule.mul_mem_mul ha hb

/- English proof (translation)
Establish `hl : ∀ (t : E) x y, h (t • x) y = star t * h x y` using `fun t x y => by`. Rewrite using `[LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]`. Establish `hr : ∀ (t : E) x y, h x (t • y) = t * h x y` using `fun t x y => by`. Rewrite using `[map_smul, smul_eq_mul]`. Establish `hsy : ∀ x y, h y x = star (h x y)` using `fun x y => by`.

Rewrite using `[← hs.eq x y, starRingEnd_apply]`. Establish `memΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, h y x ∈ (1 : Submodule (𝓞 E) E)` using `fun x => by conv_lhs => rw [← hU]`. Conclude with `Formalism.HermitianLatticesTheory.dualBasic_mem_dual h Λ x`. Establish `intΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ (1 : Submodule (𝓞 E) E)` using `fun x hx y hy => (memΛ y).1 hy x hx`. Take `⟨ρ, hρX, hρid⟩` from `exists_retract Λ hfg X`.

Set `φ : Fin r → V → E` to `fun a x => c' a x - c a x`. Establish `hφadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, φ a (x + y) = φ a x + φ a y` using `fun a x hx y hy => by`. Simplify using `only [φ, hcadd a x hx y hy, hcadd' a x hx y hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφsmul : ∀ a (t : E), ∀ x ∈ X, φ a (t • x) = t * φ a x` using `fun a t x hx => by`.

Simplify using `only [φ, hcsmul a t x hx, hcsmul' a t x hx]`. Expand and normalize the polynomial expressions, which then agree. Set `ψ : Fin r → (Λ →ₗ[𝓞 E] E)` to `fun a => { toFun := fun y => φ a (ρ y : V) map_add' := fun y₁ y₂ => by`. Rewrite using `[map_add, Submodule.coe_add, hφadd a _ (hρX y₁) _ (hρX y₂)]`. Use the proof step `map_smul' := fun o y => by`.

Rewrite using `[map_smul, Submodule.coe_smul, ← algebraMap_smul E o, hφsmul a _ _ (hρX y), RingHom.id_apply, Algebra.smul_def] }`. Use `choose w hw using fun a => riesz h hs hnd Λ hfg hsp (ψ a)`. Establish `hwX : ∀ a, ∀ x ∈ X, h (w a) x = φ a x`. Introduce `a x hx`. Take `⟨d, hd, hdx⟩` from `exists_smul_mem Λ hsp x`.

Establish `hdX : d • x ∈ X` using `by rw [← algebraMap_smul E d x]; exact X.smul_mem _ hx`. Establish `h1` using `hw a (d • x) hdx`. Establish `h2 : ρ ⟨d • x, hdx⟩ = ⟨d • x, hdx⟩` using `hρid _ hdX`. Establish `h3 : ψ a ⟨d • x, hdx⟩ = φ a (d • x)` using `by show φ a (ρ ⟨d • x, hdx⟩ : V) = _`. Rewrite using `[h2]`.

Rewrite `h1` using `[h3, ← algebraMap_smul E d x, hr, hφsmul a _ x hx]`. Conclude with `mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1`. Establish `hwJ : ∀ a, ∀ y ∈ Λ, h (w a) y ∈ J a`. Introduce `a y hy`. Rewrite using `[hw a y hy]`.

Use `show φ a (ρ ⟨y, hy⟩ : V) ∈ J a`. Establish `hm` using `hJ2 _ (ρ ⟨y, hy⟩).2 (hρX _) a`. Conclude with `(J a).sub_mem hm.2 hm.1`. Establish `key : ∀ b, ∑ a, h (w a) (e' b) • e a = e b - e' b`. Introduce `b`.

Establish `h1 : ∀ a, h (w a) (e' b) = (if a = b then 1 else 0) - c a (e' b)` using `fun a => by`. Rewrite using `[hwX a _ (he' b)]`. Simplify using `only [φ, hδ' a b]`. Simplify using `only [h1, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← hc _ (he' b)]`.

Set `G : Fin r → Fin r → E` to `fun a b => h (w a) (w b)`. Set `k : Fin r → Fin r → E` to `fun a b => if a < b then -1 else if a = b then -(θ : E) else 0`. Set `s : Fin r → Fin r → E` to `fun a b => k a b * G a b`. Establish `hkint : ∀ a b, k a b ∈ (1 : Submodule (𝓞 E) E)`. Introduce `a b`.

Simplify using `only [k]`. Use `split_ifs`. Conclude with `Submodule.mem_one.2 ⟨-1, by simp⟩`. Conclude with `Submodule.mem_one.2 ⟨-θ, by simp⟩`. Conclude with `Submodule.zero_mem _`.

Establish `hsG : ∀ a b, G a b + s a b + star (s b a) = 0`. Introduce `a b`. Establish `hG : star (G b a) = G a b` using `(hsy (w b) (w a)).symm`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Establish `h1 : ¬ b < a` using `not_lt.2 hab.le`.

Establish `h2 : b ≠ a` using `hab.ne'`. Simplify using `only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGs : star (G a a) = G a a` using `hG`. Simplify using `only [s, k, lt_irrefl, if_false, if_true, star_mul', star_neg, hGs]`.

Take the linear combination `(-(G a a)) * hθ`. Establish `h1 : ¬ a < b` using `not_lt.2 hab.le`. Establish `h2 : a ≠ b` using `hab.ne'`. Simplify using `only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_mul', star_neg, star_one, hG]`. Expand and normalize the polynomial expressions, which then agree.

Set `cc : Fin r → (V →ₗ[E] E)` to `fun a => -(h (w a)) + ∑ b, s a b • h (e b)`. Establish `hcc : ∀ a v, cc a v = -h (w a) v + ∑ b, s a b * h (e b) v` using `fun a v => by`. Simplify using `[cc]`. Set `nL : V →ₗ[E] V` to `LinearMap.id + ∑ a, (h (e a)).smulRight (w a) + ∑ a, (cc a).smulRight (e' a)`. Establish `hn : ∀ v, nL v = v + ∑ a, h (e a) v • w a + ∑ a, cc a v • e' a` using `fun v => by`.

Simplify using `[nL]`. Establish `hBX : ∀ v, ∑ a, cc a v • e' a ∈ X` using `fun v => X.sum_mem fun a _ => X.smul_mem _ (he' a)`. Establish `K1 : ∀ v a, h (v + ∑ b, h (e b) v • w b) (e' a) = star (h (e a) v)`. Introduce `v a`. Establish `hk` using `congrArg (h v) (key a)`.

Rewrite `hk` using `[map_sum, map_sub]`. Simplify using `only [hr] at hk`. Rewrite using `[map_add, LinearMap.add_apply, LinearMap.map_sum₂]`. Simplify using `only [hl]`. Establish `e1 : h v (e' a) = h v (e a) - ∑ b, h (w b) (e' a) * h v (e b)` using `by rw [hk]; ring`.

Rewrite using `[e1, ← hsy]`. Establish `e2 : ∑ b, star (h (e b) v) * h (w b) (e' a) = ∑ b, h (w b) (e' a) * h v (e b)` using `Finset.sum_congr rfl fun b _ => by rw [hsy (e b) v, mul_comm]`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hiso_n : ∀ v v', h (nL v) (nL v') = h v v'`.

Introduce `v v'`. Rewrite using `[hn, hn]`. Use `set P := v + ∑ b, h (e b) v • w b with hP`. Use `set P' := v' + ∑ b, h (e b) v' • w b with hP'`. Establish `hBB : h (∑ a, cc a v • e' a) (∑ a, cc a v' • e' a) = 0` using `hiso _ (hBX v) _ (hBX v')`.

Establish `hPB : h P (∑ a, cc a v' • e' a) = ∑ a, cc a v' * star (h (e a) v)`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [hr, K1]`. Establish `hBP : h (∑ a, cc a v • e' a) P' = ∑ a, star (cc a v) * h (e a) v'`. Rewrite using `[LinearMap.map_sum₂]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hl, hsy P' (e' a), K1, star_star]`. Establish `hPP : h P P' = h v v' + ((∑ a, h (e a) v' * star (h (w a) v)) + (∑ a, star (h (e a) v) * h (w a) v') + (∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b)))`. Establish `e1 : ∀ a, h v (w a) = star (h (w a) v)` using `fun a => hsy _ _`. Establish `hdbl : (∑ b, h (e b) v' * ∑ a, star (h (e a) v) * h (w a) (w b)) = ∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b)`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp only [G]; ring`. Rewrite using `[hP, hP']`. Simplify using `only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, e1, RingHom.id_apply, mul_add]`.

Rewrite using `[Finset.sum_add_distrib, hdbl]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[hBB, hPB, hBP, hPP]`. Use `alg_identity (fun a => h (e a) v) (fun a => h (e a) v') (fun a => h (w a) v) (fun a => h (w a) v') G s hsG` as an intermediate fact.

Simplify using `only [hcc]`. Take the linear combination `this`. Establish `hinj : Function.Injective nL`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`.

Use `hnd.1 v fun y => ?_` and prove the remaining obligations. Rewrite using `[← hiso_n v y, hv, LinearMap.map_zero₂]`. Establish `P1 : ∀ a, ∀ v ∈ Λ, h (e a) v • w a ∈ Λ`. Introduce `a v hv`. Rewrite using `[memΛ]`.

Introduce `y hy`. Rewrite using `[hr, hsy (w a) y]`. Establish `ht` using `(hJ1 a _ (hwJ a y hy)).1`. Use `intΛ _ ht v hv` as an intermediate fact. Rewrite `this` using `[hl]`.

Rewrite using `[mul_comm]` and apply the resulting hypothesis. Establish `P1' : ∀ a, ∀ v ∈ Λ, h (e' a) v • w a ∈ Λ`. Introduce `a v hv`. Rewrite using `[memΛ]`. Introduce `y hy`.

Rewrite using `[hr, hsy (w a) y]`. Establish `ht` using `(hJ1 a _ (hwJ a y hy)).2`. Use `intΛ _ ht v hv` as an intermediate fact. Rewrite `this` using `[hl]`. Rewrite using `[mul_comm]` and apply the resulting hypothesis.

Establish `P2 : ∀ a, ∀ v ∈ Λ, cc a v • e' a ∈ Λ`. Introduce `a v hv`. Rewrite using `[memΛ]`. Introduce `y hy`. Rewrite using `[hr, hcc, hsy (e' a) y]`.

Establish `t1 : h (w a) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E)`. Use `intΛ _ (P1' a y hy) v hv` as an intermediate fact. Rewrite `this` using `[hl, mul_comm]`. Then use the resulting hypothesis. Establish `t2 : ∀ b, s a b * h (e b) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E)`. Introduce `b`.

Use `intΛ _ (P1' a y hy) _ (P1 b v hv)` as an intermediate fact. Rewrite `this` using `[hl, hr]`. Establish `e1 : s a b * h (e b) v * star (h (e' a) y) = k a b * (star (h (e' a) y) * (h (e b) v * h (w a) (w b)))` using `by simp only [s, G]; ring`. Rewrite using `[e1]`. Conclude with `one_mul_mem (hkint a b) this`.

Rewrite using `[add_mul, Finset.sum_mul, neg_mul]`. Conclude with `Submodule.add_mem _ (Submodule.neg_mem _ t1) (Submodule.sum_mem _ fun b _ => t2 b)`. Establish `hint : ∀ v ∈ Λ, nL v ∈ Λ`. Introduce `v hv`. Rewrite using `[hn]`.

Conclude with `Λ.add_mem (Λ.add_mem hv (Λ.sum_mem fun a _ => P1 a v hv)) (Λ.sum_mem fun a _ => P2 a v hv)`. Set `n : V ≃ₗ[E] V` to `LinearEquiv.ofInjectiveEndo nL hinj`. Establish `hnapp : ∀ v, n v = nL v` using `fun v => rfl`. Use `⟨n, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ x y, h (n x) (n y) = h x y`.

Introduce `x y`. Rewrite using `[hnapp, hnapp, hiso_n]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `hint v hv`.

Introduce `y hy`. Use `⟨n.symm y, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, memΛ]`. Introduce `x hx`. Establish `e : h x (n.symm y) = h (nL x) y`.

Rewrite using `[← hiso_n x (n.symm y), ← hnapp (n.symm y), LinearEquiv.apply_symm_apply]`. Rewrite using `[e]`. Conclude with `intΛ _ (hint x hx) y hy`. Introduce `a`. Rewrite using `[hnapp, hn]`.

Establish `h0 : ∀ b, h (e b) (e a) = 0` using `fun b => hiso _ (he b) _ (he a)`. Establish `h1 : ∀ b, cc b (e a) = (if b = a then 1 else 0) - c' b (e a)`. Introduce `b`. Rewrite using `[hcc, hwX b _ (he a)]`. Simplify using `only [h0, mul_zero, Finset.sum_const_zero, add_zero, φ, hδ b a]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h0, zero_smul, Finset.sum_const_zero, add_zero, h1, sub_smul, ite_smul, one_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← hc' _ (he a)]`. Normalize the expressions using the abelian group laws. Introduce `v hv`.

Rewrite using `[hnapp, hn]`. Establish `h0 : ∀ a, h (e a) v = 0` using `fun a => hv _ (he a)`. Simplify using `only [h0, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]`. Conclude with `hBX v`.
-/
theorem core (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (hU : Formalism.HermitianLatticesTheory.dual h Λ = Λ)
    (X : Submodule E V) (hiso : ∀ x ∈ X, ∀ y ∈ X, h x y = 0) {r : ℕ}
    (e e' : Fin r → V) (he : ∀ a, e a ∈ X) (he' : ∀ a, e' a ∈ X)
    (c c' : Fin r → V → E)
    (hc : ∀ x ∈ X, x = ∑ a, c a x • e a) (hc' : ∀ x ∈ X, x = ∑ a, c' a x • e' a)
    (hcadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c a (x + y) = c a x + c a y)
    (hcadd' : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c' a (x + y) = c' a x + c' a y)
    (hcsmul : ∀ a (t : E), ∀ x ∈ X, c a (t • x) = t * c a x)
    (hcsmul' : ∀ a (t : E), ∀ x ∈ X, c' a (t • x) = t * c' a x)
    (hδ : ∀ a b, c a (e b) = if a = b then 1 else 0) (hδ' : ∀ a b, c' a (e' b) = if a = b then 1 else 0)
    (J : Fin r → Submodule (𝓞 E) E)
    (hJ1 : ∀ a, ∀ t ∈ J a, t • e a ∈ Λ ∧ t • e' a ∈ Λ)
    (hJ2 : ∀ x ∈ Λ, x ∈ X → ∀ a, c a x ∈ J a ∧ c' a x ∈ J a)
    (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) :
    ∃ n : V ≃ₗ[E] V, n ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ ∧ (∀ a, n (e a) = e' a) ∧
      ∀ v, (∀ x ∈ X, h x v = 0) → n v - v ∈ X := by
  classical

  have hl : ∀ (t : E) x y, h (t • x) y = star t * h x y := fun t x y => by
    rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
  have hr : ∀ (t : E) x y, h x (t • y) = t * h x y := fun t x y => by
    rw [map_smul, smul_eq_mul]
  have hsy : ∀ x y, h y x = star (h x y) := fun x y => by
    rw [← hs.eq x y, starRingEnd_apply]
  have memΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, h y x ∈ (1 : Submodule (𝓞 E) E) := fun x => by
    conv_lhs => rw [← hU]
    exact Formalism.HermitianLatticesTheory.dualBasic_mem_dual h Λ x
  have intΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy =>
    (memΛ y).1 hy x hx

  obtain ⟨ρ, hρX, hρid⟩ := exists_retract Λ hfg X
  let φ : Fin r → V → E := fun a x => c' a x - c a x
  have hφadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, φ a (x + y) = φ a x + φ a y := fun a x hx y hy => by
    simp only [φ, hcadd a x hx y hy, hcadd' a x hx y hy]; ring
  have hφsmul : ∀ a (t : E), ∀ x ∈ X, φ a (t • x) = t * φ a x := fun a t x hx => by
    simp only [φ, hcsmul a t x hx, hcsmul' a t x hx]; ring
  let ψ : Fin r → (Λ →ₗ[𝓞 E] E) := fun a =>
    { toFun := fun y => φ a (ρ y : V)
      map_add' := fun y₁ y₂ => by
        rw [map_add, Submodule.coe_add, hφadd a _ (hρX y₁) _ (hρX y₂)]
      map_smul' := fun o y => by
        rw [map_smul, Submodule.coe_smul, ← algebraMap_smul E o, hφsmul a _ _ (hρX y),
          RingHom.id_apply, Algebra.smul_def] }
  choose w hw using fun a => riesz h hs hnd Λ hfg hsp (ψ a)
  have hwX : ∀ a, ∀ x ∈ X, h (w a) x = φ a x := by
    intro a x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem Λ hsp x
    have hdX : d • x ∈ X := by rw [← algebraMap_smul E d x]; exact X.smul_mem _ hx
    have h1 := hw a (d • x) hdx
    have h2 : ρ ⟨d • x, hdx⟩ = ⟨d • x, hdx⟩ := hρid _ hdX
    have h3 : ψ a ⟨d • x, hdx⟩ = φ a (d • x) := by
      show φ a (ρ ⟨d • x, hdx⟩ : V) = _
      rw [h2]
    rw [h3, ← algebraMap_smul E d x, hr, hφsmul a _ x hx] at h1
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1
  have hwJ : ∀ a, ∀ y ∈ Λ, h (w a) y ∈ J a := by
    intro a y hy
    rw [hw a y hy]
    show φ a (ρ ⟨y, hy⟩ : V) ∈ J a
    have hm := hJ2 _ (ρ ⟨y, hy⟩).2 (hρX _) a
    exact (J a).sub_mem hm.2 hm.1

  have key : ∀ b, ∑ a, h (w a) (e' b) • e a = e b - e' b := by
    intro b
    have h1 : ∀ a, h (w a) (e' b) = (if a = b then 1 else 0) - c a (e' b) := fun a => by
      rw [hwX a _ (he' b)]
      simp only [φ, hδ' a b]
    simp only [h1, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hc _ (he' b)]

  let G : Fin r → Fin r → E := fun a b => h (w a) (w b)
  let k : Fin r → Fin r → E := fun a b => if a < b then -1 else if a = b then -(θ : E) else 0
  let s : Fin r → Fin r → E := fun a b => k a b * G a b
  have hkint : ∀ a b, k a b ∈ (1 : Submodule (𝓞 E) E) := by
    intro a b
    simp only [k]
    split_ifs
    · exact Submodule.mem_one.2 ⟨-1, by simp⟩
    · exact Submodule.mem_one.2 ⟨-θ, by simp⟩
    · exact Submodule.zero_mem _
  have hsG : ∀ a b, G a b + s a b + star (s b a) = 0 := by
    intro a b
    have hG : star (G b a) = G a b := (hsy (w b) (w a)).symm
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h1 : ¬ b < a := not_lt.2 hab.le
      have h2 : b ≠ a := hab.ne'
      simp only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_zero]
      ring
    · have hGs : star (G a a) = G a a := hG
      simp only [s, k, lt_irrefl, if_false, if_true, star_mul', star_neg, hGs]
      linear_combination (-(G a a)) * hθ
    · have h1 : ¬ a < b := not_lt.2 hab.le
      have h2 : a ≠ b := hab.ne'
      simp only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_mul', star_neg, star_one, hG]
      ring

  let cc : Fin r → (V →ₗ[E] E) := fun a => -(h (w a)) + ∑ b, s a b • h (e b)
  have hcc : ∀ a v, cc a v = -h (w a) v + ∑ b, s a b * h (e b) v := fun a v => by
    simp [cc]
  let nL : V →ₗ[E] V :=
    LinearMap.id + ∑ a, (h (e a)).smulRight (w a) + ∑ a, (cc a).smulRight (e' a)
  have hn : ∀ v, nL v = v + ∑ a, h (e a) v • w a + ∑ a, cc a v • e' a := fun v => by
    simp [nL]
  have hBX : ∀ v, ∑ a, cc a v • e' a ∈ X := fun v =>
    X.sum_mem fun a _ => X.smul_mem _ (he' a)

  have K1 : ∀ v a, h (v + ∑ b, h (e b) v • w b) (e' a) = star (h (e a) v) := by
    intro v a
    have hk := congrArg (h v) (key a)
    rw [map_sum, map_sub] at hk
    simp only [hr] at hk
    rw [map_add, LinearMap.add_apply, LinearMap.map_sum₂]
    simp only [hl]
    have e1 : h v (e' a) = h v (e a) - ∑ b, h (w b) (e' a) * h v (e b) := by rw [hk]; ring
    rw [e1, ← hsy]
    have e2 : ∑ b, star (h (e b) v) * h (w b) (e' a) = ∑ b, h (w b) (e' a) * h v (e b) :=
      Finset.sum_congr rfl fun b _ => by rw [hsy (e b) v, mul_comm]
    rw [e2]
    ring

  have hiso_n : ∀ v v', h (nL v) (nL v') = h v v' := by
    intro v v'
    rw [hn, hn]
    set P := v + ∑ b, h (e b) v • w b with hP
    set P' := v' + ∑ b, h (e b) v' • w b with hP'
    have hBB : h (∑ a, cc a v • e' a) (∑ a, cc a v' • e' a) = 0 := hiso _ (hBX v) _ (hBX v')
    have hPB : h P (∑ a, cc a v' • e' a) = ∑ a, cc a v' * star (h (e a) v) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hr, K1]
    have hBP : h (∑ a, cc a v • e' a) P' = ∑ a, star (cc a v) * h (e a) v' := by
      rw [LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hl, hsy P' (e' a), K1, star_star]
    have hPP : h P P' = h v v' + ((∑ a, h (e a) v' * star (h (w a) v)) +
        (∑ a, star (h (e a) v) * h (w a) v') +
        (∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b))) := by
      have e1 : ∀ a, h v (w a) = star (h (w a) v) := fun a => hsy _ _
      have hdbl : (∑ b, h (e b) v' * ∑ a, star (h (e a) v) * h (w a) (w b)) =
          ∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp only [G]; ring
      rw [hP, hP']
      simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, e1, RingHom.id_apply, mul_add]
      rw [Finset.sum_add_distrib, hdbl]
      ring
    simp only [map_add, LinearMap.add_apply]
    rw [hBB, hPB, hBP, hPP]
    have := alg_identity (fun a => h (e a) v) (fun a => h (e a) v') (fun a => h (w a) v)
      (fun a => h (w a) v') G s hsG
    simp only [hcc]
    linear_combination this
  have hinj : Function.Injective nL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine hnd.1 v fun y => ?_
    rw [← hiso_n v y, hv, LinearMap.map_zero₂]

  have P1 : ∀ a, ∀ v ∈ Λ, h (e a) v • w a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hsy (w a) y]
    have ht := (hJ1 a _ (hwJ a y hy)).1
    have := intΛ _ ht v hv
    rw [hl] at this
    rwa [mul_comm]
  have P1' : ∀ a, ∀ v ∈ Λ, h (e' a) v • w a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hsy (w a) y]
    have ht := (hJ1 a _ (hwJ a y hy)).2
    have := intΛ _ ht v hv
    rw [hl] at this
    rwa [mul_comm]
  have P2 : ∀ a, ∀ v ∈ Λ, cc a v • e' a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hcc, hsy (e' a) y]
    have t1 : h (w a) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E) := by
      have := intΛ _ (P1' a y hy) v hv
      rwa [hl, mul_comm] at this
    have t2 : ∀ b, s a b * h (e b) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E) := by
      intro b
      have := intΛ _ (P1' a y hy) _ (P1 b v hv)
      rw [hl, hr] at this
      have e1 : s a b * h (e b) v * star (h (e' a) y) =
          k a b * (star (h (e' a) y) * (h (e b) v * h (w a) (w b))) := by simp only [s, G]; ring
      rw [e1]
      exact one_mul_mem (hkint a b) this
    rw [add_mul, Finset.sum_mul, neg_mul]
    exact Submodule.add_mem _ (Submodule.neg_mem _ t1) (Submodule.sum_mem _ fun b _ => t2 b)
  have hint : ∀ v ∈ Λ, nL v ∈ Λ := by
    intro v hv
    rw [hn]
    exact Λ.add_mem (Λ.add_mem hv (Λ.sum_mem fun a _ => P1 a v hv)) (Λ.sum_mem fun a _ => P2 a v hv)

  let n : V ≃ₗ[E] V := LinearEquiv.ofInjectiveEndo nL hinj
  have hnapp : ∀ v, n v = nL v := fun v => rfl
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · show ∀ x y, h (n x) (n y) = h x y
    intro x y
    rw [hnapp, hnapp, hiso_n]
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hint v hv
    · intro y hy
      refine ⟨n.symm y, ?_, by simp⟩
      rw [SetLike.mem_coe, memΛ]
      intro x hx
      have e : h x (n.symm y) = h (nL x) y := by
        rw [← hiso_n x (n.symm y), ← hnapp (n.symm y), LinearEquiv.apply_symm_apply]
      rw [e]
      exact intΛ _ (hint x hx) y hy
  · intro a
    rw [hnapp, hn]
    have h0 : ∀ b, h (e b) (e a) = 0 := fun b => hiso _ (he b) _ (he a)
    have h1 : ∀ b, cc b (e a) = (if b = a then 1 else 0) - c' b (e a) := by
      intro b
      rw [hcc, hwX b _ (he a)]
      simp only [h0, mul_zero, Finset.sum_const_zero, add_zero, φ, hδ b a]
      ring
    simp only [h0, zero_smul, Finset.sum_const_zero, add_zero, h1, sub_smul, ite_smul, one_smul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hc' _ (he a)]
    abel
  · intro v hv
    rw [hnapp, hn]
    have h0 : ∀ a, h (e a) v = 0 := fun a => hv _ (he a)
    simp only [h0, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact hBX v

end PI.UnitaryGroupMassFormula.IdCellInSW
