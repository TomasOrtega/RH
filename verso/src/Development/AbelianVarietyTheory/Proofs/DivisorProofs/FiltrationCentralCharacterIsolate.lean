import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory

namespace CentralStepEigen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hpow : ∀ n : ℕ, (T ^ n) w - a ^ n • w ∈ A`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Establish `e : (T ^ (n + 1)) w - a ^ (n + 1) • w = T ((T ^ n) w - a ^ n • w) + a ^ n • (T w - a • w)`. Rewrite using `[pow_succ', Module.End.mul_apply, map_sub, map_smul, smul_sub, pow_succ, mul_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `A.add_mem (hA _ ih) (A.smul_mem _ hw)`.

Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Establish `e : Polynomial.aeval T (p + q) w - (p + q).eval a • w = (Polynomial.aeval T p w - p.eval a • w) + (Polynomial.aeval T q w - q.eval a • w)`. Rewrite using `[map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `A.add_mem hp hq`. Consider the case `monomial n c`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, mul_smul, ← smul_sub]`. Conclude with `A.smul_mem c (hpow n)`.
-/
theorem aeval_sub_mem (T : Module.End ℂ V) (A : Submodule ℂ V) (hA : ∀ x ∈ A, T x ∈ A) (a : ℂ)
    (w : V) (hw : T w - a • w ∈ A) (f : Polynomial ℂ) :
    Polynomial.aeval T f w - f.eval a • w ∈ A := by
  have hpow : ∀ n : ℕ, (T ^ n) w - a ^ n • w ∈ A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (T ^ (n + 1)) w - a ^ (n + 1) • w = T ((T ^ n) w - a ^ n • w) + a ^ n • (T w - a • w) := by
        rw [pow_succ', Module.End.mul_apply, map_sub, map_smul, smul_sub, pow_succ, mul_smul]
        abel
      rw [e]
      exact A.add_mem (hA _ ih) (A.smul_mem _ hw)
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval T (p + q) w - (p + q).eval a • w =
        (Polynomial.aeval T p w - p.eval a • w) + (Polynomial.aeval T q w - q.eval a • w) := by
      rw [map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]
      abel
    rw [e]
    exact A.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, mul_smul, ← smul_sub]
    exact A.smul_mem c (hpow n)

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]`. Consider the case `monomial n c`. Establish `hc : Commute U (T ^ n)` using `(Commute.pow_right h n)`. Rewrite using `[Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, hc.eq]`.
-/
theorem aeval_apply_comm (T U : Module.End ℂ V) (h : U * T = T * U) (f : Polynomial ℂ) (v : V) :
    Polynomial.aeval T f (U v) = U (Polynomial.aeval T f v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    have hc : Commute U (T ^ n) := (Commute.pow_right h n)
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, ← Module.End.mul_apply,
      ← Module.End.mul_apply, hc.eq]

end CentralStepEigen

open CentralStepEigen in

/- English proof (translation)
Introduce `G V X _ _ _ _ _ ρ σ N S hmono hbot htop z hz t₀ a hΨ hσ hq`. Take `⟨Ψ⟩` from `hΨ`. Establish `ht0` using `t₀.isLt`. Use `set B := S t₀.succ with hBdef`. Use `set A := S t₀.castSucc with hAdef`.

Use `set T : Module.End ℂ V := ρ z with hT`. Establish `hq' : ∀ t : Fin N, ∃ q : Polynomial ℂ, q.eval a ≠ 0 ∧ (t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, Polynomial.aeval T q w ∈ (S t.castSucc).toSubmodule)`. Introduce `t`. Distinguish the cases in `ht : t = t₀`. Conclude with `⟨1, by simp, fun h => (h ht).elim⟩`.

Take `⟨q, h1, h2⟩` from `hq t ht`. Conclude with `⟨q, h1, fun _ => h2⟩`. Use `choose q hq1 hq2 using hq'`. Set `qn : ℕ → Polynomial ℂ` to `fun i => if h : i < N then q ⟨i, h⟩ else 1`. Establish `hqn : ∀ i, (qn i).eval a ≠ 0`.

Introduce `i`. Distinguish the cases in `h : i < N`. Simplify using `only [qn, dif_pos h]`. Conclude with `hq1 _`. Simplify using `[qn, h]`.

Establish `hZ : ∀ y, subQuot B A z y = a • y`. Introduce `y`. Apply `Ψ.toLinearEquiv.injective` to reduce the goal to its premises. Establish `h1` using `Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y`. Rewrite using `[Representation.Equiv.toLinearEquiv_apply, h1, hσ, map_smul, Representation.Equiv.toLinearEquiv_apply]`.

Establish `hkey : ∀ w ∈ B.toSubmodule, T w - a • w ∈ A.toSubmodule`. Introduce `w hw`. Establish `h` using `hZ (Submodule.Quotient.mk ⟨w, hw⟩)`. Establish `e2 : subQuot B A z (Submodule.Quotient.mk ⟨w, hw⟩) = Submodule.Quotient.mk ⟨ρ z w, B.apply_mem_toSubmodule z hw⟩` using `rfl`. Rewrite `h` using `[e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`.

Simplify using `using h`. Establish `hBf : ∀ f : Polynomial ℂ, ∀ w ∈ B.toSubmodule, Polynomial.aeval T f w - f.eval a • w ∈ A.toSubmodule` using `fun f w hw => aeval_sub_mem T A.toSubmodule (fun x hx => A.apply_mem_toSubmodule z hx) a w (hkey w hw) f`. Establish `hEig : ∀ f : Polynomial ℂ, ∀ v, T v = a • v → Polynomial.aeval T f v = f.eval a • v`. Introduce `f v hv`. Establish `h` using `aeval_sub_mem T ⊥ (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; simp [hx]) a v (by rw [hv, sub_self]; exact Submodule.zero_mem _) f`.

Rewrite `h` using `[Submodule.mem_bot, sub_eq_zero]`. Conclude with `h`. Establish `L1 : ∀ j (hj : j ≤ t₀.val), ∀ v ∈ (S ⟨j, by omega⟩).toSubmodule, Polynomial.aeval T (∏ i ∈ Finset.range j, qn i) v = 0`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `hj v hv`. Establish `e : (⟨0, by omega⟩ : Fin (N + 1)) = 0` using `rfl`. Rewrite `hv` using `[e, hbot]`. Establish `hv0 : v = 0` using `(Submodule.mem_bot ℂ).1 hv`.

Simplify using `[hv0]`. Consider the case `succ j ih`. Introduce `hj v hv`. Set `t : Fin N` to `⟨j, by omega⟩`. Establish `ht : t ≠ t₀` using `fun e => by`.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [t] at this`. Use linear arithmetic over natural numbers and integers. Establish `hvs : v ∈ (S t.succ).toSubmodule`. Establish `: t.succ = ⟨j + 1, by omega⟩` using `by ext; simp [t]`.

Rewrite using `[this]`. Conclude with `hv`. Establish `h2` using `hq2 t ht v hvs`. Establish `e3 : qn j = q t` using `by show (if h : j < N then q ⟨j, h⟩ else 1) = q t`. Rewrite using `[dif_pos (show j < N by omega)]`.

Rewrite using `[Finset.prod_range_succ, Polynomial.aeval_mul, Module.End.mul_apply, e3]`. Conclude with `ih (by omega) _ h2`. Establish `L2 : ∀ m (h : t₀.val + 1 + m < N + 1), ∀ v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule, Polynomial.aeval T (∏ i ∈ Finset.range m, qn (t₀.val + 1 + i)) v ∈ B.toSubmodule`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero`. Introduce `h v hv`. Establish `e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ` using `by ext; simp`. Rewrite `hv` using `[e]`. Simplify using `using hv`.

Consider the case `succ m ih`. Introduce `h v hv`. Set `t : Fin N` to `⟨t₀.val + 1 + m, by omega⟩`. Establish `ht : t ≠ t₀` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `only [t] at this`. Use linear arithmetic over natural numbers and integers. Establish `hvs : v ∈ (S t.succ).toSubmodule`. Establish `: t.succ = ⟨t₀.val + 1 + (m + 1), h⟩` using `by ext; simp [t]; omega`. Rewrite using `[this]`.

Conclude with `hv`. Establish `h2` using `hq2 t ht v hvs`. Establish `e3 : qn (t₀.val + 1 + m) = q t` using `by show (if h : t₀.val + 1 + m < N then q ⟨t₀.val + 1 + m, h⟩ else 1) = q t`. Rewrite using `[dif_pos (show t₀.val + 1 + m < N by omega)]`. Rewrite using `[Finset.prod_range_succ, Polynomial.aeval_mul, Module.End.mul_apply, e3]`.

Conclude with `ih (by omega) _ h2`. Use `set M := N - (t₀.val + 1) with hMdef`. Use `set Qg := ∏ i ∈ Finset.range M, qn (t₀.val + 1 + i) with hQgdef`. Use `set Qs := ∏ i ∈ Finset.range t₀.val, qn i with hQsdef`. Establish `hQg : Qg.eval a ≠ 0`.

Rewrite using `[hQgdef, Polynomial.eval_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun i _ => hqn _)`. Establish `hQs : Qs.eval a ≠ 0`. Rewrite using `[hQsdef, Polynomial.eval_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun i _ => hqn _)`.

Establish `hM : ∀ v, Polynomial.aeval T Qg v ∈ B.toSubmodule`. Introduce `v`. Use `L2 M (by omega) v ?_` and prove the remaining obligations. Establish `e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N` using `by ext; simp; omega`. Rewrite using `[e, htop]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hcomm : ∀ (f : Polynomial ℂ) g v, Polynomial.aeval T f (ρ g v) = ρ g (Polynomial.aeval T f v)`. Introduce `f g v`. Use `aeval_apply_comm T (ρ g) ?_ f v` and prove the remaining obligations. Rewrite using `[hT, ← map_mul, ← map_mul, hz]`.

Set `plin : V →ₗ[ℂ] X` to `Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM`. Establish `hφ : ∀ g v, plin (ρ g v) = σ g (plin v)`. Introduce `g v`. Establish `e6 : (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM) (ρ g v) = B.toRepresentation g (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM v)` using `Subtype.ext (hcomm Qg g v)`. Use `show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ _ hM (ρ g v))) = σ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ _ hM v)))`.

Establish `e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype) (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM v)) = subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule _ hM v))` using `rfl`. Rewrite using `[e6, e8]`. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _`. Set `p : ρ.IntertwiningMap σ` to `plin.intertwiningMap_of_isIntertwiningMap ρ σ hφ`. Establish `hp : ∀ v, p v = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg v, hM v⟩)` using `fun v => rfl`.

Use `⟨p, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨⟨b, hb⟩, hx⟩` from `Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)`. Use `set u := Polynomial.aeval T Qs b with hudef`. Establish `hu : T u = a • u`.

Establish `h1 : Polynomial.aeval T Qs (T b - a • b) = 0` using `L1 t₀.val le_rfl _ (hkey b hb)`. Establish `h2 : Polynomial.aeval T Qs (T b) = T (Polynomial.aeval T Qs b)` using `aeval_apply_comm T T rfl Qs b`. Rewrite `h1` using `[map_sub, map_smul, h2]`. Conclude with `sub_eq_zero.1 h1`. Use `set c := (Qg * Qs).eval a with hcdef`.

Establish `hc : c ≠ 0` using `by rw [hcdef, Polynomial.eval_mul]; exact mul_ne_zero hQg hQs`. Establish `hpu : p u = c • y`. Establish `e1 : Polynomial.aeval T Qg u = Polynomial.aeval T (Qg * Qs) b`. Rewrite using `[Polynomial.aeval_mul, Module.End.mul_apply]`. Establish `e2` using `hBf (Qg * Qs) b hb`.

Rewrite using `[hp]`. Establish `e3 : (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg u, hM u⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) = c • Submodule.Quotient.mk ⟨b, hb⟩`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]`. Use `show Polynomial.aeval T Qg u - c • b ∈ A.toSubmodule`. Rewrite using `[e1]`.

Conclude with `e2`. Rewrite using `[e3, map_smul, hx, LinearEquiv.apply_symm_apply]`. Use `⟨c⁻¹ • u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hu, smul_comm]`. Rewrite using `[map_smul, hpu, smul_smul, inv_mul_cancel₀ hc, one_smul]`.

Introduce `v hv hpv`. Establish `hQgv` using `hEig Qg v hv`. Establish `hvA : v ∈ A.toSubmodule`. Rewrite `hpv` using `[hp]`. Establish `h1 : (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg v, hM v⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) = 0` using `(LinearEquiv.map_eq_zero_iff _).1 hpv`.

Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Establish `h1' : Polynomial.aeval T Qg v ∈ A.toSubmodule` using `h1`. Rewrite `h1'` using `[hQgv]`. Conclude with `(A.toSubmodule.smul_mem_iff hQg).1 h1'`. Establish `h` using `L1 t₀.val le_rfl v hvA`.

Rewrite `h` using `[hEig Qs v hv]`. Conclude with `(smul_eq_zero.1 h).resolve_left hQs`.
-/
theorem exists_intertwining_bijOn_eigen_of_central_step :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G X) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) → ∀ (t₀ : Fin N) (a : ℂ),
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv σ) → (∀ y, σ z y = a • y) →
    (∀ t, t ≠ t₀ → ∃ q : Polynomial ℂ, q.eval a ≠ 0 ∧
      ∀ w ∈ (S t.succ).toSubmodule, Polynomial.aeval (ρ z) q w ∈ (S t.castSucc).toSubmodule) →
    ∃ p : ρ.IntertwiningMap σ, (∀ y, ∃ v, ρ z v = a • v ∧ p v = y) ∧
      ∀ v, ρ z v = a • v → p v = 0 → v = 0 := by
  intro G V X _ _ _ _ _ ρ σ N S hmono hbot htop z hz t₀ a hΨ hσ hq
  obtain ⟨Ψ⟩ := hΨ
  have ht0 := t₀.isLt
  set B := S t₀.succ with hBdef
  set A := S t₀.castSucc with hAdef
  set T : Module.End ℂ V := ρ z with hT
  have hq' : ∀ t : Fin N, ∃ q : Polynomial ℂ, q.eval a ≠ 0 ∧ (t ≠ t₀ →
      ∀ w ∈ (S t.succ).toSubmodule, Polynomial.aeval T q w ∈ (S t.castSucc).toSubmodule) := by
    intro t
    by_cases ht : t = t₀
    · exact ⟨1, by simp, fun h => (h ht).elim⟩
    · obtain ⟨q, h1, h2⟩ := hq t ht
      exact ⟨q, h1, fun _ => h2⟩
  choose q hq1 hq2 using hq'
  let qn : ℕ → Polynomial ℂ := fun i => if h : i < N then q ⟨i, h⟩ else 1
  have hqn : ∀ i, (qn i).eval a ≠ 0 := by
    intro i
    by_cases h : i < N
    · simp only [qn, dif_pos h]; exact hq1 _
    · simp [qn, h]

  have hZ : ∀ y, subQuot B A z y = a • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hσ, map_smul,
      Representation.Equiv.toLinearEquiv_apply]
  have hkey : ∀ w ∈ B.toSubmodule, T w - a • w ∈ A.toSubmodule := by
    intro w hw
    have h := hZ (Submodule.Quotient.mk ⟨w, hw⟩)
    have e2 : subQuot B A z (Submodule.Quotient.mk ⟨w, hw⟩) =
        Submodule.Quotient.mk ⟨ρ z w, B.apply_mem_toSubmodule z hw⟩ := rfl
    rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h
    simpa using h
  have hBf : ∀ f : Polynomial ℂ, ∀ w ∈ B.toSubmodule,
      Polynomial.aeval T f w - f.eval a • w ∈ A.toSubmodule := fun f w hw =>
    aeval_sub_mem T A.toSubmodule (fun x hx => A.apply_mem_toSubmodule z hx) a w (hkey w hw) f
  have hEig : ∀ f : Polynomial ℂ, ∀ v, T v = a • v → Polynomial.aeval T f v = f.eval a • v := by
    intro f v hv
    have h := aeval_sub_mem T ⊥ (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; simp [hx]) a v
      (by rw [hv, sub_self]; exact Submodule.zero_mem _) f
    rw [Submodule.mem_bot, sub_eq_zero] at h
    exact h

  have L1 : ∀ j (hj : j ≤ t₀.val), ∀ v ∈ (S ⟨j, by omega⟩).toSubmodule,
      Polynomial.aeval T (∏ i ∈ Finset.range j, qn i) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro hj v hv
      have e : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
      rw [e, hbot] at hv
      have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
      simp [hv0]
    | succ j ih =>
      intro hj v hv
      let t : Fin N := ⟨j, by omega⟩
      have ht : t ≠ t₀ := fun e => by
        have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨j + 1, by omega⟩ := by ext; simp [t]
        rw [this]; exact hv
      have h2 := hq2 t ht v hvs
      have e3 : qn j = q t := by
        show (if h : j < N then q ⟨j, h⟩ else 1) = q t
        rw [dif_pos (show j < N by omega)]
      rw [Finset.prod_range_succ, Polynomial.aeval_mul, Module.End.mul_apply, e3]
      exact ih (by omega) _ h2

  have L2 : ∀ m (h : t₀.val + 1 + m < N + 1), ∀ v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule,
      Polynomial.aeval T (∏ i ∈ Finset.range m, qn (t₀.val + 1 + i)) v ∈ B.toSubmodule := by
    intro m
    induction m with
    | zero =>
      intro h v hv
      have e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ := by ext; simp
      rw [e] at hv
      simpa using hv
    | succ m ih =>
      intro h v hv
      let t : Fin N := ⟨t₀.val + 1 + m, by omega⟩
      have ht : t ≠ t₀ := fun e => by
        have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨t₀.val + 1 + (m + 1), h⟩ := by ext; simp [t]; omega
        rw [this]; exact hv
      have h2 := hq2 t ht v hvs
      have e3 : qn (t₀.val + 1 + m) = q t := by
        show (if h : t₀.val + 1 + m < N then q ⟨t₀.val + 1 + m, h⟩ else 1) = q t
        rw [dif_pos (show t₀.val + 1 + m < N by omega)]
      rw [Finset.prod_range_succ, Polynomial.aeval_mul, Module.End.mul_apply, e3]
      exact ih (by omega) _ h2
  set M := N - (t₀.val + 1) with hMdef
  set Qg := ∏ i ∈ Finset.range M, qn (t₀.val + 1 + i) with hQgdef
  set Qs := ∏ i ∈ Finset.range t₀.val, qn i with hQsdef
  have hQg : Qg.eval a ≠ 0 := by
    rw [hQgdef, Polynomial.eval_prod]; exact Finset.prod_ne_zero_iff.2 (fun i _ => hqn _)
  have hQs : Qs.eval a ≠ 0 := by
    rw [hQsdef, Polynomial.eval_prod]; exact Finset.prod_ne_zero_iff.2 (fun i _ => hqn _)
  have hM : ∀ v, Polynomial.aeval T Qg v ∈ B.toSubmodule := by
    intro v
    refine L2 M (by omega) v ?_
    have e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N := by ext; simp; omega
    rw [e, htop]
    trivial
  have hcomm : ∀ (f : Polynomial ℂ) g v, Polynomial.aeval T f (ρ g v) = ρ g (Polynomial.aeval T f v) := by
    intro f g v
    refine aeval_apply_comm T (ρ g) ?_ f v
    rw [hT, ← map_mul, ← map_mul, hz]
  let plin : V →ₗ[ℂ] X := Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ
    LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM
  have hφ : ∀ g v, plin (ρ g v) = σ g (plin v) := by
    intro g v
    have e6 : (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM) (ρ g v) =
        B.toRepresentation g (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM v) :=
      Subtype.ext (hcomm Qg g v)
    show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ _ hM (ρ g v))) =
      σ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ _ hM v)))
    have e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype)
        (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM v)) =
        subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule _ hM v)) := rfl
    rw [e6, e8]
    exact Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _
  let p : ρ.IntertwiningMap σ := plin.intertwiningMap_of_isIntertwiningMap ρ σ hφ
  have hp : ∀ v, p v = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg v, hM v⟩) :=
    fun v => rfl
  refine ⟨p, ?_, ?_⟩
  · intro y
    obtain ⟨⟨b, hb⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)
    set u := Polynomial.aeval T Qs b with hudef
    have hu : T u = a • u := by
      have h1 : Polynomial.aeval T Qs (T b - a • b) = 0 := L1 t₀.val le_rfl _ (hkey b hb)
      have h2 : Polynomial.aeval T Qs (T b) = T (Polynomial.aeval T Qs b) :=
        aeval_apply_comm T T rfl Qs b
      rw [map_sub, map_smul, h2] at h1
      exact sub_eq_zero.1 h1
    set c := (Qg * Qs).eval a with hcdef
    have hc : c ≠ 0 := by rw [hcdef, Polynomial.eval_mul]; exact mul_ne_zero hQg hQs
    have hpu : p u = c • y := by
      have e1 : Polynomial.aeval T Qg u = Polynomial.aeval T (Qg * Qs) b := by
        rw [Polynomial.aeval_mul, Module.End.mul_apply]
      have e2 := hBf (Qg * Qs) b hb
      rw [hp]
      have e3 : (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg u, hM u⟩ :
          B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
          c • Submodule.Quotient.mk ⟨b, hb⟩ := by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
        show Polynomial.aeval T Qg u - c • b ∈ A.toSubmodule
        rw [e1]
        exact e2
      rw [e3, map_smul, hx, LinearEquiv.apply_symm_apply]
    refine ⟨c⁻¹ • u, ?_, ?_⟩
    · rw [map_smul, hu, smul_comm]
    · rw [map_smul, hpu, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro v hv hpv
    have hQgv := hEig Qg v hv
    have hvA : v ∈ A.toSubmodule := by
      rw [hp] at hpv
      have h1 : (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg v, hM v⟩ :
          B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) = 0 :=
        (LinearEquiv.map_eq_zero_iff _).1 hpv
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
      have h1' : Polynomial.aeval T Qg v ∈ A.toSubmodule := h1
      rw [hQgv] at h1'
      exact (A.toSubmodule.smul_mem_iff hQg).1 h1'
    have h := L1 t₀.val le_rfl v hvA
    rw [hEig Qs v hv] at h
    exact (smul_eq_zero.1 h).resolve_left hQs

end GlobalTheory
