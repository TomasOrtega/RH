import Mathlib
open NumberField

namespace GlobalTheory.GensModNsmul

/- English proof (translation)
Establish `hfg : (LinearMap.range π).FG`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Take `⟨d, hd, hint⟩` from `FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hfg`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`.

Establish `hd0' : (algebraMap (𝓞 E) E d) ≠ 0` using `by simpa using hd0`. Use `set I : Ideal (𝓞 E) := Submodule.comap (Algebra.linearMap (𝓞 E) E) (LinearMap.range (d • π)) with hI`. Establish `hmem : ∀ a : 𝓞 E, a ∈ I ↔ ∃ x : N, d • π x = algebraMap (𝓞 E) E a`. Introduce `a`. Simplify using `[hI]`.

Establish `hM0 : (M : 𝓞 E) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`. Establish `key : ∃ a ∈ I, Ideal.span {(M : 𝓞 E)} * I ⊔ Ideal.span {a} = I`. Distinguish the cases in `h : I = ⊥`. Conclude with `⟨0, I.zero_mem, by simp [h]⟩`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(M : 𝓞 E)} * I) (J := I) Ideal.mul_le_right (mul_ne_zero (by simpa using hM0) h)`.

Use `⟨a, ?_, ha⟩` and prove the remaining obligations. Rewrite using `[← ha]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Take `⟨a, haI, ha⟩` from `key`. Take `⟨l, hl⟩` from `(hmem a).1 haI`.

Use `⟨l, fun x => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hint (π x) ⟨x, rfl⟩`. Establish `hbI : b ∈ I` using `(hmem b).2 ⟨x, hb.symm⟩`. Rewrite `hbI` using `[← ha, Submodule.mem_sup]`. Take `⟨u, hu, v, hv, huv⟩` from `hbI`.

Take `⟨c, hc, rfl⟩` from `Ideal.mem_span_singleton_mul.1 hu`. Take `⟨o, rfl⟩` from `Ideal.mem_span_singleton'.1 hv`. Take `⟨y, hy⟩` from `(hmem c).1 hc`. Use `⟨o, y, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hd0'` to reduce the goal to its premises.

Rewrite `hb`, `hl`, `hy` using `[Algebra.smul_def]`. Rewrite using `[← hb, ← huv, Algebra.smul_def, nsmul_eq_mul, map_add, map_mul, map_mul, map_natCast, ← hl, ← hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_gen_mod_nsmul_of_linearMap (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N] (π : N →ₗ[𝓞 E] E) :
    ∃ l : N, ∀ x : N, ∃ o : 𝓞 E, ∃ y : N, π x = o • π l + M • π y := by
  have hfg : (LinearMap.range π).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (algebraMap (𝓞 E) E d) ≠ 0 := by simpa using hd0
  set I : Ideal (𝓞 E) := Submodule.comap (Algebra.linearMap (𝓞 E) E) (LinearMap.range (d • π)) with hI
  have hmem : ∀ a : 𝓞 E, a ∈ I ↔ ∃ x : N, d • π x = algebraMap (𝓞 E) E a := by
    intro a; simp [hI]
  have hM0 : (M : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have key : ∃ a ∈ I, Ideal.span {(M : 𝓞 E)} * I ⊔ Ideal.span {a} = I := by
    by_cases h : I = ⊥
    · exact ⟨0, I.zero_mem, by simp [h]⟩
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
        (I := Ideal.span {(M : 𝓞 E)} * I) (J := I) Ideal.mul_le_right
        (mul_ne_zero (by simpa using hM0) h)
      refine ⟨a, ?_, ha⟩
      rw [← ha]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨a, haI, ha⟩ := key
  obtain ⟨l, hl⟩ := (hmem a).1 haI
  refine ⟨l, fun x => ?_⟩
  obtain ⟨b, hb⟩ := hint (π x) ⟨x, rfl⟩
  have hbI : b ∈ I := (hmem b).2 ⟨x, hb.symm⟩
  rw [← ha, Submodule.mem_sup] at hbI
  obtain ⟨u, hu, v, hv, huv⟩ := hbI
  obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 hu
  obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  obtain ⟨y, hy⟩ := (hmem c).1 hc
  refine ⟨o, y, ?_⟩
  apply mul_left_cancel₀ hd0'
  rw [Algebra.smul_def] at hb hl hy
  rw [← hb, ← huv, Algebra.smul_def, nsmul_eq_mul, map_add, map_mul, map_mul, map_natCast, ← hl, ← hy]
  ring

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `N _ _ _ f hf`. Use `⟨Fin.elim0, fun x => ⟨Fin.elim0, 0, ?_⟩⟩` and prove the remaining obligations. Simplify using `using hf (Subsingleton.elim (f x) (f 0))`.

Consider the case `succ r ih`. Introduce `N _ _ _ f hf`. Set `π : N →ₗ[𝓞 E] E` to `(LinearMap.proj 0) ∘ₗ f`. Take `⟨l, hl⟩` from `exists_gen_mod_nsmul_of_linearMap E M hM N π`. Set `f' : LinearMap.ker π →ₗ[𝓞 E] (Fin r → E)` to `LinearMap.pi fun i => (LinearMap.proj i.succ) ∘ₗ f ∘ₗ (LinearMap.ker π).subtype`.

Establish `hf' : Function.Injective f'`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hf` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[Submodule.coe_zero, map_zero]`. Conclude with `x.2`. Simplify `congrFun hx j` using `[f']`.

Take `⟨e, he⟩` from `ih (LinearMap.ker π) f' hf'`. Use `⟨Fin.cons l (fun i => (e i : N)), fun x => ?_⟩` and prove the remaining obligations. Take `⟨o, y, hoy⟩` from `hl x`. Establish `hk : x - o • l - M • y ∈ LinearMap.ker π`. Rewrite using `[LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, hoy]`.

Normalize the expressions using the abelian group laws. Take `⟨o', y', h'⟩` from `he ⟨_, hk⟩`. Use `⟨Fin.cons o o', y + y', ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Subtype.val h'`. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_smul_of_tower] at h2`.

Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_add]`. Establish `: x = o • l + M • y + (x - o • l - M • y)` using `by abel`. Rewrite using `[this, h2]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_gens_mod_nsmul_of_injective (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (r : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N]
    (f : N →ₗ[𝓞 E] (Fin r → E)), Function.Injective f →
    ∃ e : Fin r → N, ∀ x : N, ∃ o : Fin r → 𝓞 E, ∃ y : N, x = ∑ i, o i • e i + M • y := by
  induction r with
  | zero =>
    intro N _ _ _ f hf
    refine ⟨Fin.elim0, fun x => ⟨Fin.elim0, 0, ?_⟩⟩
    simpa using hf (Subsingleton.elim (f x) (f 0))
  | succ r ih =>
    intro N _ _ _ f hf
    let π : N →ₗ[𝓞 E] E := (LinearMap.proj 0) ∘ₗ f
    obtain ⟨l, hl⟩ := exists_gen_mod_nsmul_of_linearMap E M hM N π
    let f' : LinearMap.ker π →ₗ[𝓞 E] (Fin r → E) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ) ∘ₗ f ∘ₗ (LinearMap.ker π).subtype
    have hf' : Function.Injective f' := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Submodule.coe_zero, map_zero]; exact x.2
      · simpa [f'] using congrFun hx j
    obtain ⟨e, he⟩ := ih (LinearMap.ker π) f' hf'
    refine ⟨Fin.cons l (fun i => (e i : N)), fun x => ?_⟩
    obtain ⟨o, y, hoy⟩ := hl x
    have hk : x - o • l - M • y ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, hoy]; abel
    obtain ⟨o', y', h'⟩ := he ⟨_, hk⟩
    refine ⟨Fin.cons o o', y + y', ?_⟩
    have h2 := congrArg Subtype.val h'
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] at h2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_add]
    have : x = o • l + M • y + (x - o • l - M • y) := by abel
    rw [this, h2]; abel

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ`. Take `⟨e, he⟩` from `exists_gens_mod_nsmul_of_injective E M hM r Λ Λ.subtype Subtype.val_injective`. Use `⟨fun i => e i, fun i => (e i).2, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨o, y, h⟩` from `he ⟨x, hx⟩`. Use `⟨o, y, y.2, ?_⟩` and prove the remaining obligations.

Establish `h2` using `congrArg Subtype.val h`. Simplify `h2` using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_smul_of_tower]`.
-/
theorem exists_gens_mod_nsmul (E : Type) [Field E] [NumberField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hM : 1 ≤ M) (hΛ : Λ.FG) :
    ∃ e : Fin r → Fin r → E, (∀ i, e i ∈ Λ) ∧
      ∀ x ∈ Λ, ∃ o : Fin r → 𝓞 E, ∃ y ∈ Λ, x = ∑ i, o i • e i + M • y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  obtain ⟨e, he⟩ := exists_gens_mod_nsmul_of_injective E M hM r Λ Λ.subtype Subtype.val_injective
  refine ⟨fun i => e i, fun i => (e i).2, fun x hx => ?_⟩
  obtain ⟨o, y, h⟩ := he ⟨x, hx⟩
  refine ⟨o, y, y.2, ?_⟩
  have h2 := congrArg Subtype.val h
  simpa only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] using h2

end GlobalTheory.GensModNsmul
