import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Introduce `A M _ _ _ _ _ a`. Take `⟨S, hS⟩` from `(Module.Finite.fg_top : (⊤ : Submodule A M).FG)`. Set `K` to `FractionRing A`. Set `ψ : Module.Dual A M → Option S → K` to `fun l o => o.elim (algebraMap A K (a l)) (fun i => algebraMap A K (l (i : M)))`. Establish `hψs : ∀ (p : A) l o, ψ (p • l) o = algebraMap A K p * ψ l o`.

Introduce `p l o`. Apply the tactic sequence `cases o <;> simp [ψ]`. Establish `hψa : ∀ l m o, ψ (l + m) o = ψ l o + ψ m o`. Introduce `l m o`. Apply the tactic sequence `cases o <;> simp [ψ]`.

Establish `hψ0 : ∀ o, ψ 0 o = 0`. Introduce `o`. Apply the tactic sequence `cases o <;> simp [ψ]`. Set `v : Option S → K` to `fun j => if none = j then 1 else 0`. Establish `key : ∀ w ∈ Submodule.span K (Set.range ψ), ∃ s : A, s ≠ 0 ∧ ∃ l, ∀ o, algebraMap A K s * w o = ψ l o`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, rfl⟩` from `hx`. Conclude with `⟨1, one_ne_zero, l, fun o => by simp⟩`.

Consider the case `zero`. Conclude with `⟨1, one_ne_zero, 0, fun o => by simp [hψ0]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, l, hl⟩` from `hx`. Take `⟨t, ht, m, hm⟩` from `hy`.

Use `⟨s * t, mul_ne_zero hs ht, t • l + s • m, fun o => ?_⟩` and prove the remaining obligations. Rewrite using `[hψa, hψs, hψs, ← hl o, ← hm o, Pi.add_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c x _ hx`. Take `⟨s, hs, l, hl⟩` from `hx`.

Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := A) c`. Establish `hq0 : algebraMap A K q ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq`. Establish `hc : algebraMap A K q * (algebraMap A K p / algebraMap A K q) = algebraMap A K p` using `mul_div_cancel₀ _ hq0`. Use `⟨q * s, mul_ne_zero (nonZeroDivisors.ne_zero hq) hs, p • l, fun o => ?_⟩` and prove the remaining obligations. Rewrite using `[hψs, ← hl o, Pi.smul_apply, smul_eq_mul, map_mul]`.

Take the linear combination `(algebraMap A K s * x o) * hc`. Establish `hv : v ∉ Submodule.span K (Set.range ψ)`. Introduce `hmem`. Take `⟨s, hs, l, hl⟩` from `key v hmem`. Establish `hl0 : l = 0`.

Apply `LinearMap.ext_on hS` to reduce the goal to its premises. Introduce `i hi`. Establish `h` using `hl (some ⟨i, hi⟩)`. Simplify using `[v, ψ] at h`. Rewrite using `[LinearMap.zero_apply]`.

Conclude with `IsFractionRing.injective A K (by rw [map_zero]; exact h.symm)`. Substitute `hl0` using the available equality. Establish `h` using `hl none`. Simplify using `[v, ψ] at h`. Conclude with `hs h`.

Take `⟨f, hf, hfW⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance`. Establish `hf0 : ∀ l, f (ψ l) = 0`. Introduce `l`. Establish `h : f (ψ l) ∈ (Submodule.span K (Set.range ψ)).map f` using `Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)`. Rewrite `h` using `[hfW]`.

Conclude with `(Submodule.mem_bot K).mp h`. Set `c : Option S → K` to `fun o => f (fun j => if o = j then 1 else 0)`. Take `⟨Dn, hDc⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c`. Use `choose b hb using hDc`. Establish `hD0 : algebraMap A K (Dn : A) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Dn.2`.

Establish `hmain : ∀ l : Module.Dual A M, b none * a l + ∑ i : S, b (some i) * l i = 0`. Introduce `l`. Establish `e : ∑ o, ψ l o * c o = 0`. Establish `h` using `hf0 l`. Rewrite `h` using `[LinearMap.pi_apply_eq_sum_univ f (ψ l)]`.

Simplify `h` using `[c, smul_eq_mul]`. Apply `IsFractionRing.injective A K` to reduce the goal to its premises. Rewrite using `[map_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fintype.sum_option, mul_add, Finset.mul_sum, map_add, map_mul, map_sum]`.

Use `congr 1`. Rewrite using `[hb, Algebra.smul_def]`. Simplify using `only [ψ, Option.elim_none]`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, hb, Algebra.smul_def]`. Simplify using `only [ψ, Option.elim_some]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [e, mul_zero]`. Use `⟨b none, -(∑ i : S, b (some i) • (i : M)), ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Establish `h` using `hb none`. Rewrite `h` using `[h0, map_zero, Algebra.smul_def]`. Conclude with `hf ((mul_eq_zero.mp h.symm).resolve_left hD0)`. Introduce `l`.

Establish `h` using `hmain l`. Rewrite using `[map_neg, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Take the linear combination `-h`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.bidual :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a : Module.Dual A (Module.Dual A M)), ∃ (d : A) (r : M), d ≠ 0 ∧ ∀ l : Module.Dual A M, l r = d * a l := by
  intro A M _ _ _ _ _ a
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  let K := FractionRing A
  let ψ : Module.Dual A M → Option S → K := fun l o =>
    o.elim (algebraMap A K (a l)) (fun i => algebraMap A K (l (i : M)))
  have hψs : ∀ (p : A) l o, ψ (p • l) o = algebraMap A K p * ψ l o := by
    intro p l o
    cases o <;> simp [ψ]
  have hψa : ∀ l m o, ψ (l + m) o = ψ l o + ψ m o := by
    intro l m o
    cases o <;> simp [ψ]
  have hψ0 : ∀ o, ψ 0 o = 0 := by
    intro o
    cases o <;> simp [ψ]
  let v : Option S → K := fun j => if none = j then 1 else 0
  have key : ∀ w ∈ Submodule.span K (Set.range ψ),
      ∃ s : A, s ≠ 0 ∧ ∃ l, ∀ o, algebraMap A K s * w o = ψ l o := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨1, one_ne_zero, l, fun o => by simp⟩
    | zero =>
      exact ⟨1, one_ne_zero, 0, fun o => by simp [hψ0]⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨t, ht, m, hm⟩ := hy
      refine ⟨s * t, mul_ne_zero hs ht, t • l + s • m, fun o => ?_⟩
      rw [hψa, hψs, hψs, ← hl o, ← hm o, Pi.add_apply, map_mul]
      ring
    | smul c x _ hx =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have hq0 : algebraMap A K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
      have hc : algebraMap A K q * (algebraMap A K p / algebraMap A K q) = algebraMap A K p :=
        mul_div_cancel₀ _ hq0
      refine ⟨q * s, mul_ne_zero (nonZeroDivisors.ne_zero hq) hs, p • l, fun o => ?_⟩
      rw [hψs, ← hl o, Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (algebraMap A K s * x o) * hc
  have hv : v ∉ Submodule.span K (Set.range ψ) := by
    intro hmem
    obtain ⟨s, hs, l, hl⟩ := key v hmem
    have hl0 : l = 0 := by
      apply LinearMap.ext_on hS
      intro i hi
      have h := hl (some ⟨i, hi⟩)
      simp [v, ψ] at h
      rw [LinearMap.zero_apply]
      exact IsFractionRing.injective A K (by rw [map_zero]; exact h.symm)
    subst hl0
    have h := hl none
    simp [v, ψ] at h
    exact hs h
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hf0 : ∀ l, f (ψ l) = 0 := by
    intro l
    have h : f (ψ l) ∈ (Submodule.span K (Set.range ψ)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    rw [hfW] at h
    exact (Submodule.mem_bot K).mp h
  let c : Option S → K := fun o => f (fun j => if o = j then 1 else 0)
  obtain ⟨Dn, hDc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  choose b hb using hDc
  have hD0 : algebraMap A K (Dn : A) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Dn.2
  have hmain : ∀ l : Module.Dual A M, b none * a l + ∑ i : S, b (some i) * l i = 0 := by
    intro l
    have e : ∑ o, ψ l o * c o = 0 := by
      have h := hf0 l
      rw [LinearMap.pi_apply_eq_sum_univ f (ψ l)] at h
      simpa [c, smul_eq_mul] using h
    apply IsFractionRing.injective A K
    rw [map_zero]
    calc algebraMap A K (b none * a l + ∑ i : S, b (some i) * l i)
        = algebraMap A K (Dn : A) * ∑ o, ψ l o * c o := by
          rw [Fintype.sum_option, mul_add, Finset.mul_sum, map_add, map_mul, map_sum]
          congr 1
          · rw [hb, Algebra.smul_def]
            simp only [ψ, Option.elim_none]
            ring
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_mul, hb, Algebra.smul_def]
            simp only [ψ, Option.elim_some]
            ring
      _ = 0 := by rw [e, mul_zero]
  refine ⟨b none, -(∑ i : S, b (some i) • (i : M)), ?_, ?_⟩
  · intro h0
    have h := hb none
    rw [h0, map_zero, Algebra.smul_def] at h
    exact hf ((mul_eq_zero.mp h.symm).resolve_left hD0)
  · intro l
    have h := hmain l
    rw [map_neg, map_sum]
    simp only [map_smul, smul_eq_mul]
    linear_combination -h
