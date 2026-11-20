import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp.DetMod

/- English proof (translation)
Establish `hy : ∀ i, y i ∈ Λ` using `fun i => by`. Establish `h1 : y i - x i ∈ Λ` using `Submodule.smul_le_right (hxy i)`. Simplify using `using Λ.add_mem h1 (hx i)`. Establish `hupd : ∀ (z : ι → V), (∀ i, z i ∈ Λ) → ∀ i, ∀ w ∈ 𝔞 • Λ, f (Function.update z i w) ∈ 𝔞 • I`. Introduce `z hz i w hw`.

Use `Submodule.smul_induction_on hw ?_ ?_` and prove the remaining obligations. Introduce `r hr n hn`. Rewrite using `[f.map_update_smul]`. Use `Submodule.smul_mem_smul hr (hI _ fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `using hn`. Simplify `hz j` using `[Function.update_of_ne h]`. Introduce `a b ha hb`. Rewrite using `[f.map_update_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Establish `key : ∀ s : Finset ι, f (s.piecewise y x) - f x ∈ 𝔞 • I`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert i s his ih`. Establish `hz : ∀ j, s.piecewise y x j ∈ Λ` using `fun j => by`. Distinguish the cases in `h : j ∈ s`. Simplify `hy j` using `[h]`. Simplify `hx j` using `[h]`.

Establish `h1` using `hupd _ hz i _ (hxy i)`. Rewrite `h1` using `[f.map_update_sub]`. Establish `h2 : Function.update (s.piecewise y x) i (x i) = s.piecewise y x`. Rewrite using `[Function.update_eq_self_iff]`. Simplify using `[his]`.

Rewrite `h1` using `[h2]`. Rewrite using `[Finset.piecewise_insert]`. Simplify using `using Submodule.add_mem _ h1 ih`. Simplify using `using key Finset.univ`.
-/
theorem multilinear_sub_mem {O V W ι : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    [AddCommGroup W] [Module O W] [Fintype ι] [DecidableEq ι]
    (f : MultilinearMap O (fun _ : ι => V) W) (Λ : Submodule O V) (I : Submodule O W)
    (𝔞 : Ideal O) (hI : ∀ z : ι → V, (∀ i, z i ∈ Λ) → f z ∈ I)
    (x y : ι → V) (hx : ∀ i, x i ∈ Λ) (hxy : ∀ i, y i - x i ∈ 𝔞 • Λ) :
    f y - f x ∈ 𝔞 • I := by
  have hy : ∀ i, y i ∈ Λ := fun i => by
    have h1 : y i - x i ∈ Λ := Submodule.smul_le_right (hxy i)
    simpa using Λ.add_mem h1 (hx i)
  have hupd : ∀ (z : ι → V), (∀ i, z i ∈ Λ) → ∀ i, ∀ w ∈ 𝔞 • Λ,
      f (Function.update z i w) ∈ 𝔞 • I := by
    intro z hz i w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr n hn
      rw [f.map_update_smul]
      refine Submodule.smul_mem_smul hr (hI _ fun j => ?_)
      by_cases h : j = i
      · subst h; simpa using hn
      · simpa [Function.update_of_ne h] using hz j
    · intro a b ha hb
      rw [f.map_update_add]
      exact Submodule.add_mem _ ha hb
  have key : ∀ s : Finset ι, f (s.piecewise y x) - f x ∈ 𝔞 • I := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s his ih =>
      have hz : ∀ j, s.piecewise y x j ∈ Λ := fun j => by
        by_cases h : j ∈ s
        · simpa [h] using hy j
        · simpa [h] using hx j
      have h1 := hupd _ hz i _ (hxy i)
      rw [f.map_update_sub] at h1
      have h2 : Function.update (s.piecewise y x) i (x i) = s.piecewise y x := by
        rw [Function.update_eq_self_iff]; simp [his]
      rw [h2] at h1
      rw [Finset.piecewise_insert]
      simpa using Submodule.add_mem _ h1 ih
  simpa using key Finset.univ

/- English proof (translation)
Set `J : FractionalIdeal (nonZeroDivisors O) K` to `⟨I, hI⟩`. Establish `hJ : J ≠ 0`. Introduce `h0`. Apply `hI0` to reduce the goal to its premises. Establish `: (J : Submodule O K) = ((0 : FractionalIdeal (nonZeroDivisors O) K) : Submodule O K)`.

Rewrite using `[h0]`. Rewrite `this` using `[FractionalIdeal.coe_zero]`. Conclude with `this`. Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors O) δ * J ≤ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J`. Rewrite using `[FractionalIdeal.spanSingleton_mul_le_iff]`.

Introduce `t ht`. Use `Submodule.smul_induction_on (p := fun w => w ∈ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J) (h t ht) ?_ ?_` and prove the remaining obligations. Introduce `r hr n hn`. Rewrite using `[Algebra.smul_def]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hn`.

Introduce `a b ha hb`. Conclude with `Submodule.add_mem (((𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J : FractionalIdeal _ _) : Submodule O K) ha hb`. Establish `hle2` using `mul_le_mul_left hle J⁻¹`. Rewrite `hle2` using `[mul_assoc, mul_assoc, mul_inv_cancel₀ hJ, mul_one, mul_one, FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_coeIdeal]`. Take `⟨a, ha, rfl⟩` from `hle2`.

Conclude with `⟨a, ha, rfl⟩`.
-/
theorem mem_of_smul_le {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (I : Submodule O K) (hI : IsFractional (nonZeroDivisors O) I)
    (hI0 : I ≠ ⊥) (𝔞 : Ideal O) (δ : K) (h : ∀ t ∈ I, δ * t ∈ 𝔞 • I) :
    ∃ a ∈ 𝔞, δ = algebraMap O K a := by
  let J : FractionalIdeal (nonZeroDivisors O) K := ⟨I, hI⟩
  have hJ : J ≠ 0 := by
    intro h0
    apply hI0
    have : (J : Submodule O K) = ((0 : FractionalIdeal (nonZeroDivisors O) K) : Submodule O K) := by
      rw [h0]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors O) δ * J
      ≤ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro t ht
    refine Submodule.smul_induction_on (p := fun w => w ∈ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J) (h t ht) ?_ ?_
    · intro r hr n hn
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hn
    · intro a b ha hb
      exact Submodule.add_mem (((𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J : FractionalIdeal _ _) : Submodule O K) ha hb
  have hle2 := mul_le_mul_left hle J⁻¹
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hJ, mul_one, mul_one,
    FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_coeIdeal] at hle2
  obtain ⟨a, ha, rfl⟩ := hle2
  exact ⟨a, ha, rfl⟩

/- English proof (translation)
Introduce `O K _ _ _ _ _ N Λ 𝔞 γ hfg hsp hγ`. Set `f : MultilinearMap O (fun _ : Fin N => (Fin N → K)) K` to `(Matrix.detRowAlternating (n := Fin N) (R := K)).toMultilinearMap.restrictScalars O`. Establish `hf : ∀ z, f z = (Matrix.of z).det` using `fun z => rfl`. Set `I : Submodule O K` to `Submodule.span O {t | ∃ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) ∧ f z = t}`. Establish `hI : ∀ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) → f z ∈ I` using `fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : nonZeroDivisors O, ∀ x ∈ Λ, ∀ j, IsLocalization.IsInteger O ((d : O) • x j) := by`. Take `⟨S, rfl⟩` from `hfg`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun p : S × Fin N => (p.1 : Fin N → K) p.2)`. Use `⟨d, fun x hx j => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hd (⟨x, hx⟩, j)`. Consider the case `zero => simpa using IsLocalization.isInteger_zero`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Pi.add_apply, smul_add]`. Conclude with `IsLocalization.isInteger_add hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[Pi.smul_apply, smul_comm]`. Conclude with `IsLocalization.isInteger_smul hx`. Establish `hfrac : IsFractional (nonZeroDivisors O) I`. Rewrite using `[FractionalIdeal.isFractional_span_iff]`.

Use `⟨(d : O) ^ N, pow_mem d.2 N, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `choose m hm using fun i j => hd _ (hz i) j`. Use `⟨(Matrix.of m).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, hf, Algebra.smul_def, map_pow]`.

Establish `: (algebraMap O K).mapMatrix (Matrix.of m) = algebraMap O K d • Matrix.of z`. Use extensionality with `i j`. Simplify using `[hm, Algebra.smul_def]`. Rewrite using `[this, Matrix.det_smul]`. Simplify using the standard rewrite rules.

Establish `hI0 : I ≠ ⊥`. Introduce `h0`. Take `⟨s, hs, hsp', hli⟩` from `exists_linearIndependent K (Λ : Set (Fin N → K))`. Rewrite `hsp'` using `[hsp]`. Set `b : Module.Basis s K (Fin N → K)` to `Module.Basis.mk hli (by simp [hsp'])`.

Set `e : s ≃ Fin N` to `b.indexEquiv (Pi.basisFun K (Fin N))`. Set `b'` to `b.reindex e`. Establish `hb' : ∀ i, b' i ∈ Λ` using `fun i => by`. Simplify using `only [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]`. Conclude with `hs (e.symm i).2`.

Establish `h1` using `hI b' hb'`. Rewrite `h1` using `[h0, Submodule.mem_bot, hf]`. Establish `h2 : IsUnit (Matrix.of (b' : Fin N → Fin N → K))` using `Matrix.linearIndependent_rows_iff_isUnit.mp b'.linearIndependent`. Rewrite `h2` using `[Matrix.isUnit_iff_isUnit_det, h1]`. Conclude with `not_isUnit_zero h2`.

Take `⟨a, ha, hδ⟩` from `mem_of_smul_le I hfrac hI0 𝔞 (γ.det - 1) (by`. Introduce `t ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`.

Establish `h1` using `multilinear_sub_mem f Λ I 𝔞 hI z (fun i => γ *ᵥ z i) hz (fun i => hγ _ (hz i))`. Establish `h2 : Matrix.of (fun i => γ *ᵥ z i) = Matrix.of z * γᵀ`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`. Rewrite `h1` using `[hf, h2, Matrix.det_mul, Matrix.det_transpose, ← hf]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx)`. Conclude with `⟨a, ha, by rw [← hδ]; ring⟩`.
-/
theorem main : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (N : ℕ) (Λ : Submodule O (Fin N → K)) (𝔞 : Ideal O) (γ : Matrix (Fin N) (Fin N) K), Λ.FG → Submodule.span K (Λ : Set (Fin N → K)) = ⊤ → (∀ x ∈ Λ, γ *ᵥ x - x ∈ 𝔞 • Λ) → ∃ a ∈ 𝔞, γ.det = 1 + algebraMap O K a := by
  intro O K _ _ _ _ _ N Λ 𝔞 γ hfg hsp hγ
  let f : MultilinearMap O (fun _ : Fin N => (Fin N → K)) K :=
    (Matrix.detRowAlternating (n := Fin N) (R := K)).toMultilinearMap.restrictScalars O
  have hf : ∀ z, f z = (Matrix.of z).det := fun z => rfl
  let I : Submodule O K := Submodule.span O {t | ∃ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) ∧ f z = t}
  have hI : ∀ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) → f z ∈ I :=
    fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩

  obtain ⟨d, hd⟩ : ∃ d : nonZeroDivisors O, ∀ x ∈ Λ, ∀ j,
      IsLocalization.IsInteger O ((d : O) • x j) := by
    obtain ⟨S, rfl⟩ := hfg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun p : S × Fin N => (p.1 : Fin N → K) p.2)
    refine ⟨d, fun x hx j => ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact hd (⟨x, hx⟩, j)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x y _ _ hx hy =>
      rw [Pi.add_apply, smul_add]; exact IsLocalization.isInteger_add hx hy
    | smul a x _ hx =>
      rw [Pi.smul_apply, smul_comm]; exact IsLocalization.isInteger_smul hx
  have hfrac : IsFractional (nonZeroDivisors O) I := by
    rw [FractionalIdeal.isFractional_span_iff]
    refine ⟨(d : O) ^ N, pow_mem d.2 N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    choose m hm using fun i j => hd _ (hz i) j
    refine ⟨(Matrix.of m).det, ?_⟩
    rw [RingHom.map_det, hf, Algebra.smul_def, map_pow]
    have : (algebraMap O K).mapMatrix (Matrix.of m) = algebraMap O K d • Matrix.of z := by
      ext i j
      simp [hm, Algebra.smul_def]
    rw [this, Matrix.det_smul]
    simp
  have hI0 : I ≠ ⊥ := by
    intro h0
    obtain ⟨s, hs, hsp', hli⟩ := exists_linearIndependent K (Λ : Set (Fin N → K))
    rw [hsp] at hsp'
    let b : Module.Basis s K (Fin N → K) := Module.Basis.mk hli (by simp [hsp'])
    let e : s ≃ Fin N := b.indexEquiv (Pi.basisFun K (Fin N))
    let b' := b.reindex e
    have hb' : ∀ i, b' i ∈ Λ := fun i => by
      simp only [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact hs (e.symm i).2
    have h1 := hI b' hb'
    rw [h0, Submodule.mem_bot, hf] at h1
    have h2 : IsUnit (Matrix.of (b' : Fin N → Fin N → K)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp b'.linearIndependent
    rw [Matrix.isUnit_iff_isUnit_det, h1] at h2
    exact not_isUnit_zero h2
  obtain ⟨a, ha, hδ⟩ := mem_of_smul_le I hfrac hI0 𝔞 (γ.det - 1) (by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h1 := multilinear_sub_mem f Λ I 𝔞 hI z (fun i => γ *ᵥ z i) hz (fun i => hγ _ (hz i))
      have h2 : Matrix.of (fun i => γ *ᵥ z i) = Matrix.of z * γᵀ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      rw [hf, h2, Matrix.det_mul, Matrix.det_transpose, ← hf] at h1
      convert h1 using 1
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx)
  exact ⟨a, ha, by rw [← hδ]; ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.DetMod
