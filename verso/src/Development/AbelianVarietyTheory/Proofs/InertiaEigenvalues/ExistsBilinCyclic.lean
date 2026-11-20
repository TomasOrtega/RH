import Mathlib

open Polynomial

namespace GlobalTheory.SimilarTranspose

open Polynomial in

/- English proof (translation)
Use `set g := f * C f.leadingCoeff⁻¹ with hg`. Establish `hgm : g.Monic` using `monic_mul_leadingCoeff_inv hf`. Establish `hdvd : ∀ a, f ∣ a ↔ g ∣ a` using `fun a => (associated_mul_unit_right f _ (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hf))))).dvd_iff_dvd_left`. Set `l : k[X] →ₗ[k] k` to `(lcoeff k (g.natDegree - 1)).comp (modByMonicHom g)`. Use `⟨l, fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Simplify using `[l, (modByMonic_eq_zero_iff_dvd hgm).2 ((hdvd a).1 ha)]`. Rewrite using `[hdvd, ← modByMonic_eq_zero_iff_dvd hgm]`. Assume the negation of the conclusion as `hr`. Establish `hg1 : g ≠ 1`. Introduce and unpack `h`.

Apply `hr` to reduce the goal to its premises. Rewrite using `[h, modByMonic_one]`. Establish `hlt` using `natDegree_modByMonic_lt a hgm hg1`. Use `set r := a %ₘ g with hrdef`. Use `set m := g.natDegree - 1 - r.natDegree with hm`.

Establish `hsub : (a * X ^ m) %ₘ g = (r * X ^ m) %ₘ g`. Apply `modByMonic_eq_of_dvd_sub hgm` to reduce the goal to its premises. Use `⟨(a /ₘ g) * X ^ m, ?_⟩` and prove the remaining obligations. Use `modByMonic_add_div a g` as an intermediate fact. Rewrite using `[hrdef]`.

Take the linear combination `-(X ^ m) * this`. Establish `hdeg : (r * X ^ m).natDegree = g.natDegree - 1`. Rewrite using `[natDegree_mul_X_pow m hr]`. Use linear arithmetic over natural numbers and integers. Establish `hself : (r * X ^ m) %ₘ g = r * X ^ m`.

Rewrite using `[modByMonic_eq_self_iff hgm]`. Apply `degree_lt_degree` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Establish `h` using `ha (X ^ m)`. Simplify using `only [l, LinearMap.comp_apply, modByMonicHom_apply, lcoeff_apply] at h`.

Rewrite `h` using `[hsub, hself]`. Establish `hidx : g.natDegree - 1 = r.natDegree + m` using `by omega`. Rewrite `h` using `[hidx, coeff_mul_X_pow]`. Conclude with `hr (leadingCoeff_eq_zero.1 h)`.
-/
theorem _root_.GlobalTheory.SimilarTranspose.exists_form {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ l : k[X] →ₗ[k] k, (∀ a, f ∣ a → l a = 0) ∧ ∀ a, (∀ b, l (a * b) = 0) → f ∣ a := by
  set g := f * C f.leadingCoeff⁻¹ with hg
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hf
  have hdvd : ∀ a, f ∣ a ↔ g ∣ a := fun a =>
    (associated_mul_unit_right f _
      (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hf))))).dvd_iff_dvd_left
  let l : k[X] →ₗ[k] k := (lcoeff k (g.natDegree - 1)).comp (modByMonicHom g)
  refine ⟨l, fun a ha => ?_, fun a ha => ?_⟩
  · simp [l, (modByMonic_eq_zero_iff_dvd hgm).2 ((hdvd a).1 ha)]
  · rw [hdvd, ← modByMonic_eq_zero_iff_dvd hgm]
    by_contra hr
    have hg1 : g ≠ 1 := by
      rintro h
      apply hr
      rw [h, modByMonic_one]
    have hlt := natDegree_modByMonic_lt a hgm hg1
    set r := a %ₘ g with hrdef
    set m := g.natDegree - 1 - r.natDegree with hm
    have hsub : (a * X ^ m) %ₘ g = (r * X ^ m) %ₘ g := by
      apply modByMonic_eq_of_dvd_sub hgm
      refine ⟨(a /ₘ g) * X ^ m, ?_⟩
      have := modByMonic_add_div a g
      rw [hrdef]
      linear_combination -(X ^ m) * this
    have hdeg : (r * X ^ m).natDegree = g.natDegree - 1 := by
      rw [natDegree_mul_X_pow m hr]
      omega
    have hself : (r * X ^ m) %ₘ g = r * X ^ m := by
      rw [modByMonic_eq_self_iff hgm]
      apply degree_lt_degree
      omega
    have h := ha (X ^ m)
    simp only [l, LinearMap.comp_apply, modByMonicHom_apply, lcoeff_apply] at h
    rw [hsub, hself] at h
    have hidx : g.natDegree - 1 = r.natDegree + m := by omega
    rw [hidx, coeff_mul_X_pow] at h
    exact hr (leadingCoeff_eq_zero.1 h)

/- English proof (translation)
Take `⟨l, h1, h2⟩` from `exists_form f hf`. Set `l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k` to `(((Ideal.span {f}).restrictScalars k).liftQ l (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap`. Establish `hl : ∀ a, l' (Ideal.Quotient.mk _ a) = l a` using `fun a => rfl`. Use `⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y`. Express the relevant statement in the definitionally equal form `l ((X * a) * b) = l (a * (X * b))`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Introduce `y hy`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y`. Use `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))` and prove the remaining obligations. Use `hy (Ideal.Quotient.mk (Ideal.span {f}) a)` as an intermediate fact. Rewrite using `[mul_comm]`.

Conclude with `this`.
-/
theorem exists_bilin_cyclic {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ ∀ y, (∀ x, B x y = 0) → y = 0 := by
  obtain ⟨l, h1, h2⟩ := exists_form f hf
  let l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k :=
    (((Ideal.span {f}).restrictScalars k).liftQ l (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp
      (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap
  have hl : ∀ a, l' (Ideal.Quotient.mk _ a) = l a := fun a => rfl
  refine ⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l ((X * a) * b) = l (a * (X * b))
    congr 1; ring
  · intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))
    have := hy (Ideal.Quotient.mk (Ideal.span {f}) a)
    rw [mul_comm]
    exact this

/- English proof (translation)
Establish `htor : Module.IsTorsion k[X] (Module.AEval' T)` using `Module.AEval.isTorsion_of_finiteDimensional k W T`. Take `⟨ι, _, p, hp, n, ⟨e⟩⟩` from `Module.equiv_directSum_of_isTorsion htor`. Use `choose B hB1 hB2 using fun i => exists_bilin_cyclic (p i ^ n i) (pow_ne_zero _ (hp i).ne_zero)`. Set `π : ∀ i, W →ₗ[k] (k[X] ⧸ Submodule.span k[X] {p i ^ n i})` to `fun i => (((DirectSum.component k[X] ι _ i).comp e.toLinearMap).restrictScalars k).comp (Module.AEval'.of T).toLinearMap`. Establish `hπ : ∀ i x, π i x = e (Module.AEval'.of T x) i` using `fun i x => rfl`.

Establish `hT : ∀ i x, π i (T x) = (X : k[X]) • π i x`. Introduce `i x`. Rewrite using `[hπ, hπ, ← Module.AEval'.X_smul_of, map_smul]`. Both sides reduce to the same expression. Use `⟨∑ i, (B i).compl₁₂ (π i) (π i), ?_, ?_⟩` and prove the remaining obligations.

Introduce `x y`. Simplify using `only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, hT, hB1]`. Introduce `y hy`. Establish `h0 : e (Module.AEval'.of T y) = 0`. Use extensionality with `i`.

Rewrite using `[← hπ, DirectSum.zero_apply]`. Use `hB2 i _ fun z => ?_` and prove the remaining obligations. Use `hy ((Module.AEval'.of T).symm (e.symm (DirectSum.lof k[X] ι _ i z)))` as an intermediate fact. Simplify using `only [LinearMap.sum_apply, LinearMap.compl₁₂_apply] at this`. Rewrite `this` using `[Finset.sum_eq_single i]`.

Rewrite `this` using `[hπ i ((Module.AEval'.of T).symm _)]`. Simplify using `using this`. Introduce `j _ hj`. Rewrite using `[hπ j ((Module.AEval'.of T).symm _)]`. Simplify using `[DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]`.

Simplify using the standard rewrite rules. Simplify using `using h0`.
-/
theorem exists_bilin {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : W →ₗ[k] W) :
    ∃ B : W →ₗ[k] W →ₗ[k] k, (∀ x y, B (T x) y = B x (T y)) ∧ ∀ y, (∀ x, B x y = 0) → y = 0 := by
  classical
  have htor : Module.IsTorsion k[X] (Module.AEval' T) :=
    Module.AEval.isTorsion_of_finiteDimensional k W T
  obtain ⟨ι, _, p, hp, n, ⟨e⟩⟩ := Module.equiv_directSum_of_isTorsion htor
  choose B hB1 hB2 using fun i => exists_bilin_cyclic (p i ^ n i) (pow_ne_zero _ (hp i).ne_zero)
  let π : ∀ i, W →ₗ[k] (k[X] ⧸ Submodule.span k[X] {p i ^ n i}) := fun i =>
    (((DirectSum.component k[X] ι _ i).comp e.toLinearMap).restrictScalars k).comp
      (Module.AEval'.of T).toLinearMap
  have hπ : ∀ i x, π i x = e (Module.AEval'.of T x) i := fun i x => rfl
  have hT : ∀ i x, π i (T x) = (X : k[X]) • π i x := by
    intro i x
    rw [hπ, hπ, ← Module.AEval'.X_smul_of, map_smul]
    rfl
  refine ⟨∑ i, (B i).compl₁₂ (π i) (π i), ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, hT, hB1]
  · intro y hy
    have h0 : e (Module.AEval'.of T y) = 0 := by
      ext i
      rw [← hπ, DirectSum.zero_apply]
      refine hB2 i _ fun z => ?_
      have := hy ((Module.AEval'.of T).symm (e.symm (DirectSum.lof k[X] ι _ i z)))
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply] at this
      rw [Finset.sum_eq_single i] at this
      · rw [hπ i ((Module.AEval'.of T).symm _)] at this
        simpa using this
      · intro j _ hj
        rw [hπ j ((Module.AEval'.of T).symm _)]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      · simp
    simpa using h0

open Polynomial in
/- English proof (translation)
Take `⟨l, h1, h2⟩` from `_root_.GlobalTheory.SimilarTranspose.exists_form f hf`. Establish `hsurj` using `Submodule.Quotient.mk_surjective (k[X] ∙ f)`. Set `rep` to `Function.surjInv hsurj`. Establish `hrep : ∀ x, Submodule.Quotient.mk (p` using `k[X] ∙ f) (rep x) = x := Function.surjInv_eq hsurj`. Establish `hdiff : ∀ a a' : k[X], Submodule.Quotient.mk (p` using `k[X] ∙ f) a = Submodule.Quotient.mk (p := k[X] ∙ f) a' → f ∣ a - a' := by`.

Introduce `a a' h`. Rewrite `h` using `[Submodule.Quotient.eq, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `h`. Conclude with `⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩`. Set `g : (k[X] ⧸ (k[X] ∙ f)) → (k[X] ⧸ (k[X] ∙ f)) → k` to `fun x y => l (rep x * rep y)`.

Establish `hg : ∀ a b, g (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = l (a * b)`. Introduce `a b`. Establish `ha` using `hdiff _ _ (hrep (Submodule.Quotient.mk a))`. Establish `hb` using `hdiff _ _ (hrep (Submodule.Quotient.mk b))`. Establish `: rep (Submodule.Quotient.mk a) * rep (Submodule.Quotient.mk b) - a * b = (rep (Submodule.Quotient.mk a) - a) * rep (Submodule.Quotient.mk b) + a * (rep (Submodule.Quotient.mk b) - b)` using `by ring`.

Establish `h0` using `h1 _ (this ▸ dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _))`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Conclude with `h0`. Use `⟨LinearMap.mk₂ k g ?_ ?_ ?_ ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y z`.

Take `⟨a, rfl⟩` from `hsurj x`. Take `⟨b, rfl⟩` from `hsurj y`. Take `⟨c, rfl⟩` from `hsurj z`. Rewrite using `[← Submodule.Quotient.mk_add, hg, hg, hg, add_mul, map_add]`. Introduce `c x y`.

Take `⟨a, rfl⟩` from `hsurj x`. Take `⟨b, rfl⟩` from `hsurj y`. Rewrite using `[← Submodule.Quotient.mk_smul, hg, hg, smul_mul_assoc, map_smul]`. Introduce `x y z`. Take `⟨a, rfl⟩` from `hsurj x`.

Take `⟨b, rfl⟩` from `hsurj y`. Take `⟨c, rfl⟩` from `hsurj z`. Rewrite using `[← Submodule.Quotient.mk_add, hg, hg, hg, mul_add, map_add]`. Introduce `c x y`. Take `⟨a, rfl⟩` from `hsurj x`.

Take `⟨b, rfl⟩` from `hsurj y`. Rewrite using `[← Submodule.Quotient.mk_smul, hg, hg, mul_smul_comm, map_smul]`. Introduce `x y`. Take `⟨a, rfl⟩` from `hsurj x`. Take `⟨b, rfl⟩` from `hsurj y`.

Simplify using `only [LinearMap.mk₂_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hg, hg, smul_eq_mul, smul_eq_mul, mul_assoc, mul_left_comm]`. Introduce `x hx`. Take `⟨a, rfl⟩` from `hsurj x`. Take `⟨c, hc⟩` from `h2 a fun b => by`.

Use `hx (Submodule.Quotient.mk b)` as an intermediate fact. Rewrite `this` using `[LinearMap.mk₂_apply, hg]`. Conclude with `this`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`. Conclude with `⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩`.
-/
private theorem exists_nondegenerate_X_symmetric_form_quotient {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ G : (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] k,
      (∀ x y, G ((X : k[X]) • x) y = G x ((X : k[X]) • y)) ∧ ∀ x, (∀ y, G x y = 0) → x = 0 := by
  obtain ⟨l, h1, h2⟩ := _root_.GlobalTheory.SimilarTranspose.exists_form f hf
  have hsurj := Submodule.Quotient.mk_surjective (k[X] ∙ f)
  let rep := Function.surjInv hsurj
  have hrep : ∀ x, Submodule.Quotient.mk (p := k[X] ∙ f) (rep x) = x := Function.surjInv_eq hsurj
  have hdiff : ∀ a a' : k[X], Submodule.Quotient.mk (p := k[X] ∙ f) a =
      Submodule.Quotient.mk (p := k[X] ∙ f) a' → f ∣ a - a' := by
    intro a a' h
    rw [Submodule.Quotient.eq, Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
  let g : (k[X] ⧸ (k[X] ∙ f)) → (k[X] ⧸ (k[X] ∙ f)) → k := fun x y => l (rep x * rep y)
  have hg : ∀ a b, g (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = l (a * b) := by
    intro a b
    have ha := hdiff _ _ (hrep (Submodule.Quotient.mk a))
    have hb := hdiff _ _ (hrep (Submodule.Quotient.mk b))
    have : rep (Submodule.Quotient.mk a) * rep (Submodule.Quotient.mk b) - a * b =
        (rep (Submodule.Quotient.mk a) - a) * rep (Submodule.Quotient.mk b) +
          a * (rep (Submodule.Quotient.mk b) - b) := by ring
    have h0 := h1 _ (this ▸ dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _))
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  refine ⟨LinearMap.mk₂ k g ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, add_mul, map_add]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, smul_mul_assoc, map_smul]
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, mul_add, map_add]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, mul_smul_comm, map_smul]
  · intro x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    simp only [LinearMap.mk₂_apply]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hg, hg, smul_eq_mul,
      smul_eq_mul, mul_assoc, mul_left_comm]
  · intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨c, hc⟩ := h2 a fun b => by
      have := hx (Submodule.Quotient.mk b)
      rw [LinearMap.mk₂_apply, hg] at this
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩

open Polynomial in
/- English proof (translation)
Take `⟨ι, _, p, hp, e, ⟨φ⟩⟩` from `Module.equiv_directSum_of_isTorsion hM`. Establish `hne : ∀ i, p i ^ e i ≠ 0` using `fun i => pow_ne_zero _ (hp i).ne_zero`. Use `choose G hGX hGn using fun i => exists_nondegenerate_X_symmetric_form_quotient (p i ^ e i) (hne i)`. Set `ψ : M →ₗ[k] (DirectSum ι fun i => k[X] ⧸ k[X] ∙ p i ^ e i)` to `φ.toLinearMap.restrictScalars k`. Establish `hψ : ∀ m, ψ m = φ m` using `fun m => rfl`.

Establish `happ : ∀ m n, (∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ) ((DirectSum.component k ι _ i).comp ψ)) m n = ∑ i, G i (φ m i) (φ n i)`. Introduce `m n`. Simplify using `only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply, hψ]`. Both sides reduce to the same expression. Use `⟨∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ) ((DirectSum.component k ι _ i).comp ψ), ?_, ?_⟩` and prove the remaining obligations.

Introduce `m n`. Rewrite using `[happ, happ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, DirectSum.smul_apply, DirectSum.smul_apply, hGX]`. Introduce `m hm`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `DFinsupp.ext fun i => ?_` and prove the remaining obligations. Apply `hGn i` to reduce the goal to its premises. Introduce `y`.

Establish `h` using `hm (φ.symm (DirectSum.of _ i y))`. Rewrite `h` using `[happ, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i]`. Simplify using `using h`. Introduce `j _ hji`. Rewrite using `[DirectSum.of_eq_of_ne _ _ _ hji, map_zero]`.

Simplify using the standard rewrite rules.
-/
private theorem exists_nondegenerate_X_symmetric_form_torsion {k : Type} [Field k] {M : Type} [AddCommGroup M]
    [Module k[X] M] [Module k M] [IsScalarTower k k[X] M] [Module.Finite k[X] M]
    (hM : Module.IsTorsion k[X] M) :
    ∃ B : M →ₗ[k] M →ₗ[k] k, (∀ m n, B ((X : k[X]) • m) n = B m ((X : k[X]) • n)) ∧
      ∀ m, (∀ n, B m n = 0) → m = 0 := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_directSum_of_isTorsion hM
  have hne : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
  choose G hGX hGn using fun i => exists_nondegenerate_X_symmetric_form_quotient (p i ^ e i) (hne i)
  let ψ : M →ₗ[k] (DirectSum ι fun i => k[X] ⧸ k[X] ∙ p i ^ e i) :=
    φ.toLinearMap.restrictScalars k
  have hψ : ∀ m, ψ m = φ m := fun m => rfl
  have happ : ∀ m n, (∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ)) m n = ∑ i, G i (φ m i) (φ n i) := by
    intro m n
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply, hψ]
    rfl
  refine ⟨∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ), ?_, ?_⟩
  · intro m n
    rw [happ, happ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, DirectSum.smul_apply, DirectSum.smul_apply, hGX]
  · intro m hm
    apply φ.injective
    rw [map_zero]
    refine DFinsupp.ext fun i => ?_
    apply hGn i
    intro y
    have h := hm (φ.symm (DirectSum.of _ i y))
    rw [happ, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      rw [DirectSum.of_eq_of_ne _ _ _ hji, map_zero]
    · simp

open Polynomial in

/- English proof (translation)
Introduce `k ι _ _ _ A`. Establish `hT` using `Module.AEval.isTorsion_of_finiteDimensional k (ι → k) (Matrix.toLin' A)`. Take `⟨B, hBX, hBn⟩` from `exists_nondegenerate_X_symmetric_form_torsion (M := Module.AEval' (Matrix.toLin' A)) hT`. Set `o` to `Module.AEval'.of (Matrix.toLin' A)`. Set `Q : (ι → k) →ₗ[k] (ι → k) →ₗ[k] k` to `B.compl₁₂ o.toLinearMap o.toLinearMap`.

Establish `hQ : Q.compl₁₂ (Matrix.toLin' A) LinearMap.id = Q.compl₁₂ LinearMap.id (Matrix.toLin' A)`. Use `LinearMap.ext₂ fun v w => ?_` and prove the remaining obligations. Simplify using `only [Q, LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearEquiv.coe_coe, o]`. Rewrite using `[← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, hBX]`. Establish `hQP : ∀ v w, Q v w = Matrix.vecMul v (LinearMap.toMatrix₂' k Q) ⬝ᵥ w`.

Introduce `v w`. Rewrite using `[← Matrix.dotProduct_mulVec, ← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']`. Use `⟨LinearMap.toMatrix₂' k Q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.vecMul_injective_iff_isUnit]`. Introduce `v w hvw`.

Establish `h0 : ∀ u, Q (v - w) u = 0`. Introduce `u`. Rewrite using `[hQP, Matrix.sub_vecMul]`. Simplify using `only at hvw`. Rewrite using `[hvw, sub_self, zero_dotProduct]`.

Use `hBn (o (v - w)) fun n => by` as an intermediate fact. Use `h0 (o.symm n)` as an intermediate fact. Simplify `this` using `[Q]`. Rewrite `this` using `[map_eq_zero_iff _ o.injective, sub_eq_zero]`. Conclude with `this`.

Use `congrArg (LinearMap.toMatrix₂' k) hQ` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix₂'_compl₁₂]`. Simplify `this.symm` using `[LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin']`.
-/
theorem _root_.GlobalTheory.SimilarTranspose.main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  have hT := Module.AEval.isTorsion_of_finiteDimensional k (ι → k) (Matrix.toLin' A)
  obtain ⟨B, hBX, hBn⟩ := exists_nondegenerate_X_symmetric_form_torsion (M := Module.AEval' (Matrix.toLin' A)) hT
  let o := Module.AEval'.of (Matrix.toLin' A)
  let Q : (ι → k) →ₗ[k] (ι → k) →ₗ[k] k := B.compl₁₂ o.toLinearMap o.toLinearMap
  have hQ : Q.compl₁₂ (Matrix.toLin' A) LinearMap.id = Q.compl₁₂ LinearMap.id (Matrix.toLin' A) := by
    refine LinearMap.ext₂ fun v w => ?_
    simp only [Q, LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearEquiv.coe_coe, o]
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, hBX]
  have hQP : ∀ v w, Q v w = Matrix.vecMul v (LinearMap.toMatrix₂' k Q) ⬝ᵥ w := by
    intro v w
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']
  refine ⟨LinearMap.toMatrix₂' k Q, ?_, ?_⟩
  · rw [← Matrix.vecMul_injective_iff_isUnit]
    intro v w hvw
    have h0 : ∀ u, Q (v - w) u = 0 := by
      intro u
      rw [hQP, Matrix.sub_vecMul]
      simp only at hvw
      rw [hvw, sub_self, zero_dotProduct]
    have := hBn (o (v - w)) fun n => by
      have := h0 (o.symm n)
      simpa [Q] using this
    rw [map_eq_zero_iff _ o.injective, sub_eq_zero] at this
    exact this
  · have := congrArg (LinearMap.toMatrix₂' k) hQ
    rw [LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix₂'_compl₁₂] at this
    simpa [LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] using this.symm

end GlobalTheory.SimilarTranspose
