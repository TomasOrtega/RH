import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
Take `⟨hst, k, f, c, hf, hc, hs, hl⟩` from `h`. Use `⟨?_, k, f, c, hf, hc, hs, fun l => ?_⟩` and prove the remaining obligations. Introduce and unpack `a ha _ ⟨x, hx, rfl⟩`. Conclude with `⟨a • x, hst a ha x hx, by simp⟩`. Take `⟨b, hb, hsp, hiff⟩` from `hl l`.

Use `⟨fun q => e (b q), hb.map' e.toLinearMap (LinearEquiv.ker e), ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `: Set.range (fun q => e (b q)) = e.toLinearMap '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `e.surjective`. Establish `key : ∀ n : ℕ, f l ^ n • v ∈ L.map e.toLinearMap.toAddMonoidHom ↔ f l ^ n • e.symm v ∈ L`. Introduce `n`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxe⟩`.

Establish `: x = f l ^ n • e.symm v`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, e.apply_symm_apply]`. Conclude with `hxe`. Rewrite using `[← this]` and apply the resulting hypothesis.

Introduce `hx`. Conclude with `⟨_, hx, by simp⟩`. Simplify using `only [key]`. Rewrite using `[hiff (e.symm v)]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, hv⟩`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Use `congrArg e hv` as an intermediate fact. Simplify `this` using `[map_sum]`. Introduce and unpack `⟨a, ha, hv⟩`.

Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Simplify using `[map_sum]`.
-/
theorem locFree_map_equiv (R : Subalgebra o Ω) {E E' : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E'] [Module Ω E'] (e : E ≃ₗ[Ω] E') {r : ℕ} {L : AddSubgroup E}
    (h : LocFree R r L) : LocFree R r (L.map e.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hst, k, f, c, hf, hc, hs, hl⟩ := h
  refine ⟨?_, k, f, c, hf, hc, hs, fun l => ?_⟩
  · rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hst a ha x hx, by simp⟩
  · obtain ⟨b, hb, hsp, hiff⟩ := hl l
    refine ⟨fun q => e (b q), hb.map' e.toLinearMap (LinearEquiv.ker e), ?_, fun v => ?_⟩
    · have : Set.range (fun q => e (b q)) = e.toLinearMap '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]
      exact e.surjective
    · have key : ∀ n : ℕ, f l ^ n • v ∈ L.map e.toLinearMap.toAddMonoidHom ↔
          f l ^ n • e.symm v ∈ L := by
        intro n
        constructor
        · rintro ⟨x, hx, hxe⟩
          have : x = f l ^ n • e.symm v := by
            apply e.injective
            rw [map_smul, e.apply_symm_apply]
            exact hxe
          rwa [← this]
        · intro hx
          exact ⟨_, hx, by simp⟩
      simp only [key]
      rw [hiff (e.symm v)]
      constructor
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        have := congrArg e hv
        simpa [map_sum] using this
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        rw [hv]
        simp [map_sum]

/- English proof (translation)
Simplify using `[stdLat, AddSubgroup.mem_pi]`.
-/
theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} {v : ι → Ω} :
    v ∈ stdLat R ι ↔ ∀ j, v j ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

/- English proof (translation)
Use `⟨fun a ha e he => ?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp, fun _ => ?_⟩` and prove the remaining obligations. Rewrite `he`, the goal using `[mem_stdLat]`. Introduce `j`. Simplify using `using R.mul_mem ha (he j)`. Use `⟨fun q => (Pi.basisFun Ω (Fin m)) q, (Pi.basisFun Ω (Fin m)).linearIndependent, (Pi.basisFun Ω (Fin m)).span_eq, fun e => ?_⟩` and prove the remaining obligations.

Establish `hsum : ∀ a : Fin m → Ω, (∑ q, a q • (Pi.basisFun Ω (Fin m)) q) = a`. Introduce `a`. Simplify using `using (Pi.basisFun Ω (Fin m)).sum_repr a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, hn⟩`.

Simplify using `only [one_pow, one_smul] at hn`. Conclude with `⟨e, fun q => ⟨0, by simpa using (mem_stdLat R).1 hn q⟩, (hsum e).symm⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum, pow_zero, one_smul, mem_stdLat]`.

Introduce `q`. Take `⟨n, hn⟩` from `ha q`. Simplify using `using hn`.
-/
theorem locFree_stdLat (R : Subalgebra o Ω) (m : ℕ) : LocFree R m (stdLat R (Fin m)) := by
  classical
  refine ⟨fun a ha e he => ?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem,
    by simp, fun _ => ?_⟩
  · rw [mem_stdLat] at he ⊢
    intro j
    simpa using R.mul_mem ha (he j)
  · refine ⟨fun q => (Pi.basisFun Ω (Fin m)) q, (Pi.basisFun Ω (Fin m)).linearIndependent,
      (Pi.basisFun Ω (Fin m)).span_eq, fun e => ?_⟩
    have hsum : ∀ a : Fin m → Ω, (∑ q, a q • (Pi.basisFun Ω (Fin m)) q) = a := by
      intro a
      simpa using (Pi.basisFun Ω (Fin m)).sum_repr a
    constructor
    · rintro ⟨_, hn⟩
      simp only [one_pow, one_smul] at hn
      exact ⟨e, fun q => ⟨0, by simpa using (mem_stdLat R).1 hn q⟩, (hsum e).symm⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      rw [hsum, pow_zero, one_smul, mem_stdLat]
      intro q
      obtain ⟨n, hn⟩ := ha q
      simpa using hn

/- English proof (translation)
Use `locFree_map_equiv R (LinearEquiv.smulOfNeZero Ω E c⁻¹ (inv_ne_zero hc)) h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Conclude with `⟨c • v, hv, by simp [smul_smul, hc]⟩`. Introduce and unpack `⟨x, hx, rfl⟩ show c • (c⁻¹ • x) ∈ L`. Simplify `hx` using `[smul_smul, hc]`.
-/
theorem locFree_divLat (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] {c : Ω}
    (hc : c ≠ 0) {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) : LocFree R r (divLat c L) := by
  have := locFree_map_equiv R (LinearEquiv.smulOfNeZero Ω E c⁻¹ (inv_ne_zero hc)) h
  convert this using 1
  ext v
  constructor
  · intro hv
    exact ⟨c • v, hv, by simp [smul_smul, hc]⟩
  · rintro ⟨x, hx, rfl⟩
    show c • (c⁻¹ • x) ∈ L
    simpa [smul_smul, hc] using hx

/- English proof (translation)
Set `e` to `q.quotKerEquivOfSurjective hq`. Establish `h1 : (L.map (LinearMap.ker q).mkQ.toAddMonoidHom).map e.toLinearMap.toAddMonoidHom = L.map q.toAddMonoidHom`. Rewrite using `[AddSubgroup.map_map]`. Use `congr 1`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← h1]`. Conclude with `locFree_map_equiv R e h`. Introduce `h`. Establish `h2 : (L.map q.toAddMonoidHom).map e.symm.toLinearMap.toAddMonoidHom = L.map (LinearMap.ker q).mkQ.toAddMonoidHom`.

Rewrite using `[← h1, AddSubgroup.map_map]`. Use extensionality with `v`. Simplify using the standard rewrite rules. Rewrite using `[← h2]`. Conclude with `locFree_map_equiv R e.symm h`.
-/
theorem locFree_map_mkQ_iff (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E₂] [Module Ω E₂] (q : E →ₗ[Ω] E₂) (hq : Function.Surjective q) {r : ℕ}
    (L : AddSubgroup E) :
    LocFree R r (L.map (LinearMap.ker q).mkQ.toAddMonoidHom) ↔ LocFree R r (L.map q.toAddMonoidHom) := by
  let e := q.quotKerEquivOfSurjective hq
  have h1 : (L.map (LinearMap.ker q).mkQ.toAddMonoidHom).map e.toLinearMap.toAddMonoidHom =
      L.map q.toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    congr 1
  constructor
  · intro h
    rw [← h1]
    exact locFree_map_equiv R e h
  · intro h
    have h2 : (L.map q.toAddMonoidHom).map e.symm.toLinearMap.toAddMonoidHom =
        L.map (LinearMap.ker q).mkQ.toAddMonoidHom := by
      rw [← h1, AddSubgroup.map_map]
      ext v
      simp
    rw [← h2]
    exact locFree_map_equiv R e.symm h

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Establish `h` using `IsBaseChange.pi (S := C) (fun _ : ι => Algebra.linearMap Ω C) (fun _ => IsBaseChange.linearMap Ω C)`. Conclude with `h`.
-/
theorem isBaseChange_bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) [Finite ι] :
    IsBaseChange C (bcMap Ω C ι) := by
  have := Fintype.ofFinite ι
  have h := IsBaseChange.pi (S := C) (fun _ : ι => Algebra.linearMap Ω C)
    (fun _ => IsBaseChange.linearMap Ω C)
  exact h

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv ⊢`. Introduce `j hj`.

Simplify using `[bcMap, hv j hj]`. Introduce `v hv`. Simplify using `only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv`. Establish `: v = ∑ j, v j • bcMap Ω C (Fin n) (if (j : ℕ) < i then 0 else Pi.single j 1)`. Use extensionality with `k`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single k]`. Distinguish the cases in `hk : (k : ℕ) < i`. Simplify using `[hk, hv k hk, bcMap]`. Simplify using `[hk, bcMap]`.

Introduce `j _ hjk`. Distinguish the cases in `hj : (j : ℕ) < i`. Simplify using `[hj, bcMap]`. Simplify using `[hj, bcMap, Pi.single_apply, hjk.symm]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)` and prove the remaining obligations. Simplify using `only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]`. Introduce `k hk`. Distinguish the cases in `hj : (j : ℕ) < i`.

Simplify using `[hj]`. Establish `: k ≠ j` using `by rintro rfl; exact hj hk`. Simplify using `[hj, Pi.single_apply, this]`.
-/
theorem span_bcMap_annSub (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (n i : ℕ) :
    Submodule.span C (bcMap Ω C (Fin n) '' (annSub Ω n i : Set (Fin n → Ω))) = annSub C n i := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv ⊢
    intro j hj
    simp [bcMap, hv j hj]
  · intro v hv
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv
    have : v = ∑ j, v j • bcMap Ω C (Fin n) (if (j : ℕ) < i then 0 else Pi.single j 1) := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · by_cases hk : (k : ℕ) < i
        · simp [hk, hv k hk, bcMap]
        · simp [hk, bcMap]
      · intro j _ hjk
        by_cases hj : (j : ℕ) < i
        · simp [hj, bcMap]
        · simp [hj, bcMap, Pi.single_apply, hjk.symm]
      · simp
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro k hk
    by_cases hj : (j : ℕ) < i
    · simp [hj]
    · have : k ≠ j := by rintro rfl; exact hj hk
      simp [hj, Pi.single_apply, this]

/- English proof (translation)
Unfold `spanOver`. Rewrite using `[AddMonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, _, ⟨_, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨a • (b' z, b v), ⟨a, ha, _, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨a, ha, _, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨a, ha, _, ⟨_, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩`.
-/
theorem spanOver_swap {C V Z Vc Zc : Type} [Field C] [Algebra o C] (RC : Subalgebra o C)
    [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (Γ : AddSubgroup (Z × V)) :
    spanOver RC (Prod.map b b' '' (Γ.map (AddEquiv.prodComm (M := Z) (N := V)).toAddMonoidHom : AddSubgroup (V × Z))) =
      (spanOver RC (Prod.map b' b '' Γ)).map (AddEquiv.prodComm (M := Zc) (N := Vc)).toAddMonoidHom := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨_, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • (b' z, b v), ⟨a, ha, _, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨_, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
