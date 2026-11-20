import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

noncomputable section

namespace PI.VolStabSW

open Polynomial

/- English proof (translation)
Distinguish the cases in `hsq : ∃ c : k, c * c = D`. Take `⟨c, hc⟩` from `hsq`. Establish `hc0 : c ≠ 0` using `by rintro rfl; exact hD (by rw [← hc, mul_zero])`. Set `σ' : (k × k) ≃ₐ[k] (k × k)` to `{ RingEquiv.prodComm with commutes' := fun r => rfl }`. Establish `hσ : ∀ x : k × k, σ' x = x.swap` using `fun x => rfl`.

Use `⟨k × k, inferInstance, inferInstance, σ', (c, -c), ⟨fun x => by simp [hσ], Or.inr ⟨AlgEquiv.refl, fun x => by simp [hσ]⟩⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [hc]`. Apply the tactic sequence `ext <;> simp [hσ]`. Establish `h2c : (2 : k) * c ≠ 0` using `mul_ne_zero h2 hc0`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x1, y1⟩ ⟨x2, y2⟩ h`. Simplify using `only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h`. Take `⟨h1, h2'⟩` from `h`. Establish `hy : y1 = y2`. Establish `: (2 * c) * (y1 - y2) = 0` using `by linear_combination h1 - h2'`.

Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2c)`. Substitute `hy` using the available equality. Establish `hx : x1 = x2` using `by linear_combination h1`. Rewrite using `[hx]`. Introduce and unpack `⟨u, w⟩`.

Use `⟨((u + w) / 2, (u - w) / (2 * c)), ?_⟩` and prove the remaining obligations. Simplify using `only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Prove the components needed by the constructor for the conclusion. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `push Not at hsq`. Set `f : k[X]` to `X ^ 2 - C D`. Establish `hfdeg : f.natDegree = 2` using `natDegree_X_pow_sub_C`.

Establish `hnr : ∀ x, ¬ IsRoot f x`. Introduce `x hx`. Apply `hsq x` to reduce the goal to its premises. Establish `: x ^ 2 - D = 0` using `by simpa [f] using hx`. Take the linear combination `this`.

Establish `hirr : Irreducible f` using `irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide) hnr`. Establish `: Fact (Irreducible f)` using `⟨hirr⟩`. Establish `hf0 : f ≠ 0` using `hirr.ne_zero`. Set `K` to `AdjoinRoot f`. Set `r : K` to `AdjoinRoot.root f`.

Establish `hr2 : r * r = algebraMap k K D`. Establish `h` using `AdjoinRoot.eval₂_root f`. Simplify using `only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h`. Rewrite using `[← sq, show algebraMap k K D = AdjoinRoot.of f D from rfl]`. Take the linear combination `h`.

Establish `hneg : f.eval₂ (Algebra.ofId k K) (-r) = 0`. Simplify using `only [f, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq]`. Establish `h` using `AdjoinRoot.eval₂_root f`. Simplify using `only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h`. Conclude with `h`.

Set `τ : K →ₐ[k] K` to `AdjoinRoot.liftAlgHom f (Algebra.ofId k K) (-r) hneg`. Establish `hτr : τ r = -r` using `AdjoinRoot.liftAlgHom_root _ _ _ _`. Establish `hττ : τ.comp τ = AlgHom.id k K`. Apply `AdjoinRoot.algHom_ext` to reduce the goal to its premises. Use `show τ (τ r) = r`.

Rewrite using `[hτr, map_neg, hτr, neg_neg]`. Set `σ' : K ≃ₐ[k] K` to `AlgEquiv.ofAlgHom τ τ hττ hττ`. Establish `hσr : σ' r = -r` using `hτr`. Establish `hr0 : r ≠ 0`. Introduce `h`.

Rewrite `hr2` using `[h, mul_zero]`. Conclude with `hD ((algebraMap k K).injective (by rw [← hr2, map_zero]))`. Establish `h2K : (2 : K) ≠ 0`. Introduce `h`. Apply `h2` to reduce the goal to its premises.

Apply `(algebraMap k K).injective` to reduce the goal to its premises. Rewrite using `[map_ofNat, h, map_zero]`. Establish `hfin : Module.finrank k K = 2`. Rewrite using `[(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdeg]`. Use `⟨K, inferInstance, inferInstance, σ', r, ⟨fun x => ?_, Or.inl ⟨Field.toIsField K, hfin, fun h => ?_⟩⟩, hr2, hσr, ?_⟩` and prove the remaining obligations.

Use `show τ (τ x) = x`. Conclude with `congrArg (fun g : K →ₐ[k] K => g x) hττ`. Establish `h1 : σ' r = r` using `by rw [h]; rfl`. Rewrite `h1` using `[hσr]`. Establish `: (2 : K) * r = 0` using `by linear_combination -h1`.

Conclude with `hr0 ((mul_eq_zero.1 this).resolve_left h2K)`. Establish `hinj : Function.Injective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r)`. Introduce and unpack `⟨x1, y1⟩ ⟨x2, y2⟩ h`. Simplify using `only at h`. Distinguish the cases in `hy : y1 = y2`.

Substitute `hy` using the available equality. Establish `: algebraMap k K x1 = algebraMap k K x2` using `by linear_combination h`. Rewrite using `[(algebraMap k K).injective this]`. It suffices to derive a contradiction. Establish `hy' : y1 - y2 ≠ 0` using `sub_ne_zero.2 hy`.

Establish `hyK : algebraMap k K (y1 - y2) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (algebraMap k K).injective]`. Conclude with `hy'`. Establish `hm : algebraMap k K (y1 - y2) * r = algebraMap k K (x2 - x1)`. Rewrite using `[map_sub, map_sub]`.

Take the linear combination `h`. Establish `hrr : r = algebraMap k K ((x2 - x1) / (y1 - y2))`. Rewrite using `[map_div₀, eq_div_iff hyK, mul_comm]`. Conclude with `hm`. Apply `hsq ((x2 - x1) / (y1 - y2))` to reduce the goal to its premises.

Apply `(algebraMap k K).injective` to reduce the goal to its premises. Rewrite using `[map_mul, ← hrr, hr2]`. Establish `hKm : Module.Finite k K` using `(AdjoinRoot.powerBasis hf0).finite`. Establish `hKf : Finite K` using `Module.finite_of_finite k`. Use `hinj.bijective_of_nat_card_le ?_` and prove the remaining obligations.

Use `letI := Fintype.ofFinite k`. Use `letI := Fintype.ofFinite K`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k), hfin, Fintype.card_prod, sq]`.
-/
theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  classical
  by_cases hsq : ∃ c : k, c * c = D
  · obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by rintro rfl; exact hD (by rw [← hc, mul_zero])
    let σ' : (k × k) ≃ₐ[k] (k × k) :=
      { RingEquiv.prodComm with commutes' := fun r => rfl }
    have hσ : ∀ x : k × k, σ' x = x.swap := fun x => rfl
    refine ⟨k × k, inferInstance, inferInstance, σ', (c, -c), ⟨fun x => by simp [hσ], Or.inr
      ⟨AlgEquiv.refl, fun x => by simp [hσ]⟩⟩, ?_, ?_, ?_⟩
    · ext <;> simp [hc]
    · ext <;> simp [hσ]
    · have h2c : (2 : k) * c ≠ 0 := mul_ne_zero h2 hc0
      constructor
      · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
        obtain ⟨h1, h2'⟩ := h
        have hy : y1 = y2 := by
          have : (2 * c) * (y1 - y2) = 0 := by linear_combination h1 - h2'
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2c)
        subst hy
        have hx : x1 = x2 := by linear_combination h1
        rw [hx]
      · rintro ⟨u, w⟩
        refine ⟨((u + w) / 2, (u - w) / (2 * c)), ?_⟩
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        constructor
        · field_simp
          ring
        · field_simp
          ring
  · push Not at hsq
    let f : k[X] := X ^ 2 - C D
    have hfdeg : f.natDegree = 2 := natDegree_X_pow_sub_C
    have hnr : ∀ x, ¬ IsRoot f x := by
      intro x hx
      apply hsq x
      have : x ^ 2 - D = 0 := by simpa [f] using hx
      linear_combination this
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide) hnr
    have : Fact (Irreducible f) := ⟨hirr⟩
    have hf0 : f ≠ 0 := hirr.ne_zero
    let K := AdjoinRoot f
    let r : K := AdjoinRoot.root f
    have hr2 : r * r = algebraMap k K D := by
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      rw [← sq, show algebraMap k K D = AdjoinRoot.of f D from rfl]
      linear_combination h
    have hneg : f.eval₂ (Algebra.ofId k K) (-r) = 0 := by
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq]
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      exact h
    let τ : K →ₐ[k] K := AdjoinRoot.liftAlgHom f (Algebra.ofId k K) (-r) hneg
    have hτr : τ r = -r := AdjoinRoot.liftAlgHom_root _ _ _ _
    have hττ : τ.comp τ = AlgHom.id k K := by
      apply AdjoinRoot.algHom_ext
      show τ (τ r) = r
      rw [hτr, map_neg, hτr, neg_neg]
    let σ' : K ≃ₐ[k] K := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσr : σ' r = -r := hτr
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr2
      exact hD ((algebraMap k K).injective (by rw [← hr2, map_zero]))
    have h2K : (2 : K) ≠ 0 := by
      intro h
      apply h2
      apply (algebraMap k K).injective
      rw [map_ofNat, h, map_zero]
    have hfin : Module.finrank k K = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
    refine ⟨K, inferInstance, inferInstance, σ', r, ⟨fun x => ?_, Or.inl ⟨Field.toIsField K, hfin,
      fun h => ?_⟩⟩, hr2, hσr, ?_⟩
    · show τ (τ x) = x
      exact congrArg (fun g : K →ₐ[k] K => g x) hττ
    · have h1 : σ' r = r := by rw [h]; rfl
      rw [hσr] at h1
      have : (2 : K) * r = 0 := by linear_combination -h1
      exact hr0 ((mul_eq_zero.1 this).resolve_left h2K)
    · have hinj : Function.Injective
          (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
        rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only at h
        by_cases hy : y1 = y2
        · subst hy
          have : algebraMap k K x1 = algebraMap k K x2 := by linear_combination h
          rw [(algebraMap k K).injective this]
        · exfalso
          have hy' : y1 - y2 ≠ 0 := sub_ne_zero.2 hy
          have hyK : algebraMap k K (y1 - y2) ≠ 0 := by
            rw [Ne, map_eq_zero_iff _ (algebraMap k K).injective]; exact hy'
          have hm : algebraMap k K (y1 - y2) * r = algebraMap k K (x2 - x1) := by
            rw [map_sub, map_sub]; linear_combination h
          have hrr : r = algebraMap k K ((x2 - x1) / (y1 - y2)) := by
            rw [map_div₀, eq_div_iff hyK, mul_comm]
            exact hm
          apply hsq ((x2 - x1) / (y1 - y2))
          apply (algebraMap k K).injective
          rw [map_mul, ← hrr, hr2]
      have hKm : Module.Finite k K := (AdjoinRoot.powerBasis hf0).finite
      have hKf : Finite K := Module.finite_of_finite k
      refine hinj.bijective_of_nat_card_le ?_
      letI := Fintype.ofFinite k
      letI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
        hfin, Fintype.card_prod, sq]

end PI.VolStabSW
