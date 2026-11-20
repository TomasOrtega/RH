import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

/- English proof (translation)
Set `_` to `MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)`. Establish `hA : (map (Int.castRingHom ℚ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ) = algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ)`. Rewrite using `[algebraMap_def, algebraMap_int_eq]`. Rewrite `hf` using `[hA, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := σ)))]`. Take `⟨⟨⟨g, hg⟩, ⟨_, m, hm, rfl⟩⟩, h⟩` from `hf`.

Establish `hinj : Function.Injective (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ))`. Rewrite using `[← hA]`. Conclude with `map_injective _ Int.cast_injective`. Establish `h' : C m * f = g` using `by rw [mul_comm]; exact hinj (by simpa using h)`. Take `⟨t, ht⟩ : m ∣ (m.natAbs : ℤ)` from `Int.dvd_natAbs.mpr dvd_rfl`.

Use `⟨m.natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.ne_zero hm), ?_⟩` and prove the remaining obligations. Establish `: (m.natAbs : MvPolynomial σ ℤ) = C (m.natAbs : ℤ)` using `(map_natCast C _).symm`. Rewrite using `[this, ht, C_mul, mul_comm (C m), mul_assoc, h']`. Conclude with `I.mul_mem_left _ hg`.
-/
theorem exists_natMul_mem_of_map_rat_mem {σ : Type} (I : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ)
    (hf : map (Int.castRingHom ℚ) f ∈ Ideal.map (map (Int.castRingHom ℚ)) I) :
    ∃ M : ℕ, M ≠ 0 ∧ (M : MvPolynomial σ ℤ) * f ∈ I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
  have hA : (map (Int.castRingHom ℚ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ) =
      algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) := by
    rw [algebraMap_def, algebraMap_int_eq]
  rw [hA, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := σ)))] at hf
  obtain ⟨⟨⟨g, hg⟩, ⟨_, m, hm, rfl⟩⟩, h⟩ := hf
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ)) := by
    rw [← hA]; exact map_injective _ Int.cast_injective
  have h' : C m * f = g := by rw [mul_comm]; exact hinj (by simpa using h)
  obtain ⟨t, ht⟩ : m ∣ (m.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.ne_zero hm), ?_⟩
  have : (m.natAbs : MvPolynomial σ ℤ) = C (m.natAbs : ℤ) := (map_natCast C _).symm
  rw [this, ht, C_mul, mul_comm (C m), mul_assoc, h']
  exact I.mul_mem_left _ hg

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D L hL p hp hbad`. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hQ : coneNullIdeal y L = (coneNullIdealZ y L).map (map (Int.castRingHom ℚ))`. Rewrite using `[coneNullIdeal, coneNullIdealZ, Ideal.map_span, Set.image_union, ← Set.range_comp]`. Both sides reduce to the same expression.

Use `set I := coneNullIdealZ y L`. Set `π` to `Ideal.Quotient.mk I`. Take `⟨N₁, hN₁⟩` from `PullConeNull.proof K ι Ω y D L hL`. Establish `key : ∀ c : ∀ k, ι k, ∃ N M : ℕ, ¬ p ∣ M ∧ (M : MRing ι ⧸ I) * π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N = 0`. Introduce `c`.

Use `set u := π (∏ k, (X ⟨k, c k⟩ : MRing ι))`. Take `⟨M₁, hM₁, h₁⟩` from `exists_natMul_mem_of_map_rat_mem I ((∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N₁) (by rw [← hQ]; simpa [map_prod] using hN₁ c)`. Establish `e₁ : (M₁ : MRing ι ⧸ I) * u ^ N₁ = 0`. Rewrite using `[← map_natCast π, ← map_pow, ← map_mul]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr h₁`.

Choose the witnesses or unpack the hypotheses as in `⟨N₂, h, e₂⟩ : ∃ N₂ h, u ^ N₂ = (p : MRing ι ⧸ I) * h := by`. Set `φ : MRing ι →+* MvPolynomial (Σ k, ι k) (ZMod p)` to `map (Int.castRingHom (ZMod p))`. Establish `hrad : φ (∏ k, (X ⟨k, c k⟩ : MRing ι)) ∈ (I.map φ).radical`. Rewrite using `[← IsJacobsonRing.out inferInstance (Ideal.radical_isRadical (I.map φ)), Ideal.jacobson, Submodule.mem_sInf]`. Introduce and unpack `m ⟨hJm, hm⟩`.

Use `letI := Ideal.Quotient.field m`. Use `finite_of_finite_type_of_isJacobsonRing (ZMod p) (MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)` as an intermediate fact. Set `ψ` to `IsAlgClosed.lift (R := ZMod p) (M := AlgebraicClosure (ZMod p)) (S := MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)`. Set `z : (Σ k, ι k) → AlgebraicClosure (ZMod p)` to `fun q => ψ (Ideal.Quotient.mk m (X q))`. Establish `hev : ∀ f : MRing ι, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) = ψ (Ideal.Quotient.mk m (φ f))`.

Introduce `f`. Establish `e : (eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p)))) = ((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)` and prove the remaining obligations. Conclude with `RingHom.congr_fun (RingHom.ext_int (((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))).comp C) ((((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ).comp C)) r`. Simplify using `[z, φ]`.

Conclude with `RingHom.congr_fun e f`. Establish `hker : ∀ f : MRing ι, f ∈ I → ψ (Ideal.Quotient.mk m (φ f)) = 0` using `fun f hf => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.le_radical (Ideal.mem_map_of_mem φ hf))), map_zero]`. Assume the negation of the conclusion as `hc`. Use `hbad ⟨z, fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]`. Use `Ideal.mul_mem_right _ m (Ideal.Quotient.eq_zero_iff_mem.mp (ψ.injective ?_))` and prove the remaining obligations. Simplify `h0` using `[z, φ]`. Rewrite using `[hev]`. Conclude with `hker f (Ideal.subset_span (Or.inl hf))`.

Rewrite using `[hev]`. Conclude with `hker _ (Ideal.subset_span (Or.inr ⟨j, rfl⟩))`. Take `⟨n, hn⟩` from `Ideal.mem_radical_iff.mp hrad`. Rewrite `hn` using `[← map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective φ (map_surjective _ ZMod.intCast_surjective)]`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hn`.

Establish `hb' : b ∈ RingHom.ker φ` using `by simpa [RingHom.mem_ker] using hb`. Rewrite `hb'` using `[ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨h, rfl⟩` from `hb'`. Use `⟨n, π h, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_natCast C p, map_natCast, mul_comm]`.

Take `⟨a, M₀, hM₀, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hM₁ p hp.ne_one`. Use `⟨a * N₂ + N₁, M₀, hM₀, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, pow_mul', e₂, mul_pow]`. Move the coercions through the operations in `at e₁`. Take the linear combination `h ^ a * e₁`.

Use `choose Nc Mc hMc hc using key`. Use `⟨Finset.univ.sup Nc, ∏ c, Mc c, ?_, fun c => ?_⟩` and prove the remaining obligations. Conclude with `fun hdvd => (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd |>.elim fun c ⟨_, h⟩ => hMc c h`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Nat.add_sub_cancel' (Finset.le_sup (f := Nc) (Finset.mem_univ c)), pow_add]`. Use `push_cast`.

Take the linear combination `((∏ c' ∈ Finset.univ.erase c, (Mc c' : MRing ι ⧸ I)) * π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ (Finset.univ.sup Nc - Nc c)) * hc c`.
-/
theorem PullConeNullModP.proof : PullConeNullModP.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL p hp hbad
  have : Fact p.Prime := ⟨hp⟩
  have hQ : coneNullIdeal y L = (coneNullIdealZ y L).map (map (Int.castRingHom ℚ)) := by
    rw [coneNullIdeal, coneNullIdealZ, Ideal.map_span, Set.image_union, ← Set.range_comp]; rfl
  set I := coneNullIdealZ y L
  let π := Ideal.Quotient.mk I
  obtain ⟨N₁, hN₁⟩ := PullConeNull.proof K ι Ω y D L hL

  have key : ∀ c : ∀ k, ι k, ∃ N M : ℕ, ¬ p ∣ M ∧
      (M : MRing ι ⧸ I) * π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N = 0 := by
    intro c
    set u := π (∏ k, (X ⟨k, c k⟩ : MRing ι))

    obtain ⟨M₁, hM₁, h₁⟩ := exists_natMul_mem_of_map_rat_mem I ((∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N₁)
      (by rw [← hQ]; simpa [map_prod] using hN₁ c)
    have e₁ : (M₁ : MRing ι ⧸ I) * u ^ N₁ = 0 := by
      rw [← map_natCast π, ← map_pow, ← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h₁

    obtain ⟨N₂, h, e₂⟩ : ∃ N₂ h, u ^ N₂ = (p : MRing ι ⧸ I) * h := by
      let φ : MRing ι →+* MvPolynomial (Σ k, ι k) (ZMod p) := map (Int.castRingHom (ZMod p))
      have hrad : φ (∏ k, (X ⟨k, c k⟩ : MRing ι)) ∈ (I.map φ).radical := by
        rw [← IsJacobsonRing.out inferInstance (Ideal.radical_isRadical (I.map φ)), Ideal.jacobson, Submodule.mem_sInf]
        rintro m ⟨hJm, hm⟩
        letI := Ideal.Quotient.field m
        have := finite_of_finite_type_of_isJacobsonRing (ZMod p) (MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let ψ := IsAlgClosed.lift (R := ZMod p) (M := AlgebraicClosure (ZMod p))
          (S := MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let z : (Σ k, ι k) → AlgebraicClosure (ZMod p) := fun q => ψ (Ideal.Quotient.mk m (X q))
        have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) =
            ψ (Ideal.Quotient.mk m (φ f)) := by
          intro f
          have e : (eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p)))) =
              ((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ := by
            refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
            · exact RingHom.congr_fun (RingHom.ext_int
                (((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))).comp C)
                ((((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ).comp C)) r
            · simp [z, φ]
          exact RingHom.congr_fun e f
        have hker : ∀ f : MRing ι, f ∈ I → ψ (Ideal.Quotient.mk m (φ f)) = 0 := fun f hf => by
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.le_radical (Ideal.mem_map_of_mem φ hf))), map_zero]
        by_contra hc
        refine hbad ⟨z, fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_, fun j => ?_⟩
        · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
          refine Ideal.mul_mem_right _ m (Ideal.Quotient.eq_zero_iff_mem.mp (ψ.injective ?_))
          simpa [z, φ] using h0
        · rw [hev]; exact hker f (Ideal.subset_span (Or.inl hf))
        · rw [hev]; exact hker _ (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
      rw [← map_pow, ← Ideal.mem_comap,
        Ideal.comap_map_of_surjective φ (map_surjective _ ZMod.intCast_surjective)] at hn
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hn
      have hb' : b ∈ RingHom.ker φ := by simpa [RingHom.mem_ker] using hb
      rw [ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton'] at hb'
      obtain ⟨h, rfl⟩ := hb'
      refine ⟨n, π h, ?_⟩
      rw [← map_pow, ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_natCast C p,
        map_natCast, mul_comm]

    obtain ⟨a, M₀, hM₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₁ p hp.ne_one
    refine ⟨a * N₂ + N₁, M₀, hM₀, ?_⟩
    rw [pow_add, pow_mul', e₂, mul_pow]
    push_cast at e₁
    linear_combination h ^ a * e₁
  choose Nc Mc hMc hc using key
  refine ⟨Finset.univ.sup Nc, ∏ c, Mc c, ?_, fun c => ?_⟩
  · exact fun hdvd => (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd |>.elim fun c ⟨_, h⟩ => hMc c h
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
      ← Nat.add_sub_cancel' (Finset.le_sup (f := Nc) (Finset.mem_univ c)), pow_add]
    push_cast
    linear_combination ((∏ c' ∈ Finset.univ.erase c, (Mc c' : MRing ι ⧸ I)) *
      π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ (Finset.univ.sup Nc - Nc c)) * hc c

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
