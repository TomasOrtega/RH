import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc`. Establish `hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))`. Introduce `g`. Establish `h` using `hbar.1 g 0`. Simplify `h` using `[w]`.

Establish `hd1 : ∀ g : F.G0, ρ.r g 1 1 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹`. Introduce `g`. Establish `h` using `hbar.1 g 1`. Simplify `h` using `[w]`. Establish `hup : ∀ g : F.G0, ρ.r g 0 1 = 0`.

Introduce `g`. Establish `h : ρ.r g 0 1 ∈ ρ.triM` using `Ideal.subset_span ⟨g, 0, 1, by decide, rfl⟩`. Rewrite `h` using `[htri, Ideal.mem_bot]`. Conclude with `h`. Establish `hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))`.

Introduce `v s`. Establish `h` using `hbar.2 v 0 s`. Simplify `h` using `[w]`. Establish `hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹`. Introduce `v s`.

Establish `h` using `hbar.2 v 1 s`. Simplify `h` using `[w]`. Use `⟨hlc 1 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g h`. Simplify using `only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def, Units.val_inv_eq_inv_val]`.

Rewrite using `[hd0, hd1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `g show ρ.r (F.star g) 1 0 = ρ.r g 1 0`. Rewrite using `[(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0]`. Both sides reduce to the same expression.

Introduce `v`. Take `⟨t, ht⟩` from `hF.f3 v`. Use `set d : k := ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ with hdd`. Establish `hne` using `Units.ne_zero (F.Ψ (F.loc v t))`. Establish `hd : d ≠ 0`.

Introduce `h`. Apply `ht` to reduce the goal to its premises. Rewrite `h` using `[hdd, sub_eq_zero]`. Rewrite using `[Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨algebraMap k Q d⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩` and prove the remaining obligations. Establish `h10` using `congrFun (congrFun (ρ.ord v ![s, t]) 1) 0`. Simplify using `only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one, (by decide : (1 : …`. Establish `hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s` using `fun _ => rfl`. Rewrite `h10` using `[hd0, hd1, hψ0, hψ1, hl, hl]`.

Simplify using `only [mul_zero, sub_zero] at h10`. Establish `hinv : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q d⁻¹ = 1`. Rewrite using `[← map_sub, ← map_mul, ← hdd, mul_inv_cancel₀ hd, map_one]`. Simplify using `only [Algebra.smul_def, Units.val_inv_eq_inv_val, map_sub]`. Take the linear combination `algebraMap k Q d⁻¹ * h10 - ρ.r (F.loc0 v s) 1 0 * hinv`.
-/
theorem UpperTheory.V.Fr.framePoint_fiber_nonempty :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 2 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strS Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hup : ∀ g : F.G0, ρ.r g 0 1 = 0 := by
    intro g
    have h : ρ.r g 0 1 ∈ ρ.triM := Ideal.subset_span ⟨g, 0, 1, by decide, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def, Units.val_inv_eq_inv_val]
    rw [hd0, hd1]
    ring
  · intro g
    show ρ.r (F.star g) 1 0 = ρ.r g 1 0
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0]
    rfl
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    set d : k := ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ with hdd
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hd : d ≠ 0 := by
      intro h
      apply ht
      rw [hdd, sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    refine ⟨algebraMap k Q d⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![s, t]) 1) 0
    simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one, (by decide : (1 : Fin 2) ≠ 0), if_false, if_true, smul_zero,
      sub_zero, smul_eq_mul, mul_one] at h10
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    rw [hd0, hd1, hψ0, hψ1, hl, hl] at h10
    simp only [mul_zero, sub_zero] at h10
    have hinv : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹)
        * algebraMap k Q d⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, ← hdd, mul_inv_cancel₀ hd, map_one]
    simp only [Algebra.smul_def, Units.val_inv_eq_inv_val, map_sub]
    linear_combination algebraMap k Q d⁻¹ * h10 - ρ.r (F.loc0 v s) 1 0 * hinv
