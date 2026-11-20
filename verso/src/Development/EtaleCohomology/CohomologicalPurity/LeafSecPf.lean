import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSecPf

/- English proof (translation)
Introduce `A T _ _ φ I μ hφ hμ`. Use `algebraize [φ]`. Establish `: Algebra.Etale A T` using `RingHom.etale_algebraMap.mp hφ`. Use `set J : Ideal T := I.map φ with hJ`. Establish `hle : I ≤ J.comap φ` using `Ideal.le_comap_map`.

Establish `hker : ∀ a ∈ J, μ a = 0`. Introduce `a ha`. Establish `: J ≤ RingHom.ker μ`. Rewrite using `[hJ, Ideal.map_le_iff_le_comap]`. Introduce `c hc`.

Simplify using `only [Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[← RingHom.comp_apply, hμ]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hc`. Conclude with `this ha`. Set `q : A ⧸ I →+* T ⧸ J` to `Ideal.quotientMap J φ hle`.

Set `μb : T ⧸ J →+* A ⧸ I` to `Ideal.Quotient.lift J μ hker`. Establish `hμq : ∀ z, μb (q z) = z`. Introduce `z`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Use `show μb (Ideal.Quotient.mk J (φ c)) = _`.

Simplify using `only [μb, Ideal.Quotient.lift_mk]`. Rewrite using `[← RingHom.comp_apply, hμ]`. Set `g : T →ₐ[A] T ⧸ J` to `{ (q.comp μ) with commutes' := fun a => by show q (μ (φ a)) = Ideal.Quotient.mk J (φ a)`. Rewrite using `[← RingHom.comp_apply μ φ, hμ]`. Use `rfl }`.

Set `f : T →ₐ[A] T ⧸ J` to `Ideal.Quotient.mkₐ A J`. Set `ψ : T ⊗[A] T →ₐ[A] T ⧸ J` to `Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)`. Establish `key : ∀ x : T ⊗[A] T, μb (ψ x) = μ (Algebra.TensorProduct.lmul' A x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [ψ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]`. Use `congr 1`. Apply the tactic sequence `all_goals first | rfl | exact hμq _`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Take `⟨t, ht⟩` from `Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem A T))`. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : μb (Ideal.Quotient.mk J t) = μ t` using `Ideal.Quotient.lift_mk _ _ _`. Rewrite using `[← h1, ht, key, Algebra.FormallyUnramified.lmul_elem, map_one]`.

Introduce `s hs`. Establish `h2` using `congrArg ψ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)`. Simplify using `only [map_mul, ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h2`. Establish `hg : g s = 0` using `by show q (μ s) = 0; rw [hs, map_zero]`. Rewrite `h2` using `[hg, zero_mul]`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht, mul_comm]`. Conclude with `h2.symm`.
-/
theorem LeafSec_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  intro A T _ _ φ I μ hφ hμ
  algebraize [φ]
  have : Algebra.Etale A T := RingHom.etale_algebraMap.mp hφ
  set J : Ideal T := I.map φ with hJ
  have hle : I ≤ J.comap φ := Ideal.le_comap_map
  have hker : ∀ a ∈ J, μ a = 0 := by
    intro a ha
    have : J ≤ RingHom.ker μ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro c hc
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [← RingHom.comp_apply, hμ]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    exact this ha
  let q : A ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hle
  let μb : T ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J μ hker
  have hμq : ∀ z, μb (q z) = z := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    show μb (Ideal.Quotient.mk J (φ c)) = _
    simp only [μb, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply, hμ]
  let g : T →ₐ[A] T ⧸ J :=
    { (q.comp μ) with
      commutes' := fun a => by
        show q (μ (φ a)) = Ideal.Quotient.mk J (φ a)
        rw [← RingHom.comp_apply μ φ, hμ]; rfl }
  let f : T →ₐ[A] T ⧸ J := Ideal.Quotient.mkₐ A J
  let ψ : T ⊗[A] T →ₐ[A] T ⧸ J := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have key : ∀ x : T ⊗[A] T, μb (ψ x) = μ (Algebra.TensorProduct.lmul' A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ψ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]
      congr 1
      all_goals first | rfl | exact hμq _
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem A T))
  refine ⟨t, ?_, ?_⟩
  · have h1 : μb (Ideal.Quotient.mk J t) = μ t := Ideal.Quotient.lift_mk _ _ _
    rw [← h1, ht, key, Algebra.FormallyUnramified.lmul_elem, map_one]
  · intro s hs
    have h2 := congrArg ψ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)
    simp only [map_mul, ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h2
    have hg : g s = 0 := by show q (μ s) = 0; rw [hs, map_zero]
    rw [hg, zero_mul] at h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht, mul_comm]
    exact h2.symm

end LateralTheory.CohomologicalPurity.LeafSecPf
