import Mathlib

namespace GlobalTheory.FiniteFieldCountEstimate

/- English proof (translation)
Set `K` to `FractionRing R`. Set `L` to `TensorProduct R B K`. Set `f : B →ₐ[R] L` to `Algebra.TensorProduct.includeLeft`. Set `iR : K →ₐ[R] L` to `Algebra.TensorProduct.includeRight`. Establish `hf : Function.Injective f` using `Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)`.

Establish `hfa : ∀ b, algebraMap B L b = f b` using `fun b => rfl`. Establish `hK : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero`. Set `u : L` to `iR (algebraMap R K π)⁻¹`. Establish `hcu : algebraMap R L π * u = 1`. Rewrite using `[← iR.commutes π, ← map_mul, mul_inv_cancel₀ hK, map_one]`.

Establish `htfL : Module.IsTorsionFree R L`. Use `Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => ?_` and prove the remaining obligations. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`.

Establish `hrK : algebraMap R K r ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hrK, map_one, one_mul]`. Use `_ = iR (algebraMap R K r)⁻¹ * (r • x) := by`. Rewrite using `[map_mul, iR.commutes, Algebra.smul_def, mul_assoc]`.

Use `_ = 0 := by rw [hrx, mul_zero]`. Establish `: IsNoetherianRing B` using `Algebra.FiniteType.isNoetherianRing R B`. Take `⟨k, gs, hgs⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)`. Set `t : Fin k → L` to `fun i => u * f (gs i)`. Establish `hπt : ∀ i, algebraMap R L π * t i = f (gs i)` using `fun i => by`.

Simplify using `only [t]`. Rewrite using `[← mul_assoc, hcu, one_mul]`. Set `A : MvPolynomial (Fin k) B →ₐ[R] L` to `(MvPolynomial.aeval t).restrictScalars R`. Set `S : Subalgebra R L` to `A.range`. Establish `hAC : ∀ b, A (MvPolynomial.C b) = f b` using `fun b => by simp [A, hfa]`.

Establish `hAX : ∀ i, A (MvPolynomial.X i) = t i` using `fun i => by simp [A]`. Establish `hmemf : ∀ b, f b ∈ S` using `fun b => ⟨MvPolynomial.C b, hAC b⟩`. Set `φ : B →ₐ[R] S` to `f.codRestrict S hmemf`. Establish `htfS : Module.IsTorsionFree R S` using `Function.Injective.moduleIsTorsionFree (fun x : S => (x : L)) Subtype.val_injective (fun r x => rfl)`. Establish `hind : ∀ Q : S → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b' : S, algebraMap R S π * b' = φ g → Q b') → (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x`.

Introduce `Q hB hI hadd hmul x`. Establish `key : ∀ P, Q ⟨A P, P, rfl⟩`. Introduce `P`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C b`.

Establish `e : (⟨A (MvPolynomial.C b), _, rfl⟩ : S) = φ b` using `Subtype.ext (hAC b)`. Rewrite using `[e]`. Conclude with `hB b`. Consider the case `add p q hp hq`. Establish `e : (⟨A (p + q), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ + ⟨A q, q, rfl⟩` using `Subtype.ext (map_add A p q)`.

Rewrite using `[e]`. Conclude with `hadd _ _ hp hq`. Consider the case `mul_X p i hp`. Establish `e : (⟨A (p * MvPolynomial.X i), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ * ⟨A (MvPolynomial.X i), _, rfl⟩` using `Subtype.ext (map_mul A _ _)`. Rewrite using `[e]`.

Use `hmul _ _ hp (hI (gs i) (by rw [← hgs]; exact Submodule.subset_span ⟨i, rfl⟩) _ ?_)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show algebraMap R L π * A (MvPolynomial.X i) = f (gs i)`. Rewrite using `[hAX]`. Conclude with `hπt i`.

Take `⟨P, hP⟩` from `x.prop`. Establish `e : x = ⟨A P, P, rfl⟩` using `Subtype.ext hP.symm`. Rewrite using `[e]`. Conclude with `key P`. Use `⟨↥S, inferInstance, inferInstance, φ, ?_, ?_, ?_, ?_, ?_, ?_, hind⟩` and prove the remaining obligations.

Establish `: Algebra.FiniteType R (MvPolynomial (Fin k) B)` using `Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R B) inferInstance`. Conclude with `Algebra.FiniteType.of_surjective A.rangeRestrict A.rangeRestrict_surjective`. Use `infer_instance`. Introduce `a b h`. Conclude with `hf (congrArg Subtype.val h)`.

Introduce `b'`. Use `hind (fun b' => ∃ n b, algebraMap R S π ^ n * b' = φ b) (fun b => ⟨0, b, by simp⟩) (fun g _ b' h => ⟨1, g, by simpa using h⟩) ?_ ?_ b'` and prove the remaining obligations. Introduce and unpack `x y ⟨n, b, hb⟩ ⟨m, c, hc⟩`. Use `⟨n + m, algebraMap R B π ^ m * b + algebraMap R B π ^ n * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, ← hb, ← hc]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `x y ⟨n, b, hb⟩ ⟨m, c, hc⟩`. Use `⟨n + m, b * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hb, ← hc]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x hx`. Conclude with `(Module.isTorsionFree_iff_smul_eq_zero.mp htfS π x (by rw [Algebra.smul_def]; exact hx)).resolve_left hπ.ne_zero`. Introduce `g hg`. Rewrite `hg` using `[← hgs]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun B).mp hg`.

Use `⟨⟨A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i), _, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show algebraMap R L π * A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) = f g`. Rewrite using `[← hc, map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hAC, hAX, smul_eq_mul, map_mul, ← hπt i]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R)
    (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Module.Flat R B] (I : Ideal B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'),
      Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧
      (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧
      (∀ x : B', algebraMap R B' π * x = 0 → x = 0) ∧
      (∀ g ∈ I, ∃ b' : B', algebraMap R B' π * b' = φ g) ∧
      ∀ Q : B' → Prop, (∀ b, Q (φ b)) →
        (∀ g ∈ I, ∀ b' : B', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x := by
  classical

  let K := FractionRing R
  let L := TensorProduct R B K
  let f : B →ₐ[R] L := Algebra.TensorProduct.includeLeft
  let iR : K →ₐ[R] L := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)
  have hfa : ∀ b, algebraMap B L b = f b := fun b => rfl
  have hK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  let u : L := iR (algebraMap R K π)⁻¹
  have hcu : algebraMap R L π * u = 1 := by
    rw [← iR.commutes π, ← map_mul, mul_inv_cancel₀ hK, map_one]

  have htfL : Module.IsTorsionFree R L := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
    calc x = iR ((algebraMap R K r)⁻¹ * algebraMap R K r) * x := by
          rw [inv_mul_cancel₀ hrK, map_one, one_mul]
      _ = iR (algebraMap R K r)⁻¹ * (r • x) := by
          rw [map_mul, iR.commutes, Algebra.smul_def, mul_assoc]
      _ = 0 := by rw [hrx, mul_zero]

  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  obtain ⟨k, gs, hgs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  let t : Fin k → L := fun i => u * f (gs i)
  have hπt : ∀ i, algebraMap R L π * t i = f (gs i) := fun i => by
    simp only [t]
    rw [← mul_assoc, hcu, one_mul]

  let A : MvPolynomial (Fin k) B →ₐ[R] L := (MvPolynomial.aeval t).restrictScalars R
  let S : Subalgebra R L := A.range
  have hAC : ∀ b, A (MvPolynomial.C b) = f b := fun b => by simp [A, hfa]
  have hAX : ∀ i, A (MvPolynomial.X i) = t i := fun i => by simp [A]
  have hmemf : ∀ b, f b ∈ S := fun b => ⟨MvPolynomial.C b, hAC b⟩
  let φ : B →ₐ[R] S := f.codRestrict S hmemf
  have htfS : Module.IsTorsionFree R S :=
    Function.Injective.moduleIsTorsionFree (fun x : S => (x : L)) Subtype.val_injective (fun r x => rfl)
  have hind : ∀ Q : S → Prop, (∀ b, Q (φ b)) →
      (∀ g ∈ I, ∀ b' : S, algebraMap R S π * b' = φ g → Q b') →
      (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x := by
    intro Q hB hI hadd hmul x
    have key : ∀ P, Q ⟨A P, P, rfl⟩ := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C b =>
        have e : (⟨A (MvPolynomial.C b), _, rfl⟩ : S) = φ b := Subtype.ext (hAC b)
        rw [e]
        exact hB b
      | add p q hp hq =>
        have e : (⟨A (p + q), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ + ⟨A q, q, rfl⟩ := Subtype.ext (map_add A p q)
        rw [e]
        exact hadd _ _ hp hq
      | mul_X p i hp =>
        have e : (⟨A (p * MvPolynomial.X i), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ * ⟨A (MvPolynomial.X i), _, rfl⟩ :=
          Subtype.ext (map_mul A _ _)
        rw [e]
        refine hmul _ _ hp (hI (gs i) (by rw [← hgs]; exact Submodule.subset_span ⟨i, rfl⟩) _ ?_)
        apply Subtype.ext
        show algebraMap R L π * A (MvPolynomial.X i) = f (gs i)
        rw [hAX]
        exact hπt i
    obtain ⟨P, hP⟩ := x.prop
    have e : x = ⟨A P, P, rfl⟩ := Subtype.ext hP.symm
    rw [e]
    exact key P
  refine ⟨↥S, inferInstance, inferInstance, φ, ?_, ?_, ?_, ?_, ?_, ?_, hind⟩
  · have : Algebra.FiniteType R (MvPolynomial (Fin k) B) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R B) inferInstance
    exact Algebra.FiniteType.of_surjective A.rangeRestrict A.rangeRestrict_surjective
  · infer_instance
  · intro a b h
    exact hf (congrArg Subtype.val h)
  · intro b'
    refine hind (fun b' => ∃ n b, algebraMap R S π ^ n * b' = φ b) (fun b => ⟨0, b, by simp⟩)
      (fun g _ b' h => ⟨1, g, by simpa using h⟩) ?_ ?_ b'
    · rintro x y ⟨n, b, hb⟩ ⟨m, c, hc⟩
      refine ⟨n + m, algebraMap R B π ^ m * b + algebraMap R B π ^ n * c, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, ← hb, ← hc]
      ring
    · rintro x y ⟨n, b, hb⟩ ⟨m, c, hc⟩
      refine ⟨n + m, b * c, ?_⟩
      rw [map_mul, ← hb, ← hc]
      ring
  · intro x hx
    exact (Module.isTorsionFree_iff_smul_eq_zero.mp htfS π x (by rw [Algebra.smul_def]; exact hx)).resolve_left
      hπ.ne_zero
  · intro g hg
    rw [← hgs] at hg
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hg
    refine ⟨⟨A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i), _, rfl⟩, Subtype.ext ?_⟩
    show algebraMap R L π * A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) = f g
    rw [← hc, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hAC, hAX, smul_eq_mul, map_mul, ← hπt i]
    ring

end GlobalTheory.FiniteFieldCountEstimate
