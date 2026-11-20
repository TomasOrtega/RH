import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Ge

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

noncomputable def qL (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qL_apply (σ : E →+* K) (x : Fin N → A) : qL D σ x = D.q σ x := rfl

/- English proof (translation)
Take `⟨hcol1, hcol2⟩` from `hg`. Use `choose x'' hx'' using hcol1`. Use `choose yM hyM hq using hcol2`. Establish `hx1 : ∃ y₁ ∈ D.omHT σ, D.q σ (x - ∑ a, t a • (fun l => g l (Sum.inr a))) = ((p : A) ^ m) • y₁`. Use `⟨y - ∑ a, t a • yM a, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.sub_mem _ hy (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hyM a))`. Rewrite using `[← qL_apply, map_sub, map_sum]`. Simplify using `only [map_smul, qL_apply, hq, e, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]`. Simplify using `only [smul_comm (t _) ((p : A) ^ m)]`. Normalize the expressions using the abelian group laws.

Take `⟨w, x', hw⟩` from `(hex.2.1 _).1 hx1`. Use `⟨bW.repr w, x' - ∑ b, bW.repr w b • x'' b, ?_⟩` and prove the remaining obligations. Establish `hiw : i w = ∑ b, bW.repr w b • i (bW b)` using `by conv_lhs => rw [← bW.sum_repr w]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`.

Establish `hcolL : ∀ b, i (bW b) = (fun l => g l (Sum.inl b)) - ((p : A) ^ m) • x'' b` using `fun b => by`. Rewrite using `[hx'' b]`. Normalize the expressions using the abelian group laws. Establish `hx : x = ∑ a, t a • (fun l => g l (Sum.inr a)) + i w + ((p : A) ^ m) • x'`. Rewrite using `[add_assoc, ← hw]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hx, hiw]`. Simplify using `only [hcolL]`. Use extensionality with `l`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]`.

Put the polynomial expressions in normal form. Establish `s1 : ∑ x, g l (Sum.inl x) * (bW.repr w) x = ∑ x, (bW.repr w) x * g l (Sum.inl x)` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `s2 : ∑ x, g l (Sum.inr x) * t x = ∑ x, t x * g l (Sum.inr x)` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `s3 : ∑ x, (p : A) ^ m * (bW.repr w) x * x'' x l = ∑ x, (bW.repr w) x * (p : A) ^ m * x'' x l` using `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[s1, s2, s3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem frame_expand {σ : E →+* K} {m j k : ℕ}
    {i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) A (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) A} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → A) (t : Fin k → A) (y : Ω) (hy : y ∈ D.omHT σ)
    (e : D.q σ x = ∑ a, t a • (bM a : Ω) + ((p : A) ^ m) • y) :
    ∃ (s : Fin j → A) (z : Fin N → A), x = g.mulVec (Sum.elim s t) + ((p : A) ^ m) • z := by
  obtain ⟨hcol1, hcol2⟩ := hg
  choose x'' hx'' using hcol1
  choose yM hyM hq using hcol2
  have hx1 : ∃ y₁ ∈ D.omHT σ, D.q σ (x - ∑ a, t a • (fun l => g l (Sum.inr a))) = ((p : A) ^ m) • y₁ := by
    refine ⟨y - ∑ a, t a • yM a, ?_, ?_⟩
    · exact Submodule.sub_mem _ hy (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hyM a))
    · rw [← qL_apply, map_sub, map_sum]
      simp only [map_smul, qL_apply, hq, e, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
      simp only [smul_comm (t _) ((p : A) ^ m)]
      abel
  obtain ⟨w, x', hw⟩ := (hex.2.1 _).1 hx1
  refine ⟨bW.repr w, x' - ∑ b, bW.repr w b • x'' b, ?_⟩
  have hiw : i w = ∑ b, bW.repr w b • i (bW b) := by
    conv_lhs => rw [← bW.sum_repr w]
    rw [map_sum]
    simp only [map_smul]
  have hcolL : ∀ b, i (bW b) = (fun l => g l (Sum.inl b)) - ((p : A) ^ m) • x'' b := fun b => by
    rw [hx'' b]
    abel
  have hx : x = ∑ a, t a • (fun l => g l (Sum.inr a)) + i w + ((p : A) ^ m) • x' := by
    rw [add_assoc, ← hw]
    abel
  rw [hx, hiw]
  simp only [hcolL]
  ext l
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  ring_nf
  have s1 : ∑ x, g l (Sum.inl x) * (bW.repr w) x = ∑ x, (bW.repr w) x * g l (Sum.inl x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s2 : ∑ x, g l (Sum.inr x) * t x = ∑ x, t x * g l (Sum.inr x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s3 : ∑ x, (p : A) ^ m * (bW.repr w) x * x'' x l = ∑ x, (bW.repr w) x * (p : A) ^ m * x'' x l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2, s3]
  ring

end

/- English proof (translation)
Introduce `A K _ _ _ _ _ E _ _ c _ p R N _ Ω _ _ _ _ D σ m j k i bW bM eqv hqM hex`. Use `⟨?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h3 : ∀ a : Fin k, ∃ x : Fin N → A, ∃ y ∈ D.omHT σ, D.q σ x = (bM a : Ω) + ((p : A) ^ m) • y`. Introduce `a`. Take `⟨x, y', hy', he⟩` from `hex.2.2 (bM a) (bM a).2`.

Use `⟨x, -y', Submodule.neg_mem _ hy', ?_⟩` and prove the remaining obligations. Rewrite using `[he, smul_neg]`. Normalize the expressions using the abelian group laws. Use `choose xs ys hys hxs using h3`. Use `⟨Matrix.of fun l c => Sum.elim (fun a => i (bW a) l) (fun a => xs a l) c, fun a => ⟨0, ?_⟩, fun a => ⟨ys a, hys a, ?_⟩⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules. Simplify using `using hxs a`. Establish `hsurj : ∀ x : Fin N → A, ∃ v : Fin j ⊕ Fin k → A, ∃ z : Fin N → A, x = g.mulVec v + ((p : A) ^ m) • z`. Introduce `x`.

Take `⟨s, z, hz⟩` from `frame_expand D hex hg x (bM.repr ⟨D.q σ x, hqM x⟩) 0 (Submodule.zero_mem _) (by`. Rewrite using `[smul_zero, add_zero]`. Establish `h5` using `congrArg Subtype.val (bM.sum_repr ⟨D.q σ x, hqM x⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h5`. Conclude with `h5.symm)`.

Conclude with `⟨_, z, hz⟩`. Use `choose v z hvz using fun l : Fin N => hsurj (Pi.single l 1)`. Establish `hprod : g.submatrix id eqv.symm * Matrix.of (fun c l => v l (eqv.symm c)) = 1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l)`. Use extensionality with `l l'`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.submatrix_apply, id, Matrix.of_apply]`. Establish `e1 : ∑ c, g l (eqv.symm c) * v l' (eqv.symm c) = (g.mulVec (v l')) l`. Rewrite using `[Matrix.mulVec, dotProduct]`. Conclude with `Equiv.sum_comp eqv.symm (fun d => g l d * v l' d)`. Rewrite using `[e1, eq_sub_of_add_eq (hvz l').symm]`.

Simplify using `[Matrix.one_apply, Pi.single_apply]`. Establish `hmem : (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A).det - 1 ∈ Ideal.span {((p : A) ^ m)}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]`. Establish `e2 : (Ideal.Quotient.mk (Ideal.span {((p : A) ^ m)})).mapMatrix (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A) = 1`. Use extensionality with `a b`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, sub_zero, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e2, Matrix.det_one]`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hmem`. Use `⟨(Matrix.of (fun c l => v l (eqv.symm c)) : Matrix (Fin N) (Fin N) A).det, r, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.det_mul, hprod]`. Take the linear combination `(-1 : A) * hr`.
-/
theorem frame_exists : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (m j k : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))) (bM : Basis (Fin k) A (D.omHT σ)) (eqv : Fin j ⊕ Fin k ≃ Fin N), (∀ x, D.q σ x ∈ D.omHT σ) → D.ExactMod σ m i → (∃ g, D.IsFrame σ m i bW bM g) ∧ ∀ g, D.IsFrame σ m i bW bM g → ∃ h r : A, (g.submatrix id eqv.symm).det * h = 1 + (p : A) ^ m * r := by
  intro A K _ _ _ _ _ E _ _ c _ p R N _ Ω _ _ _ _ D σ m j k i bW bM eqv hqM hex
  refine ⟨?_, fun g hg => ?_⟩
  · have h3 : ∀ a : Fin k, ∃ x : Fin N → A, ∃ y ∈ D.omHT σ, D.q σ x = (bM a : Ω) + ((p : A) ^ m) • y := by
      intro a
      obtain ⟨x, y', hy', he⟩ := hex.2.2 (bM a) (bM a).2
      refine ⟨x, -y', Submodule.neg_mem _ hy', ?_⟩
      rw [he, smul_neg]
      abel
    choose xs ys hys hxs using h3
    refine ⟨Matrix.of fun l c => Sum.elim (fun a => i (bW a) l) (fun a => xs a l) c, fun a => ⟨0, ?_⟩,
      fun a => ⟨ys a, hys a, ?_⟩⟩
    · funext l
      simp
    · simpa using hxs a
  · have hsurj : ∀ x : Fin N → A, ∃ v : Fin j ⊕ Fin k → A, ∃ z : Fin N → A,
        x = g.mulVec v + ((p : A) ^ m) • z := by
      intro x
      obtain ⟨s, z, hz⟩ := frame_expand D hex hg x (bM.repr ⟨D.q σ x, hqM x⟩) 0 (Submodule.zero_mem _) (by
        rw [smul_zero, add_zero]
        have h5 := congrArg Subtype.val (bM.sum_repr ⟨D.q σ x, hqM x⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h5
        exact h5.symm)
      exact ⟨_, z, hz⟩
    choose v z hvz using fun l : Fin N => hsurj (Pi.single l 1)
    have hprod : g.submatrix id eqv.symm * Matrix.of (fun c l => v l (eqv.symm c)) =
        1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) := by
      ext l l'
      rw [Matrix.mul_apply]
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply]
      have e1 : ∑ c, g l (eqv.symm c) * v l' (eqv.symm c) = (g.mulVec (v l')) l := by
        rw [Matrix.mulVec, dotProduct]
        exact Equiv.sum_comp eqv.symm (fun d => g l d * v l' d)
      rw [e1, eq_sub_of_add_eq (hvz l').symm]
      simp [Matrix.one_apply, Pi.single_apply]
    have hmem : (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A).det - 1 ∈
        Ideal.span {((p : A) ^ m)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
      have e2 : (Ideal.Quotient.mk (Ideal.span {((p : A) ^ m)})).mapMatrix
          (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A) = 1 := by
        ext a b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
          map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, sub_zero,
          Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, Matrix.det_one]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨(Matrix.of (fun c l => v l (eqv.symm c)) : Matrix (Fin N) (Fin N) A).det, r, ?_⟩
    rw [← Matrix.det_mul, hprod]
    linear_combination (-1 : A) * hr

end PositivityTheory.HtPt.Ge
