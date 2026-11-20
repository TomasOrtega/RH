import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

open UpperTheory.V.Z.Sym MulAction in
/- English proof (translation)
Introduce `T G _ _ ι C θ U f δ hf hδ J S x hx hs`. Use `letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι`. Establish `sm : ∀ (t : T) (g : G), t • (g : G ⧸ U) = ((ι t * g : G) : G ⧸ U)` using `fun _ _ => rfl`. Establish `k1 : ∀ (t : T) (g : G), ∀ u ∈ U, f ((ι t * g * u)⁻¹ * δ * θ (ι t * g * u)) = f (g⁻¹ * δ * θ g)` using `fun t g u hu => by`. Rewrite using `[← hf u hu (g⁻¹ * δ * θ g)]`.

Use `congr 1`. Use `conv_rhs => rw [← hδ t]`. Simplify using `[mul_assoc]`. Establish `st : ∀ (t : T) (y : G ⧸ U), stabilizer T (t • y) = stabilizer T y` using `fun t y => by`. Use extensionality with `a`.

Simplify using `only [mem_stabilizer_iff]`. Rewrite using `[smul_smul, mul_comm, mul_smul, smul_left_cancel_iff]`. Set `q : J → orbitRel.Quotient T (G ⧸ U)` to `fun i => Quotient.mk'' (x i : G ⧸ U)`. Establish `rel : ∀ (o : orbitRel.Quotient T (G ⧸ U)) (i : J), o = q i ↔ ∃ t, ∃ u ∈ U, o.out.out = ι t * x i * u` using `fun o i => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `: orbitRel T _ o.out (x i : G ⧸ U)` using `Quotient.exact (by rw [Quotient.out_eq]; exact h)`. Take `⟨t, ht⟩` from `this`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul U (ι t * x i)`. Conclude with `⟨t, u, u.2, by rw [← hu, ← sm]; exact congrArg _ ht.symm⟩`.

Introduce and unpack `⟨t, u, hu, h⟩`. Rewrite using `[← o.out_eq]`. Use `Quotient.sound ⟨t, ?_⟩` and prove the remaining obligations. Use `show t • _ = _`. Rewrite using `[sm, ← o.out.out_eq', h]`.

Conclude with `(QuotientGroup.mk_mul_of_mem _ hu).symm`. Unfold `orb wcount`. Rewrite using `[finsum_eq_sum_of_support_subset (s := S.image q) _ fun o ho => ?_, Finset.sum_image fun i hi j hj h => ?_]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨t, u, hu, h⟩` from `(rel (q i) i).1 rfl`.

Establish `e : (q i).out = t • (x i : G ⧸ U)`. Rewrite using `[sm, ← (q i).out.out_eq', h]`. Conclude with `QuotientGroup.mk_mul_of_mem _ hu`. Use `beta_reduce`. Rewrite using `[h, k1 t _ u hu, e, st]`.

Both sides reduce to the same expression. Take `⟨t, u, hu, h1⟩` from `(rel (q i) i).1 rfl`. Take `⟨t', u', hu', h2⟩` from `(rel (q i) j).1 h`. Use `hx i hi j hj (t'⁻¹ * t) (u * u'⁻¹) (mul_mem hu (inv_mem hu')) ?_` and prove the remaining obligations. Use `h1.symm.trans h2` as an intermediate fact.

Rewrite using `[map_mul, map_inv, mul_assoc (ι t')⁻¹, mul_assoc (ι t')⁻¹, ← mul_assoc _ u, this]`. Simplify using `[mul_assoc]`. Take `⟨t, i, hi, u, hu, h⟩` from `hs o.out.out (right_ne_zero_of_mul ho)`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, hi, ((rel o i).2 ⟨t, u, hu, h⟩).symm⟩)`.
-/
theorem UpperTheory.V.Z.Sym.Tf.orbReps :
    UpperTheory.V.Z.Sym.Tf.OrbReps := by
  classical
  intro T G _ _ ι C θ U f δ hf hδ J S x hx hs
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  have sm : ∀ (t : T) (g : G), t • (g : G ⧸ U) = ((ι t * g : G) : G ⧸ U) := fun _ _ => rfl
  have k1 : ∀ (t : T) (g : G), ∀ u ∈ U, f ((ι t * g * u)⁻¹ * δ * θ (ι t * g * u)) = f (g⁻¹ * δ * θ g) := fun t g u hu => by
    rw [← hf u hu (g⁻¹ * δ * θ g)]
    congr 1
    conv_rhs => rw [← hδ t]
    simp [mul_assoc]
  have st : ∀ (t : T) (y : G ⧸ U), stabilizer T (t • y) = stabilizer T y := fun t y => by
    ext a
    simp only [mem_stabilizer_iff]
    rw [smul_smul, mul_comm, mul_smul, smul_left_cancel_iff]
  let q : J → orbitRel.Quotient T (G ⧸ U) := fun i => Quotient.mk'' (x i : G ⧸ U)
  have rel : ∀ (o : orbitRel.Quotient T (G ⧸ U)) (i : J), o = q i ↔ ∃ t, ∃ u ∈ U, o.out.out = ι t * x i * u := fun o i => by
    constructor
    · intro h
      have : orbitRel T _ o.out (x i : G ⧸ U) := Quotient.exact (by rw [Quotient.out_eq]; exact h)
      obtain ⟨t, ht⟩ := this
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (ι t * x i)
      exact ⟨t, u, u.2, by rw [← hu, ← sm]; exact congrArg _ ht.symm⟩
    · rintro ⟨t, u, hu, h⟩
      rw [← o.out_eq]
      refine Quotient.sound ⟨t, ?_⟩
      show t • _ = _
      rw [sm, ← o.out.out_eq', h]
      exact (QuotientGroup.mk_mul_of_mem _ hu).symm
  unfold orb wcount
  rw [finsum_eq_sum_of_support_subset (s := S.image q) _ fun o ho => ?_, Finset.sum_image fun i hi j hj h => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨t, u, hu, h⟩ := (rel (q i) i).1 rfl
    have e : (q i).out = t • (x i : G ⧸ U) := by
      rw [sm, ← (q i).out.out_eq', h]; exact QuotientGroup.mk_mul_of_mem _ hu
    beta_reduce
    rw [h, k1 t _ u hu, e, st]
    rfl
  · obtain ⟨t, u, hu, h1⟩ := (rel (q i) i).1 rfl
    obtain ⟨t', u', hu', h2⟩ := (rel (q i) j).1 h
    refine hx i hi j hj (t'⁻¹ * t) (u * u'⁻¹) (mul_mem hu (inv_mem hu')) ?_
    have := h1.symm.trans h2
    rw [map_mul, map_inv, mul_assoc (ι t')⁻¹, mul_assoc (ι t')⁻¹, ← mul_assoc _ u, this]
    simp [mul_assoc]
  · obtain ⟨t, i, hi, u, hu, h⟩ := hs o.out.out (right_ne_zero_of_mul ho)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, hi, ((rel o i).2 ⟨t, u, hu, h⟩).symm⟩)
