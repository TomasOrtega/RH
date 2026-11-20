import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SatSplit

noncomputable section

namespace PI.LocMassTypW.WSatP

open Matrix

/- English proof (translation)
Establish `hk : LinearMap.ker (Matrix.toLin' A) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `t ht`. Conclude with `h t (by simpa [Matrix.toLin'_apply] using ht)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hk`.

Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`.
-/
theorem leftInv_field {K : Type*} [Field K] {n m : ℕ} (A : Matrix (Fin n) (Fin m) K)
    (h : ∀ t, A *ᵥ t = 0 → t = 0) : ∃ L : Matrix (Fin m) (Fin n) K, L * A = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    exact h t (by simpa [Matrix.toLin'_apply] using ht)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

/- English proof (translation)
Take `⟨Lb, hLb⟩` from `h`. Set `L0 : Matrix (Fin m) (Fin n) O` to `Matrix.of fun i j => Classical.choose (IsLocalRing.residue_surjective (Lb i j))`. Establish `hL0 : L0.map (IsLocalRing.residue O) = Lb` using `Matrix.ext fun i j => Classical.choose_spec (IsLocalRing.residue_surjective (Lb i j))`. Establish `hdet : IsUnit (L0 * A).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, hL0, hLb, Matrix.det_one]`.

Conclude with `one_ne_zero`. Use `⟨(L0 * A)⁻¹ * L0, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]`.
-/
theorem leftInv_lift {O : Type*} [CommRing O] [IsLocalRing O] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) O)
    (h : ∃ L : Matrix (Fin m) (Fin n) (IsLocalRing.ResidueField O),
      L * A.map (IsLocalRing.residue O) = 1) :
    ∃ L : Matrix (Fin m) (Fin n) O, L * A = 1 := by
  obtain ⟨Lb, hLb⟩ := h
  let L0 : Matrix (Fin m) (Fin n) O :=
    Matrix.of fun i j => Classical.choose (IsLocalRing.residue_surjective (Lb i j))
  have hL0 : L0.map (IsLocalRing.residue O) = Lb :=
    Matrix.ext fun i j => Classical.choose_spec (IsLocalRing.residue_surjective (Lb i j))
  have hdet : IsUnit (L0 * A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_mul, hL0, hLb, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(L0 * A)⁻¹ * L0, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

end PI.LocMassTypW.WSatP

namespace PI.LocMassTypW

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/- English proof (translation)
Introduce `F _ _ v n m A hsat`. Apply `WSatP.leftInv_lift` to reduce the goal to its premises. Apply `WSatP.leftInv_field` to reduce the goal to its premises. Introduce `tb htb`. Assume the negation of the conclusion as `hne`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, tb j ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Conclude with `hne (funext fun k => not_not.mp fun h' => hall ⟨k, h'⟩)`. Set `t : Fin m → v.adicCompletionIntegers F` to `fun j => Classical.choose (IsLocalRing.residue_surjective (tb j))`. Establish `ht : ∀ j, IsLocalRing.residue _ (t j) = tb j` using `fun j => Classical.choose_spec (IsLocalRing.residue_surjective (tb j))`.

Establish `htj : IsUnit (t j)` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [ht]; exact hj)`. Establish `hAt : ∀ i, (A *ᵥ t) i ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Introduce `i`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, RingHom.map_mulVec]`. Establish `: (IsLocalRing.residue _ ∘ t) = tb` using `funext ht`.

Rewrite using `[this, htb]`. Both sides reduce to the same expression. Take `⟨x, hx⟩` from `IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)`. Set `I : Ideal (v.adicCompletionIntegers F)` to `Ideal.span (insert x (Set.range (A *ᵥ t)))`. Take `⟨c, hc⟩` from `(IsPrincipalIdealRing.principal I).principal`.

Establish `hmemI : ∀ y ∈ insert x (Set.range (A *ᵥ t)), ∃ q, q * c = y`. Introduce `y hy`. Establish `: y ∈ I` using `Ideal.subset_span hy`. Rewrite `this` using `[hc]`. Conclude with `Ideal.mem_span_singleton'.mp this`.

Establish `hcm : c ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Establish `: c ∈ I` using `by rw [hc]; exact Submodule.mem_span_singleton_self c`. Use `(Ideal.span_le.mpr ?_) this` and prove the remaining obligations. Introduce and unpack `_ (rfl | ⟨i, rfl⟩)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr hx.not_isUnit`.

Conclude with `hAt i`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Take `⟨q, hq⟩` from `hmemI x (Set.mem_insert _ _)`. Rewrite `hq` using `[mul_zero]`.

Conclude with `hx.ne_zero hq.symm`. Establish `hcK : (c : v.adicCompletion F) ≠ 0`. Introduce `h0`. Conclude with `hc0 (Subtype.ext h0)`. Set `f` to `(v.adicCompletionIntegers F).subtype`.

Set `t' : Fin m → v.adicCompletion F` to `(c : v.adicCompletion F)⁻¹ • (f ∘ t)`. Establish `hint : ∀ i, (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i ∈ v.adicCompletionIntegers F`. Introduce `i`. Take `⟨q, hq⟩` from `hmemI ((A *ᵥ t) i) (Set.mem_insert_of_mem _ ⟨i, rfl⟩)`. Establish `e1 : (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i = (c : v.adicCompletion F)⁻¹ * f ((A *ᵥ t) i)`.

Rewrite using `[Matrix.mulVec_smul, RingHom.map_mulVec]`. Both sides reduce to the same expression. Rewrite using `[e1, ← hq, map_mul]`. Establish `e2 : (c : v.adicCompletion F)⁻¹ * (f q * f c) = f q`. Express the relevant statement in the definitionally equal form `(c : v.adicCompletion F)⁻¹ * (f q * (c : v.adicCompletion F)) = f q`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`. Conclude with `q.2`. Establish `hj'` using `hsat t' hint j`. Establish `e3 : t' j = (c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F)` using `rfl`.

Rewrite `hj'` using `[e3]`. Use `set s : v.adicCompletionIntegers F := ⟨_, hj'⟩ with hs`. Establish `hts : t j = c * s`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(t j : v.adicCompletion F) = (c : v.adicCompletion F) * ((c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F))`.

Clear the denominators using the available nonvanishing facts. Establish `: t j ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Rewrite using `[hts]`. Conclude with `Ideal.mul_mem_right _ _ hcm`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp this) htj`.
-/
theorem saturated_split_lattice : SatSplit := by
  intro F _ _ v n m A hsat
  apply WSatP.leftInv_lift
  apply WSatP.leftInv_field
  intro tb htb
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, tb j ≠ 0 := by
    by_contra hall
    exact hne (funext fun k => not_not.mp fun h' => hall ⟨k, h'⟩)
  let t : Fin m → v.adicCompletionIntegers F := fun j =>
    Classical.choose (IsLocalRing.residue_surjective (tb j))
  have ht : ∀ j, IsLocalRing.residue _ (t j) = tb j := fun j =>
    Classical.choose_spec (IsLocalRing.residue_surjective (tb j))
  have htj : IsUnit (t j) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [ht]; exact hj)
  have hAt : ∀ i, (A *ᵥ t) i ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro i
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_mulVec]
    have : (IsLocalRing.residue _ ∘ t) = tb := funext ht
    rw [this, htb]
    rfl
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  let I : Ideal (v.adicCompletionIntegers F) := Ideal.span (insert x (Set.range (A *ᵥ t)))
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ y ∈ insert x (Set.range (A *ᵥ t)), ∃ q, q * c = y := by
    intro y hy
    have : y ∈ I := Ideal.subset_span hy
    rw [hc] at this
    exact Ideal.mem_span_singleton'.mp this
  have hcm : c ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
    refine (Ideal.span_le.mpr ?_) this
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact (IsLocalRing.mem_maximalIdeal _).mpr hx.not_isUnit
    · exact hAt i
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hmemI x (Set.mem_insert _ _)
    rw [mul_zero] at hq
    exact hx.ne_zero hq.symm
  have hcK : (c : v.adicCompletion F) ≠ 0 := by
    intro h0; exact hc0 (Subtype.ext h0)
  let f := (v.adicCompletionIntegers F).subtype
  let t' : Fin m → v.adicCompletion F := (c : v.adicCompletion F)⁻¹ • (f ∘ t)
  have hint : ∀ i, (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i ∈
      v.adicCompletionIntegers F := by
    intro i
    obtain ⟨q, hq⟩ := hmemI ((A *ᵥ t) i) (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    have e1 : (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i =
        (c : v.adicCompletion F)⁻¹ * f ((A *ᵥ t) i) := by
      rw [Matrix.mulVec_smul, RingHom.map_mulVec]
      rfl
    rw [e1, ← hq, map_mul]
    have e2 : (c : v.adicCompletion F)⁻¹ * (f q * f c) = f q := by
      change (c : v.adicCompletion F)⁻¹ * (f q * (c : v.adicCompletion F)) = f q
      field_simp
    rw [e2]
    exact q.2
  have hj' := hsat t' hint j
  have e3 : t' j = (c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F) := rfl
  rw [e3] at hj'
  set s : v.adicCompletionIntegers F := ⟨_, hj'⟩ with hs
  have hts : t j = c * s := by
    apply Subtype.ext
    change (t j : v.adicCompletion F) = (c : v.adicCompletion F) * ((c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F))
    field_simp
  have : t j ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [hts]; exact Ideal.mul_mem_right _ _ hcm
  exact ((IsLocalRing.mem_maximalIdeal _).mp this) htj

end PI.LocMassTypW
