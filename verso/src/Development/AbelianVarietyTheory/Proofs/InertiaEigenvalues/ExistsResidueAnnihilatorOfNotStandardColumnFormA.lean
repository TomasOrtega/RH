import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Use `set V := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hV`. Set `A : Set (Fin r → IsLocalRing.ResidueField O)` to `{v | ∃ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ V ∧ (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) ∧ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = v}`. Establish `hA0 : (0 : Fin r → IsLocalRing.ResidueField O) ∈ A` using `⟨0, by convert V.zero_mem using 1; ext; simp, by simp, by ext; simp⟩`. Establish `hAadd : ∀ v w, v ∈ A → w ∈ A → v + w ∈ A`. Introduce and unpack `v w ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩`.

Use `⟨u + u', ?_, ?_, ?_⟩` and prove the remaining obligations. Use `V.add_mem hu hu'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using the standard rewrite rules.

Introduce `i`. Simplify using `[hu0 i, hu0' i]`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hAsmul : ∀ (c : IsLocalRing.ResidueField O) v, v ∈ A → c • v ∈ A`.

Introduce and unpack `c v ⟨u, hu, hu0, rfl⟩`. Take `⟨c', rfl⟩` from `IsLocalRing.residue_surjective c`. Use `⟨c' • u, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `V.smul_mem (algebraMap O K c') hu` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Simplify using the standard rewrite rules. Introduce `i`. Simplify using `[hu0 i]`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Establish `hspan : ∀ v ∈ Submodule.span (IsLocalRing.ResidueField O) A, v ∈ A`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`.

Consider the case `zero => exact hA0`. Consider the case `add y w _ _ hy hw => exact hAadd y w hy hw`. Consider the case `smul c y _ hy => exact hAsmul c y hy`. Distinguish the cases in `htop : Submodule.span (IsLocalRing.ResidueField O) A = ⊤`. It suffices to derive a contradiction.

Apply `hx` to reduce the goal to its premises. Establish `hmem : ∀ i : Fin r, (Pi.single i 1 : Fin r → IsLocalRing.ResidueField O) ∈ A` using `fun i => hspan _ (htop ▸ Submodule.mem_top)`. Use `choose u hu hu0 hu1 using hmem`. Set `B : Matrix (Fin r ⊕ Fin t) (Fin r) O` to `fun p j => u j p`. Set `T : Matrix (Fin r) (Fin r) O` to `fun i j => u j (Sum.inl i)`.

Establish `hT : IsUnit T.det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Establish `: (IsLocalRing.residue O).mapMatrix T = 1`. Use extensionality with `i j`. Use `congrFun (hu1 j) i` as an intermediate fact.

Use `show IsLocalRing.residue O (u j (Sum.inl i)) = _`. Rewrite using `[this]`. Simplify using `[Pi.single_apply, Matrix.one_apply]`. Rewrite using `[this, Matrix.det_one]`. Conclude with `one_ne_zero`.

Establish `hmax` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Establish `hdiv : ∀ (i : Fin t) (j : Fin r), ∃ c, u j (Sum.inr i) = ϖ * c`. Introduce `i j`. Establish `: u j (Sum.inr i) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.residue_eq_zero_iff _).1 (hu0 j i)`. Rewrite `this` using `[hmax, Ideal.mem_span_singleton]`.

Conclude with `this`. Use `choose C hC using hdiv`. Establish `hcol : ∀ j, ∃ c : Fin r → K, ∑ l, c l • (fun i => algebraMap O K (x i l)) = fun i => algebraMap O K (u j i)` using `fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu j)`. Use `choose d hd using hcol`. Set `D : Matrix (Fin r) (Fin r) K` to `fun l j => d j l`.

Establish `hBD : x.map (algebraMap O K) * D = B.map (algebraMap O K)`. Use extensionality with `p j`. Use `congrFun (hd j) p` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[Matrix.mul_apply, Matrix.map_apply]`.

Use `show _ = algebraMap O K (u j p)`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `hTD : (x.submatrix Sum.inl id).map (algebraMap O K) * D = T.map (algebraMap O K)`. Use extensionality with `i j`.

Use `congrFun₂ hBD (Sum.inl i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`. Establish `hdetT : (T.map (algebraMap O K)).det = algebraMap O K T.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hTK : IsUnit (T.map (algebraMap O K)).det`. Rewrite using `[hdetT]`. Conclude with `hT.map _`. Establish `hDu : IsUnit D.det`. Rewrite `hTK` using `[← hTD, Matrix.det_mul]`.

Conclude with `isUnit_of_mul_isUnit_right hTK`. Establish `hdetTi : ((T⁻¹).map (algebraMap O K)).det = algebraMap O K (T⁻¹).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `hg : IsUnit (D * (T⁻¹).map (algebraMap O K))`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hdetTi]`. Conclude with `hDu.mul ((Matrix.isUnit_nonsing_inv_det T hT).map _)`. Use `⟨hg.unit, Matrix.fromRows 0 (Matrix.of fun i j => ∑ l, C i l * T⁻¹ l j), ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, ← Matrix.mul_assoc, hBD, ← Matrix.map_mul]`. Use `congr 1`.

Use extensionality with `p j`. Break down `p with i | i` into its components or cases. Rewrite using `[Matrix.mul_apply]`. Use `congrFun₂ (Matrix.mul_nonsing_inv T hT) i j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`.

Simplify `this` using `[B, T]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[B, hC, Finset.mul_sum, mul_assoc]`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 htop)`. Establish `hf : ∀ v, f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v`.

Introduce `v`. Use `conv_lhs => rw [pi_eq_sum_univ v]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Use `congr 2`. Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`. Use `⟨fun i => f (Pi.single i 1), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hf0` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[LinearMap.zero_apply, hf v, h0, zero_dotProduct]`. Introduce `u hu hu0`.

Rewrite using `[← hf]`. Conclude with `hle (Submodule.subset_span ⟨u, hu, hu0, rfl⟩)`.
-/
theorem exists_residue_annihilator_of_not_standard_column_form (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) O)
    (hx : ¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) :
    ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  classical
  set V := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hV
  let A : Set (Fin r → IsLocalRing.ResidueField O) :=
    {v | ∃ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ V ∧
      (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) ∧ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = v}
  have hA0 : (0 : Fin r → IsLocalRing.ResidueField O) ∈ A :=
    ⟨0, by convert V.zero_mem using 1; ext; simp, by simp, by ext; simp⟩
  have hAadd : ∀ v w, v ∈ A → w ∈ A → v + w ∈ A := by
    rintro v w ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩
    refine ⟨u + u', ?_, ?_, ?_⟩
    · have := V.add_mem hu hu'
      convert this using 1
      ext i; simp
    · intro i; simp [hu0 i, hu0' i]
    · ext i; simp
  have hAsmul : ∀ (c : IsLocalRing.ResidueField O) v, v ∈ A → c • v ∈ A := by
    rintro c v ⟨u, hu, hu0, rfl⟩
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨c' • u, ?_, ?_, ?_⟩
    · have := V.smul_mem (algebraMap O K c') hu
      convert this using 1
      ext i; simp
    · intro i; simp [hu0 i]
    · ext i; simp
  have hspan : ∀ v ∈ Submodule.span (IsLocalRing.ResidueField O) A, v ∈ A := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact hA0
    | add y w _ _ hy hw => exact hAadd y w hy hw
    | smul c y _ hy => exact hAsmul c y hy
  by_cases htop : Submodule.span (IsLocalRing.ResidueField O) A = ⊤
  · exfalso
    apply hx
    have hmem : ∀ i : Fin r, (Pi.single i 1 : Fin r → IsLocalRing.ResidueField O) ∈ A :=
      fun i => hspan _ (htop ▸ Submodule.mem_top)
    choose u hu hu0 hu1 using hmem
    let B : Matrix (Fin r ⊕ Fin t) (Fin r) O := fun p j => u j p
    let T : Matrix (Fin r) (Fin r) O := fun i j => u j (Sum.inl i)
    have hT : IsUnit T.det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      have : (IsLocalRing.residue O).mapMatrix T = 1 := by
        ext i j
        have := congrFun (hu1 j) i
        show IsLocalRing.residue O (u j (Sum.inl i)) = _
        rw [this]; simp [Pi.single_apply, Matrix.one_apply]
      rw [this, Matrix.det_one]; exact one_ne_zero
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hdiv : ∀ (i : Fin t) (j : Fin r), ∃ c, u j (Sum.inr i) = ϖ * c := by
      intro i j
      have : u j (Sum.inr i) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.residue_eq_zero_iff _).1 (hu0 j i)
      rw [hmax, Ideal.mem_span_singleton] at this
      exact this
    choose C hC using hdiv
    have hcol : ∀ j, ∃ c : Fin r → K, ∑ l, c l • (fun i => algebraMap O K (x i l)) = fun i => algebraMap O K (u j i) :=
      fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu j)
    choose d hd using hcol
    let D : Matrix (Fin r) (Fin r) K := fun l j => d j l
    have hBD : x.map (algebraMap O K) * D = B.map (algebraMap O K) := by
      ext p j
      have := congrFun (hd j) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_apply, Matrix.map_apply]
      show _ = algebraMap O K (u j p)
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hTD : (x.submatrix Sum.inl id).map (algebraMap O K) * D = T.map (algebraMap O K) := by
      ext i j
      have := congrFun₂ hBD (Sum.inl i) j
      simpa [Matrix.mul_apply] using this
    have hdetT : (T.map (algebraMap O K)).det = algebraMap O K T.det := by
      rw [RingHom.map_det]; rfl
    have hTK : IsUnit (T.map (algebraMap O K)).det := by
      rw [hdetT]; exact hT.map _
    have hDu : IsUnit D.det := by
      rw [← hTD, Matrix.det_mul] at hTK
      exact isUnit_of_mul_isUnit_right hTK
    have hdetTi : ((T⁻¹).map (algebraMap O K)).det = algebraMap O K (T⁻¹).det := by
      rw [RingHom.map_det]; rfl
    have hg : IsUnit (D * (T⁻¹).map (algebraMap O K)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hdetTi]
      exact hDu.mul ((Matrix.isUnit_nonsing_inv_det T hT).map _)
    refine ⟨hg.unit, Matrix.fromRows 0 (Matrix.of fun i j => ∑ l, C i l * T⁻¹ l j), ?_⟩
    rw [IsUnit.unit_spec, ← Matrix.mul_assoc, hBD, ← Matrix.map_mul]
    congr 1
    ext p j
    rcases p with i | i
    · rw [Matrix.mul_apply]
      have := congrFun₂ (Matrix.mul_nonsing_inv T hT) i j
      rw [Matrix.mul_apply] at this
      simpa [B, T] using this
    · rw [Matrix.mul_apply]
      simp [B, hC, Finset.mul_sum, mul_assoc]
  · obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 htop)
    have hf : ∀ v, f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]; congr 2; ext j; simp [Pi.single_apply, eq_comm]
    refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
    · intro h0
      apply hf0
      apply LinearMap.ext
      intro v
      rw [LinearMap.zero_apply, hf v, h0, zero_dotProduct]
    · intro u hu hu0
      rw [← hf]
      exact hle (Submodule.subset_span ⟨u, hu, hu0, rfl⟩)

end GlobalTheory
