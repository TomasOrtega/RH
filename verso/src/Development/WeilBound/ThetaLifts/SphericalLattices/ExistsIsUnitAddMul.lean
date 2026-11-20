import Development.WeilBound.ThetaLifts.SphericalLattices.LatDefs

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

/- English proof (translation)
Take `⟨R, hR⟩` from `Submodule.exists_isCompl (LinearMap.range (Matrix.toLin' A))`. Take `⟨U', hU'⟩` from `Submodule.exists_isCompl ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))`. Establish `h1 : Module.finrank K ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D)) = Module.finrank K (LinearMap.ker (Matrix.toLin' A))`. Establish `hker : LinearMap.ker ((Matrix.toLin' D).domRestrict (LinearMap.ker (Matrix.toLin' A))) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `w hw`. Establish `hw1 : A *ᵥ (w : Fin n → K) = 0`. Use `w.2` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, Matrix.toLin'_apply]`. Then use the resulting hypothesis. Establish `hw2 : D *ᵥ (w : Fin n → K) = 0`.

Simplify `hw` using `[Matrix.toLin'_apply]`. Conclude with `Subtype.ext (h _ hw1 hw2)`. Rewrite using `[← LinearMap.range_domRestrict]`. Conclude with `LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)`. Establish `h2 : Module.finrank K R = Module.finrank K (LinearMap.ker (Matrix.toLin' A))`.

Establish `e1` using `Submodule.finrank_add_eq_of_isCompl hR`. Establish `e2` using `LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)`. Use linear arithmetic over natural numbers and integers. Set `e` to `LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)`. Set `proj` to `Submodule.linearProjOfIsCompl _ _ hU'`.

Set `c : (Fin n → K) →ₗ[K] (Fin n → K)` to `R.subtype ∘ₗ e.toLinearMap ∘ₗ proj`. Use `⟨LinearMap.toMatrix' c, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]`. Establish `key : ∀ x, (A + LinearMap.toMatrix' c * D) *ᵥ x = 0 → x = 0`. Introduce `x hx`.

Rewrite `hx` using `[Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]`. Establish `hcR : c (D *ᵥ x) ∈ R` using `(e (proj (D *ᵥ x))).2`. Establish `haR : A *ᵥ x ∈ LinearMap.range (Matrix.toLin' A)` using `⟨x, Matrix.toLin'_apply A x⟩`. Establish `hax : A *ᵥ x = 0`. Establish `hneg : A *ᵥ x = -(c (D *ᵥ x))` using `eq_neg_of_add_eq_zero_left hx`.

Establish `hmem : A *ᵥ x ∈ R` using `hneg ▸ R.neg_mem hcR`. Conclude with `(Submodule.disjoint_def.mp hR.disjoint) _ haR hmem`. Establish `hcx : c (D *ᵥ x) = 0`. Rewrite `hx` using `[hax, zero_add]`. Conclude with `hx`.

Establish `hDU : D *ᵥ x ∈ (LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D)` using `⟨x, by rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hax, Matrix.toLin'_apply D x⟩`. Establish `hproj : proj (D *ᵥ x) = ⟨D *ᵥ x, hDU⟩` using `Submodule.linearProjOfIsCompl_apply_left hU' ⟨_, hDU⟩`. Establish `hex : e ⟨D *ᵥ x, hDU⟩ = 0`. Establish `h3 : ((e (proj (D *ᵥ x)) : R) : Fin n → K) = 0` using `hcx`. Rewrite `h3` using `[hproj]`.

Conclude with `Subtype.ext h3`. Establish `hDx : D *ᵥ x = 0`. Establish `h4` using `congrArg Subtype.val (e.injective (hex.trans (map_zero e).symm))`. Conclude with `h4`. Conclude with `h x hax hDx`.

Introduce `x y hxy`. Establish `hsub : (A + LinearMap.toMatrix' c * D) *ᵥ (x - y) = 0`. Rewrite using `[Matrix.mulVec_sub, hxy, sub_self]`. Conclude with `sub_eq_zero.mp (key _ hsub)`.
-/
theorem exists_isUnit_add_mul {K : Type} [Field K] {n : ℕ} (A D : Matrix (Fin n) (Fin n) K)
    (h : ∀ x, A *ᵥ x = 0 → D *ᵥ x = 0 → x = 0) : ∃ C : Matrix (Fin n) (Fin n) K, IsUnit (A + C * D).det := by
  classical
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range (Matrix.toLin' A))
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))
  have h1 : Module.finrank K ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))
      = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
    have hker : LinearMap.ker ((Matrix.toLin' D).domRestrict (LinearMap.ker (Matrix.toLin' A))) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have hw1 : A *ᵥ (w : Fin n → K) = 0 := by
        have := w.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hw2 : D *ᵥ (w : Fin n → K) = 0 := by
        simpa [Matrix.toLin'_apply] using hw
      exact Subtype.ext (h _ hw1 hw2)
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
  have h2 : Module.finrank K R = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
    have e1 := Submodule.finrank_add_eq_of_isCompl hR
    have e2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
    omega
  let e := LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  let proj := Submodule.linearProjOfIsCompl _ _ hU'
  let c : (Fin n → K) →ₗ[K] (Fin n → K) := R.subtype ∘ₗ e.toLinearMap ∘ₗ proj
  refine ⟨LinearMap.toMatrix' c, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ x, (A + LinearMap.toMatrix' c * D) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hx
    have hcR : c (D *ᵥ x) ∈ R := (e (proj (D *ᵥ x))).2
    have haR : A *ᵥ x ∈ LinearMap.range (Matrix.toLin' A) := ⟨x, Matrix.toLin'_apply A x⟩
    have hax : A *ᵥ x = 0 := by
      have hneg : A *ᵥ x = -(c (D *ᵥ x)) := eq_neg_of_add_eq_zero_left hx
      have hmem : A *ᵥ x ∈ R := hneg ▸ R.neg_mem hcR
      exact (Submodule.disjoint_def.mp hR.disjoint) _ haR hmem
    have hcx : c (D *ᵥ x) = 0 := by
      rw [hax, zero_add] at hx
      exact hx
    have hDU : D *ᵥ x ∈ (LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D) :=
      ⟨x, by rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hax,
        Matrix.toLin'_apply D x⟩
    have hproj : proj (D *ᵥ x) = ⟨D *ᵥ x, hDU⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hU' ⟨_, hDU⟩
    have hex : e ⟨D *ᵥ x, hDU⟩ = 0 := by
      have h3 : ((e (proj (D *ᵥ x)) : R) : Fin n → K) = 0 := hcx
      rw [hproj] at h3
      exact Subtype.ext h3
    have hDx : D *ᵥ x = 0 := by
      have h4 := congrArg Subtype.val (e.injective (hex.trans (map_zero e).symm))
      exact h4
    exact h x hax hDx
  intro x y hxy
  have hsub : (A + LinearMap.toMatrix' c * D) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨A, Z, hZ, hY⟩` from `h1`. Take `⟨B, Z', hZ', hY'⟩` from `h2`. Establish `hsurj` using `IsLocalRing.residue_surjective (R := 𝒪[k])`. Take `⟨Cb, hCb⟩` from `exists_isUnit_add_mul (A.map (IsLocalRing.residue 𝒪[k])) (1 - B.map (IsLocalRing.residue 𝒪[k]) * A.map (IsLocalRing.residue 𝒪[k])) (by`. Introduce `x hx1 hx2`.

Rewrite `hx2` using `[Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx1, Matrix.mulVec_zero, sub_zero]`. Conclude with `hx2)`. Set `C : Matrix (Fin n) (Fin n) 𝒪[k]` to `Cb.map (Function.surjInv hsurj)`. Establish `hC : C.map (IsLocalRing.residue 𝒪[k]) = Cb`. Use extensionality with `i j`.

Simplify using `only [C, Matrix.map_apply]`. Conclude with `Function.surjInv_eq hsurj _`. Set `FinalForm : Matrix (Fin n) (Fin d) 𝒪[k]` to `Matrix.of fun i j => ⟨Z i j, hZ i j⟩`. Set `Zo' : Matrix (Fin n) (Fin d) 𝒪[k]` to `Matrix.of fun i j => ⟨Z' i j, hZ' i j⟩`. Establish `hZo : FinalForm.map (algebraMap 𝒪[k] k) = Z`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hZo' : Zo'.map (algebraMap 𝒪[k] k) = Z'`. Use extensionality with `i j`. Both sides reduce to the same expression.

Use `⟨A + C * (1 - B * A), ?_, (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k), ?_, ?_⟩` and prove the remaining obligations. Apply `isUnit_of_map_unit (IsLocalRing.residue 𝒪[k])` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add (IsLocalRing.residue 𝒪[k]) (map_add _), Matrix.map_mul, Matrix.map_sub (IsLocalRing.residue 𝒪[k]) (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, hC]`. Conclude with `hCb`. Introduce `i j`.

Conclude with `((FinalForm - C * (B * FinalForm + Zo')) i j).2`. Establish `hU : (A + C * (1 - B * A)).map (algebraMap 𝒪[k] k) = A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k) * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k))`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]`. Establish `hW : (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k) = Z - C.map (algebraMap 𝒪[k] k) * (B.map (algebraMap 𝒪[k] k) * Z + Z')`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hZo, hZo']`.

Establish `h2' : Y' = B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y' + t • (B.map (algebraMap 𝒪[k] k) * Z + Z')`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add]`. Normalize the expressions using the abelian group laws. Establish `e1 : Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y' = t • (B.map (algebraMap 𝒪[k] k) * Z + Z')`.

Rewrite using `[sub_eq_iff_eq_add']`. Conclude with `h2'`. Establish `e2 : (A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k) * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k))) * Y' = A.map (algebraMap 𝒪[k] k) * Y' + C.map (algebraMap 𝒪[k] k) * (Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y')`. Rewrite using `[Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]`. Rewrite using `[hU, hW, e2, e1, Matrix.mul_smul, smul_sub]`.

Use `conv_lhs => rw [hY]`. Normalize the expressions using the abelian group laws.
-/
theorem orbit {n d : ℕ} {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} (h1 : Below t Y Y') (h2 : Below t Y' Y) :
    ∃ U : Matrix (Fin n) (Fin n) 𝒪[k], IsUnit U.det ∧ ∃ Z, IntM Z ∧ Y = U.map (algebraMap 𝒪[k] k) * Y' + t • Z := by
  classical
  obtain ⟨A, Z, hZ, hY⟩ := h1
  obtain ⟨B, Z', hZ', hY'⟩ := h2
  have hsurj := IsLocalRing.residue_surjective (R := 𝒪[k])
  obtain ⟨Cb, hCb⟩ := exists_isUnit_add_mul (A.map (IsLocalRing.residue 𝒪[k]))
    (1 - B.map (IsLocalRing.residue 𝒪[k]) * A.map (IsLocalRing.residue 𝒪[k])) (by
      intro x hx1 hx2
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx1, Matrix.mulVec_zero,
        sub_zero] at hx2
      exact hx2)
  let C : Matrix (Fin n) (Fin n) 𝒪[k] := Cb.map (Function.surjInv hsurj)
  have hC : C.map (IsLocalRing.residue 𝒪[k]) = Cb := by
    ext i j
    simp only [C, Matrix.map_apply]
    exact Function.surjInv_eq hsurj _
  let FinalForm : Matrix (Fin n) (Fin d) 𝒪[k] := Matrix.of fun i j => ⟨Z i j, hZ i j⟩
  let Zo' : Matrix (Fin n) (Fin d) 𝒪[k] := Matrix.of fun i j => ⟨Z' i j, hZ' i j⟩
  have hZo : FinalForm.map (algebraMap 𝒪[k] k) = Z := by
    ext i j
    rfl
  have hZo' : Zo'.map (algebraMap 𝒪[k] k) = Z' := by
    ext i j
    rfl
  refine ⟨A + C * (1 - B * A), ?_, (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k), ?_, ?_⟩
  · apply isUnit_of_map_unit (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add (IsLocalRing.residue 𝒪[k]) (map_add _),
      Matrix.map_mul, Matrix.map_sub (IsLocalRing.residue 𝒪[k]) (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, hC]
    exact hCb
  · intro i j
    exact ((FinalForm - C * (B * FinalForm + Zo')) i j).2
  · have hU : (A + C * (1 - B * A)).map (algebraMap 𝒪[k] k)
        = A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k)
          * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k)) := by
      rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]
    have hW : (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k)
        = Z - C.map (algebraMap 𝒪[k] k) * (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hZo, hZo']
    have h2' : Y' = B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y'
        + t • (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      calc Y' = B.map (algebraMap 𝒪[k] k) * Y + t • Z' := hY'
        _ = B.map (algebraMap 𝒪[k] k) * (A.map (algebraMap 𝒪[k] k) * Y' + t • Z) + t • Z' := by rw [hY]
        _ = _ := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add]
          abel
    have e1 : Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y'
        = t • (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      rw [sub_eq_iff_eq_add']
      exact h2'
    have e2 : (A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k)
          * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k))) * Y'
        = A.map (algebraMap 𝒪[k] k) * Y' + C.map (algebraMap 𝒪[k] k)
          * (Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y') := by
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
    rw [hU, hW, e2, e1, Matrix.mul_smul, smul_sub]
    conv_lhs => rw [hY]
    abel

end PositivityTheory.Sph

end
