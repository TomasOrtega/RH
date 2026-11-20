import Development.EtaleCohomology.EtaleSheaves.GlueRelPf

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace LateralTheory.E.GlueRelPfCone

/- English proof (translation)
Take `⟨b, rfl⟩` from `b.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (mappingCone.fst φ) (zcomp (Cocycle.ofHom φ) b (zero_add m)) (add_comm 1 m)) = 0`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`. Use `⟨m, rfl, -(m.negOnePow • (mappingCone.snd φ).comp b.1 (zero_add m)), ?_⟩` and prove the remaining obligations. Use `ext1`.

Simplify using `only [zcomp, Cocycle.ofHom_coe]`. Rewrite using `[δ_neg, δ_units_smul, δ_comp _ _ (zero_add m) 1 (m + 1) (m + 1) rfl (zero_add 1) rfl, mappingCone.δ_snd]`. Simplify using `[Cocycle.δ_eq_zero, Cochain.comp_assoc_of_second_is_zero_cochain, smul_smul, Int.units_mul_self]`.
-/
theorem pre_pull_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (b : HK R L F m) :
    HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) (HK.pull R φ F m b) = 0 := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (zcomp (Cocycle.ofHom φ) b (zero_add m)) (add_comm 1 m)) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, rfl, -(m.negOnePow • (mappingCone.snd φ).comp b.1 (zero_add m)), ?_⟩
  ext1
  simp only [zcomp, Cocycle.ofHom_coe]
  rw [δ_neg, δ_units_smul, δ_comp _ _ (zero_add m) 1 (m + 1) (m + 1) rfl (zero_add 1) rfl, mappingCone.δ_snd]
  simp [Cocycle.δ_eq_zero, Cochain.comp_assoc_of_second_is_zero_cochain, smul_smul, Int.units_mul_self]

/- English proof (translation)
Take `⟨a, rfl⟩` from `x.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (mappingCone.fst φ) a (add_comm 1 m)) = 0 at hx`. Rewrite `hx` using `[CohomologyClass.mk_eq_zero_iff]`. Take `⟨m', hm', γ, hγ⟩` from `hx`. Take `rfl : m' = m` from `by omega`.

Establish `hγ' : δ m' (m' + 1) γ = (mappingCone.fst φ).1.comp a.1 (add_comm 1 m')`. Rewrite using `[hγ]`. Both sides reduce to the same expression. Establish `hb : δ m' (m' + 1) ((Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')) = 0`. Rewrite using `[δ_comp _ _ (zero_add m') 1 (m' + 1) (m' + 1) rfl (zero_add 1) rfl, hγ', δ_ofHom]`.

Rewrite using `[← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]`. Simplify using the standard rewrite rules. Set `b : Cocycle L (res R F) m'` to `Cocycle.mk (-(m'.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m'))) (m' + 1) rfl (by rw [δ_neg, δ_units_smul, hb]; simp)`. Use `⟨CohomologyClass.mk b, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add m')) = CohomologyClass.mk a`.

Rewrite using `[← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]`. Use `⟨m' - 1, by omega, -((mappingCone.inl φ).comp γ (by omega)), ?_⟩` and prove the remaining obligations. Use `ext1`. Rewrite using `[δ_neg, δ_comp _ _ (show -1 + m' = m' - 1 by omega) 0 (m' + 1) m' (by omega) (by omega) rfl, hγ', mappingCone.δ_inl]`. Rewrite using `[← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_comm 1 m') (by omega), mappingCone.inl_fst]`.

Simplify using `[zcomp, b, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, sub_eq_add_neg]`.
-/
theorem range_of_pre_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (x : HK R K F m)
    (hx : HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) x = 0) : x ∈ Set.range (HK.pull R φ F m) := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) a (add_comm 1 m)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m', hm', γ, hγ⟩ := hx
  obtain rfl : m' = m := by omega
  have hγ' : δ m' (m' + 1) γ = (mappingCone.fst φ).1.comp a.1 (add_comm 1 m') := by
    rw [hγ]; rfl
  have hb : δ m' (m' + 1) ((Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')) = 0 := by
    rw [δ_comp _ _ (zero_add m') 1 (m' + 1) (m' + 1) rfl (zero_add 1) rfl, hγ', δ_ofHom]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp
  let b : Cocycle L (res R F) m' := Cocycle.mk (-(m'.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')))
    (m' + 1) rfl (by rw [δ_neg, δ_units_smul, hb]; simp)
  refine ⟨CohomologyClass.mk b, ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add m')) = CohomologyClass.mk a
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m' - 1, by omega, -((mappingCone.inl φ).comp γ (by omega)), ?_⟩
  ext1
  rw [δ_neg, δ_comp _ _ (show -1 + m' = m' - 1 by omega) 0 (m' + 1) m' (by omega) (by omega) rfl, hγ',
    mappingCone.δ_inl]
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_comm 1 m') (by omega), mappingCone.inl_fst]
  simp [zcomp, b, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, sub_eq_add_neg]

/- English proof (translation)
Introduce `R _ K L φ F m x`. Conclude with `⟨range_of_pre_zero R φ F m x, by rintro ⟨b, rfl⟩; exact pre_pull_zero R φ F m b⟩`.
-/
theorem coneExact : LateralTheory.E.GlueRelPf.ConeExact := by
  intro R _ K L φ F m x
  exact ⟨range_of_pre_zero R φ F m x, by rintro ⟨b, rfl⟩; exact pre_pull_zero R φ F m b⟩

/- English proof (translation)
The claim follows from `LateralTheory.E.GlueRelPf.GlueRel_of coneExact hE`.
-/
theorem GlueRel_of (hE : LateralTheory.E.GlueRelPf.EdgeInj) : LateralTheory.E.LocGlueEtPf.GlueRel :=
  LateralTheory.E.GlueRelPf.GlueRel_of coneExact hE

end LateralTheory.E.GlueRelPfCone
