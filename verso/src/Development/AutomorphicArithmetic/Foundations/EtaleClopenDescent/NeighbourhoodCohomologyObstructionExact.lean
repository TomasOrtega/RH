import Mathlib
import Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace UpperTheory.Cb.ConeExactness

/- English proof (translation)
Take `⟨c, rfl⟩` from `y.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add (m + 1))) = 0 at hy`. Rewrite `hy` using `[CohomologyClass.mk_eq_zero_iff]`. Take `⟨m', hm', β, hβ⟩` from `hy`. Take `rfl : m' = m` from `by omega`.

Establish `hβ' : δ m' (m' + 1) β = (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add (m' + 1))`. Rewrite using `[hβ]`. Both sides reduce to the same expression. Set `e : Cochain (mappingCone φ) (res R F) m'` to `(mappingCone.snd φ).comp β (zero_add m')`. Set `d : Cochain (mappingCone φ) (res R F) (m' + 1)` to `c.1 - δ m' (m' + 1) e`.

Establish `hinre : (Cochain.ofHom (mappingCone.inr φ)).comp e (zero_add m') = β`. Simplify using `only [e]`. Rewrite using `[← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_snd]`. Simplify using the standard rewrite rules. Establish `hinr : (Cochain.ofHom (mappingCone.inr φ)).comp d (zero_add (m' + 1)) = 0`.

Simplify using `only [d]`. Rewrite using `[Cochain.comp_sub, ← δ_ofHom_comp, hinre, hβ', sub_self]`. Establish `hdcl : δ (m' + 1) (m' + 1 + 1) d = 0`. Simplify using `only [d]`. Rewrite using `[δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]`.

Set `a : Cochain K (res R F) m'` to `(mappingCone.inl φ).comp d (by omega)`. Establish `hdec : (mappingCone.fst φ).1.comp a (add_comm 1 m') = d`. Establish `hid` using `mappingCone.id φ`. Establish `h2 : ((mappingCone.fst φ).1.comp (mappingCone.inl φ) (add_neg_cancel 1) + (mappingCone.snd φ).comp (Cochain.ofHom (mappingCone.inr φ)) (add_zero 0)).comp d (zero_add (m' + 1)) = d`. Rewrite using `[hid]`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[Cochain.add_comp, Cochain.comp_assoc _ _ _ (add_neg_cancel 1) (show (-1 : ℤ) + (m' + 1) = m' by omega) (show (1 : ℤ) + -1 + (m' + 1) = m' + 1 by omega), Cochain.comp_assoc_of_second_is_zero_cochain, hinr]`. Simplify `h2` using `[a]`. Establish `ha : δ m' (m' + 1) a = 0`. Establish `h1` using `δ_comp (mappingCone.fst φ).1 a (add_comm 1 m') 2 (m' + 1) (m' + 1 + 1) rfl (by omega) rfl`.

Rewrite `h1` using `[hdec, hdcl, Cocycle.δ_eq_zero]`. Establish `h2` using `congrArg (fun t => (mappingCone.inl φ).comp t (show (-1 : ℤ) + (m' + 1 + 1) = m' + 1 by omega)) h1`. Simplify using `only [Cochain.comp_zero, Cochain.zero_comp, smul_zero, add_zero] at h2`. Rewrite `h2` using `[← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (show (1 : ℤ) + (m' + 1) = m' + 1 + 1 by omega) (show (-1 : ℤ) + 1 + (m' + 1) = m' + 1 by omega), mappingCone.inl_fst]`. Simplify using `using h2.symm`.

Use `⟨CohomologyClass.mk (Cocycle.mk a (m' + 1) rfl ha), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (mappingCone.fst φ) (Cocycle.mk a (m' + 1) rfl ha) (add_comm 1 m')) = CohomologyClass.mk c`. Rewrite using `[← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]`. Use `⟨m', by omega, -e, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (mappingCone.fst φ).1.comp a (add_comm 1 m') - c.1`.

Rewrite using `[hdec, δ_neg]`. Simplify using `[d]`.
-/
private theorem cone_exact (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ)
    (y : HK R (mappingCone φ) F (m + 1))
    (hy : HK.pull R (mappingCone.inr φ) F (m + 1) y = 0) :
    ∃ w, HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) w = y := by
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add (m + 1))) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m', hm', β, hβ⟩ := hy
  obtain rfl : m' = m := by omega
  have hβ' : δ m' (m' + 1) β = (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add (m' + 1)) := by
    rw [hβ]; rfl

  let e : Cochain (mappingCone φ) (res R F) m' := (mappingCone.snd φ).comp β (zero_add m')
  let d : Cochain (mappingCone φ) (res R F) (m' + 1) := c.1 - δ m' (m' + 1) e
  have hinre : (Cochain.ofHom (mappingCone.inr φ)).comp e (zero_add m') = β := by
    simp only [e]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_snd]
    simp
  have hinr : (Cochain.ofHom (mappingCone.inr φ)).comp d (zero_add (m' + 1)) = 0 := by
    simp only [d]
    rw [Cochain.comp_sub, ← δ_ofHom_comp, hinre, hβ', sub_self]
  have hdcl : δ (m' + 1) (m' + 1 + 1) d = 0 := by
    simp only [d]
    rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]
  let a : Cochain K (res R F) m' := (mappingCone.inl φ).comp d (by omega)
  have hdec : (mappingCone.fst φ).1.comp a (add_comm 1 m') = d := by
    have hid := mappingCone.id φ
    have h2 : ((mappingCone.fst φ).1.comp (mappingCone.inl φ) (add_neg_cancel 1) +
        (mappingCone.snd φ).comp (Cochain.ofHom (mappingCone.inr φ)) (add_zero 0)).comp d (zero_add (m' + 1)) = d := by
      rw [hid]; simp
    rw [Cochain.add_comp, Cochain.comp_assoc _ _ _ (add_neg_cancel 1) (show (-1 : ℤ) + (m' + 1) = m' by omega)
        (show (1 : ℤ) + -1 + (m' + 1) = m' + 1 by omega),
      Cochain.comp_assoc_of_second_is_zero_cochain, hinr] at h2
    simpa [a] using h2
  have ha : δ m' (m' + 1) a = 0 := by
    have h1 := δ_comp (mappingCone.fst φ).1 a (add_comm 1 m') 2 (m' + 1) (m' + 1 + 1) rfl (by omega) rfl
    rw [hdec, hdcl, Cocycle.δ_eq_zero] at h1
    have h2 := congrArg (fun t => (mappingCone.inl φ).comp t (show (-1 : ℤ) + (m' + 1 + 1) = m' + 1 by omega)) h1
    simp only [Cochain.comp_zero, Cochain.zero_comp, smul_zero, add_zero] at h2
    rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (show (1 : ℤ) + (m' + 1) = m' + 1 + 1 by omega)
      (show (-1 : ℤ) + 1 + (m' + 1) = m' + 1 by omega), mappingCone.inl_fst] at h2
    simpa using h2.symm
  refine ⟨CohomologyClass.mk (Cocycle.mk a (m' + 1) rfl ha), ?_⟩
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (Cocycle.mk a (m' + 1) rfl ha) (add_comm 1 m')) =
    CohomologyClass.mk c
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m', by omega, -e, ?_⟩
  change _ = (mappingCone.fst φ).1.comp a (add_comm 1 m') - c.1
  rw [hdec, δ_neg]
  simp [d]

end UpperTheory.Cb.ConeExactness

/- English proof (translation)
Introduce `q _ U E u i m y hy`. Conclude with `UpperTheory.Cb.ConeExactness.cone_exact (ZMod q) _ _ m y hy`.
-/
theorem UpperTheory.Cb.neighbourhood_cohomology_obstruction_exact :
    LateralTheory.E.NeighbourhoodKilling.ObsExact := by
  intro q _ U E u i m y hy
  exact UpperTheory.Cb.ConeExactness.cone_exact (ZMod q) _ _ m y hy
