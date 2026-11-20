import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

/- English proof (translation)
Rewrite using `[eval_map, eval₂_at_apply]`.
-/
theorem evalMapHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (x : R) :
    (p.map f).eval (f x) = f (p.eval x) := by
  rw [eval_map, eval₂_at_apply]

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (c.w e)`.
-/
theorem Diag.leg_comp_map {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J}
    (e : j ⟶ k) : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

/- English proof (translation)
Introduce `A _ I Δ c hc η hη`. Establish `st` using `hS A I Δ c hc η hη`. Establish `push : ∀ j (S : Type) [CommRing S] (φ : Δ.D.obj j →+* S), Good φ (I.map (Δ.s j)) → ∃ π : S →+* c.pt, π.comp φ = Δ.leg c j`. Introduce `j S _ φ hφ`. Take `⟨k, e, ρ, hρ⟩` from `Δ.exh j S φ hφ`.

Conclude with `⟨(Δ.leg c k).comp ρ, by rw [RingHom.comp_assoc, hρ, Δ.leg_comp_map]⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `y`.

Establish `hzy : z * y ∈ I.map η` using `Ideal.mul_mem_right y _ hz`. Take `⟨j, hj⟩` from `st.1 {z * y}`. Take `⟨x, hx⟩` from `hj (z * y) (Finset.mem_singleton_self _)`. Establish `hx' : x ∈ I.map (Δ.s j)` using `st.2 j x (by rw [hx]; exact hzy)`. Take `⟨S, _, φ, hφ, hu⟩` from `hI (Δ.D.obj j) (I.map (Δ.s j)) x hx'`.

Take `⟨π, hπ⟩` from `push j S φ hφ`. Establish `h` using `hu.map π`. Rewrite `h` using `[← RingHom.comp_apply, hπ, map_add, map_one, hx, add_comm]`. Conclude with `h`. Introduce `f hf a₀ ha₀ hu`.

Take `⟨u, hu'⟩` from `Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : c.pt ⧸ I.map η)`. Establish `hdu : f.derivative.eval a₀ * u - 1 ∈ I.map η`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu', map_one, IsUnit.mul_val_inv, sub_self]`. Set `T : Finset c.pt` to `insert a₀ (insert u (f.support.image f.coeff))`. Take `⟨j, hj⟩` from `st.1 T`.

Take `⟨a, ha⟩` from `hj a₀ (Finset.mem_insert_self _ _)`. Take `⟨v, hv⟩` from `hj u (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))`. Establish `hco : ∀ n, f.coeff n ∈ Set.range (Δ.leg c j)`. Introduce `n`. Distinguish the cases in `hn : n ∈ f.support`.

Conclude with `hj _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))`. Conclude with `⟨0, by rw [map_zero, notMem_support_iff.1 hn]⟩`. Take `⟨g, hg, -, hgm⟩` from `lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hco) hf`. Establish `h1 : g.eval a ∈ I.map (Δ.s j)` using `st.2 j _ (by rw [← evalMapHom, hg, ha]; exact ha₀)`. Establish `h2 : g.derivative.eval a * v - 1 ∈ I.map (Δ.s j)` using `st.2 j _ (by`.

Rewrite using `[map_sub, map_mul, map_one, ← evalMapHom, ← derivative_map, hg, ha, hv]`. Conclude with `hdu)`. Establish `h3 : IsUnit (Ideal.Quotient.mk (I.map (Δ.s j)) (g.derivative.eval a))` using `IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v) (by rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (Δ.s j)))]; exact Ideal.Quotient.eq.2 h2)`. Take `⟨S, _, φ, b, hφ, hb, hba⟩` from `hR (Δ.D.obj j) (I.map (Δ.s j)) g a hgm h1 h3`. Take `⟨π, hπ⟩` from `push j S φ hφ`.

Use `⟨π b, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hb.map (f := π)`. Rewrite `h` using `[Polynomial.map_map, hπ, hg]`. Then use the resulting hypothesis. Establish `h` using `Ideal.mem_map_of_mem π hba`. Rewrite `h` using `[Ideal.map_map, Ideal.map_map, hπ, hη, map_sub, ← RingHom.comp_apply, hπ, ha]`.

Conclude with `h`.
-/
theorem LeafColHens_of (hS : LeafStage) (hI : LeafInv) (hR : LeafRoot) : LeafColHens := by
  classical
  intro A _ I Δ c hc η hη
  have st := hS A I Δ c hc η hη
  have push : ∀ j (S : Type) [CommRing S] (φ : Δ.D.obj j →+* S), Good φ (I.map (Δ.s j)) →
      ∃ π : S →+* c.pt, π.comp φ = Δ.leg c j := by
    intro j S _ φ hφ
    obtain ⟨k, e, ρ, hρ⟩ := Δ.exh j S φ hφ
    exact ⟨(Δ.leg c k).comp ρ, by rw [RingHom.comp_assoc, hρ, Δ.leg_comp_map]⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Ideal.mem_jacobson_bot]
    intro y
    have hzy : z * y ∈ I.map η := Ideal.mul_mem_right y _ hz
    obtain ⟨j, hj⟩ := st.1 {z * y}
    obtain ⟨x, hx⟩ := hj (z * y) (Finset.mem_singleton_self _)
    have hx' : x ∈ I.map (Δ.s j) := st.2 j x (by rw [hx]; exact hzy)
    obtain ⟨S, _, φ, hφ, hu⟩ := hI (Δ.D.obj j) (I.map (Δ.s j)) x hx'
    obtain ⟨π, hπ⟩ := push j S φ hφ
    have h := hu.map π
    rw [← RingHom.comp_apply, hπ, map_add, map_one, hx, add_comm] at h
    exact h
  · intro f hf a₀ ha₀ hu
    obtain ⟨u, hu'⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : c.pt ⧸ I.map η)
    have hdu : f.derivative.eval a₀ * u - 1 ∈ I.map η := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu', map_one, IsUnit.mul_val_inv, sub_self]
    let T : Finset c.pt := insert a₀ (insert u (f.support.image f.coeff))
    obtain ⟨j, hj⟩ := st.1 T
    obtain ⟨a, ha⟩ := hj a₀ (Finset.mem_insert_self _ _)
    obtain ⟨v, hv⟩ := hj u (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hco : ∀ n, f.coeff n ∈ Set.range (Δ.leg c j) := by
      intro n
      by_cases hn : n ∈ f.support
      · exact hj _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
      · exact ⟨0, by rw [map_zero, notMem_support_iff.1 hn]⟩
    obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hco) hf
    have h1 : g.eval a ∈ I.map (Δ.s j) := st.2 j _ (by rw [← evalMapHom, hg, ha]; exact ha₀)
    have h2 : g.derivative.eval a * v - 1 ∈ I.map (Δ.s j) := st.2 j _ (by
      rw [map_sub, map_mul, map_one, ← evalMapHom, ← derivative_map, hg, ha, hv]; exact hdu)
    have h3 : IsUnit (Ideal.Quotient.mk (I.map (Δ.s j)) (g.derivative.eval a)) :=
      IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v)
        (by rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (Δ.s j)))]; exact Ideal.Quotient.eq.2 h2)
    obtain ⟨S, _, φ, b, hφ, hb, hba⟩ := hR (Δ.D.obj j) (I.map (Δ.s j)) g a hgm h1 h3
    obtain ⟨π, hπ⟩ := push j S φ hφ
    refine ⟨π b, ?_, ?_⟩
    · have h := hb.map (f := π)
      rwa [Polynomial.map_map, hπ, hg] at h
    · have h := Ideal.mem_map_of_mem π hba
      rw [Ideal.map_map, Ideal.map_map, hπ, hη, map_sub, ← RingHom.comp_apply, hπ, ha] at h
      exact h

end LateralTheory.CohomologicalPurity.Hz
