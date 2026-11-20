import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.TwSecPfGamma

/- English proof (translation)
Rewrite using `[Polynomial.map_map]`. Establish `: (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this, Polynomial.map_id]`.
-/
theorem map_symm_map {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (f : B[X]) :
    (f.map (e.symm : B →+* A)).map (e : A →+* B) = f := by
  rw [Polynomial.map_map]
  have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
    ext x; simp
  rw [this, Polynomial.map_id]

/- English proof (translation)
Simplify using `only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Rewrite using `[isUnit_map_iff e.symm x]`.
-/
theorem mem_max_iff {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (x : B) :
    e.symm x ∈ IsLocalRing.maximalIdeal A ↔ x ∈ IsLocalRing.maximalIdeal B := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [isUnit_map_iff e.symm x]

/- English proof (translation)
Use `haveI : Nontrivial A := inferInstance`. Use `haveI : Nontrivial B := e.injective.nontrivial`. Use `haveI : IsLocalRing B := IsLocalRing.of_surjective' (e : A →+* B) e.surjective`. Use `{ is_henselian := ?_ }` and prove the remaining obligations. Introduce `f hf a₀ h1 h2`.

Establish `hev : ∀ (p : B[X]) (b : B), (p.map (e.symm : B →+* A)).eval (e.symm b) = e.symm (p.eval b)`. Introduce `p b`. Rewrite using `[Polynomial.eval_map]`. Conclude with `Polynomial.eval₂_hom (e.symm : B →+* A) b`. Take `⟨a, ha, hmem⟩` from `hA.is_henselian (f.map (e.symm : B →+* A)) (hf.map _) (e.symm a₀) (by rw [hev, mem_max_iff]; exact h1) (by rw [Polynomial.derivative_map, hev]; exact (isUnit_map_iff e.symm _).2 h2)`.

Use `⟨e a, ?_, ?_⟩` and prove the remaining obligations. Use `ha.map (f := (e : A →+* B))` as an intermediate fact. Rewrite `this` using `[map_symm_map]`. Then use the resulting hypothesis. Rewrite using `[← mem_max_iff e]`. Establish `: e.symm (e a - a₀) = a - e.symm a₀` using `by simp`.

Rewrite using `[this]`. Conclude with `hmem`.
-/
theorem henselian_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) [hA : HenselianLocalRing A] :
    HenselianLocalRing B := by
  haveI : Nontrivial A := inferInstance
  haveI : Nontrivial B := e.injective.nontrivial
  haveI : IsLocalRing B := IsLocalRing.of_surjective' (e : A →+* B) e.surjective
  refine { is_henselian := ?_ }
  intro f hf a₀ h1 h2
  have hev : ∀ (p : B[X]) (b : B), (p.map (e.symm : B →+* A)).eval (e.symm b) = e.symm (p.eval b) := by
    intro p b
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom (e.symm : B →+* A) b
  obtain ⟨a, ha, hmem⟩ := hA.is_henselian (f.map (e.symm : B →+* A)) (hf.map _) (e.symm a₀)
    (by rw [hev, mem_max_iff]; exact h1)
    (by rw [Polynomial.derivative_map, hev]; exact (isUnit_map_iff e.symm _).2 h2)
  refine ⟨e a, ?_, ?_⟩
  · have := ha.map (f := (e : A →+* B))
    rwa [map_symm_map] at this
  · rw [← mem_max_iff e]
    have : e.symm (e a - a₀) = a - e.symm a₀ := by simp
    rw [this]; exact hmem

/- English proof (translation)
Use `IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_` and prove the remaining obligations. Establish `hdeg : (p.map (e.symm : L →+* K)).degree ≠ 0`. Rewrite using `[Polynomial.degree_map]`. Introduce `h`. Conclude with `hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)`.

Take `⟨x, hx⟩` from `IsSepClosed.exists_root (p.map (e.symm : L →+* K)) hdeg (hsep.map)`. Use `⟨e x, ?_⟩` and prove the remaining obligations. Use `hx.map (f := (e : K →+* L))` as an intermediate fact. Rewrite `this` using `[map_symm_map]`. Conclude with `this`.
-/
theorem sepClosed_of_equiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : (p.map (e.symm : L →+* K)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro h
    exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (p.map (e.symm : L →+* K)) hdeg (hsep.map)
  refine ⟨e x, ?_⟩
  have := hx.map (f := (e : K →+* L))
  rw [map_symm_map] at this
  exact this

/- English proof (translation)
Take `⟨hA, hs⟩` from `h`. Use `haveI := hA`. Use `haveI := henselian_of_equiv e`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Use `haveI := hs`.

Conclude with `sepClosed_of_equiv (IsLocalRing.ResidueField.mapEquiv e)`.
-/
theorem SH_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : SH A) : SH B := by
  obtain ⟨hA, hs⟩ := h
  haveI := hA
  haveI := henselian_of_equiv e
  refine ⟨inferInstance, ?_⟩
  haveI := hs
  exact sepClosed_of_equiv (IsLocalRing.ResidueField.mapEquiv e)

end LateralTheory.KummerTheory.TwSecPfGamma

namespace LateralTheory.KummerTheory

/- English proof (translation)
The claim follows from `TwSecPfGamma.SH_of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm h`.
-/
theorem SHGamma_holds (A : Type) [CommRing A] (h : SH A) : SH Γ(Spec (CommRingCat.of A), ⊤) :=
  TwSecPfGamma.SH_of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm h

end LateralTheory.KummerTheory
