import Development.EtaleCohomology.EtaleSheaves.ChartsGeomVpaPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.ChartOverlap₂

set_option linter.unusedSectionVars false

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

/- English proof (translation)
Establish `key : ∀ s : S, (∃ d ∈ (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P).asIdeal, (d : K) = (s : K)) ↔ res (eR.symm s) ∈ P.asIdeal`. Introduce `s`. Establish `hd : eW (res (eR.symm s)) = ⟨(s : K), by simpa [hc] using (eW (res (eR.symm s))).2⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, hd1, hd2⟩`. Establish `: d = eW (res (eR.symm s))` using `by rw [hd]; exact Subtype.ext hd2`. Substitute `this` using the available equality. Simplify using `using hd1`.

Introduce `h`. Use `⟨eW (res (eR.symm s)), ?_, by simp [hc]⟩` and prove the remaining obligations. Simplify using `using h`. Unfold `Restr`. Repeatedly rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `r`. Simplify using `only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe]`. Use `h (eR r)` as an intermediate fact.

Simplify using `using this`. Introduce `h s`. Use `congrArg (fun q : PrimeSpectrum R => eR.symm s ∈ q.asIdeal) h` as an intermediate fact. Simplify using `only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this`. Conclude with `Iff.of_eq this`.
-/
theorem restr_iff (B : Subalgebra A K) (t : K) (S : Subalgebra A K) {R W : Type} [CommRing R] [CommRing W]
    (eR : R ≃+* S) (eW : W ≃+* AdjoinInv B t) (res : R →+* W) (hc : ∀ r, ((eW (res r) : AdjoinInv B t) : K) = (eR r : K))
    (P : PrimeSpectrum W) (x : PrimeSpectrum S) :
    Restr B t (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P) S x ↔
      PrimeSpectrum.comap (eR : R →+* S) x = PrimeSpectrum.comap res P := by
  have key : ∀ s : S, (∃ d ∈ (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P).asIdeal, (d : K) = (s : K)) ↔
      res (eR.symm s) ∈ P.asIdeal := by
    intro s
    have hd : eW (res (eR.symm s)) = ⟨(s : K), by simpa [hc] using (eW (res (eR.symm s))).2⟩ := by
      apply Subtype.ext; simp [hc]
    constructor
    · rintro ⟨d, hd1, hd2⟩
      have : d = eW (res (eR.symm s)) := by rw [hd]; exact Subtype.ext hd2
      subst this
      simpa using hd1
    · intro h
      refine ⟨eW (res (eR.symm s)), ?_, by simp [hc]⟩
      simpa using h
  unfold Restr
  simp_rw [key]
  constructor
  · intro h
    ext r
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe]
    have := h (eR r)
    simpa using this
  · intro h s
    have := congrArg (fun q : PrimeSpectrum R => eR.symm s ∈ q.asIdeal) h
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    exact Iff.of_eq this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chartMap_base {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) (x : PrimeSpectrum B) :
    (chartMap hU φ hi B hr).base x =
      hU.fromSpec.base (PrimeSpectrum.comap (chartEquiv φ hi B hr : Γ(Z, U) →+* B) x) := rfl

/- English proof (translation)
Rewrite using `[← hU.map_fromSpec hW (homOfLE h).op]`. Both sides reduce to the same expression.
-/
theorem fromSpec_res {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U)
    (P : PrimeSpectrum Γ(Z, W)) :
    hU.fromSpec.base (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom P) = hW.fromSpec.base P := by
  rw [← hU.map_fromSpec hW (homOfLE h).op]; rfl

/- English proof (translation)
Introduce `A _ _ K _ _ Z p B C t _ U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV x y`. Use `set eU := chartEquiv φU iU B rU`. Use `set eV := chartEquiv φV iV C rV`. Use `set eW := chartEquiv φW iW (AdjoinInv B t) rW`. Establish `hcU : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom r) : AdjoinInv B t) : K) = (eU r : K)` using `fun r => cU r`.

Establish `hcV : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom r) : AdjoinInv B t) : K) = (eV r : K)` using `fun r => cV r`. Rewrite using `[chartMap_base, chartMap_base]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hzU : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (U : Set Z)`.

Rewrite using `[← hU.range_fromSpec]`. Conclude with `⟨_, rfl⟩`. Establish `hzV : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (V : Set Z)`. Rewrite using `[h, ← hV.range_fromSpec]`. Conclude with `⟨_, rfl⟩`.

Establish `hz : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ Set.range hW.fromSpec.base`. Rewrite using `[hW.range_fromSpec]`. Conclude with `⟨hzU, hzV⟩`. Take `⟨P, hP⟩` from `hz`. Use `⟨PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V)) P, (restr_iff B t B eU eW _ hcU P x).2 ?_, (restr_iff B t C eV eW _ hcV P y).2 ?_⟩` and prove the remaining obligations.

Apply `hU.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises. Conclude with `((fromSpec_res hU hW inf_le_left P).trans hP).symm`. Apply `hV.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises. Conclude with `(h.symm.trans hP.symm).trans (fromSpec_res hV hW inf_le_right P).symm`. Introduce and unpack `⟨Q, hx, hy⟩`.

Establish `hQ : Q = PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V)) (PrimeSpectrum.comap (eW : Γ(Z, U ⊓ V) →+* AdjoinInv B t) Q)`. Use extensionality with `a`. Simplify using `only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]`. Rewrite `hx`, `hy` using `[hQ]`. Establish `hx1` using `(restr_iff B t B eU eW _ hcU _ x).1 hx`.

Establish `hy1` using `(restr_iff B t C eV eW _ hcV _ y).1 hy`. Conclude with `(congrArg hU.fromSpec.base hx1).trans ((fromSpec_res hU hW inf_le_left _).trans ((fromSpec_res hV hW inf_le_right _).symm.trans (congrArg hV.fromSpec.base hy1).symm))`.
-/
theorem Overlap_of : LateralTheory.E.ChartsGeom_vpaPf.Overlap := by
  intro A _ _ K _ _ Z p B C t _ U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV x y
  set eU := chartEquiv φU iU B rU
  set eV := chartEquiv φV iV C rV
  set eW := chartEquiv φW iW (AdjoinInv B t) rW
  have hcU : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom r) : AdjoinInv B t) : K) =
      (eU r : K) := fun r => cU r
  have hcV : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom r) : AdjoinInv B t) : K) =
      (eV r : K) := fun r => cV r
  rw [chartMap_base, chartMap_base]
  constructor
  · intro h
    have hzU : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (U : Set Z) := by
      rw [← hU.range_fromSpec]; exact ⟨_, rfl⟩
    have hzV : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (V : Set Z) := by
      rw [h, ← hV.range_fromSpec]; exact ⟨_, rfl⟩
    have hz : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ Set.range hW.fromSpec.base := by
      rw [hW.range_fromSpec]; exact ⟨hzU, hzV⟩
    obtain ⟨P, hP⟩ := hz
    refine ⟨PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V)) P,
      (restr_iff B t B eU eW _ hcU P x).2 ?_, (restr_iff B t C eV eW _ hcV P y).2 ?_⟩
    · apply hU.fromSpec.isOpenEmbedding.injective
      exact ((fromSpec_res hU hW inf_le_left P).trans hP).symm
    · apply hV.fromSpec.isOpenEmbedding.injective
      exact (h.symm.trans hP.symm).trans (fromSpec_res hV hW inf_le_right P).symm
  · rintro ⟨Q, hx, hy⟩
    have hQ : Q = PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V))
        (PrimeSpectrum.comap (eW : Γ(Z, U ⊓ V) →+* AdjoinInv B t) Q) := by
      ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rw [hQ] at hx hy
    have hx1 := (restr_iff B t B eU eW _ hcU _ x).1 hx
    have hy1 := (restr_iff B t C eV eW _ hcV _ y).1 hy
    exact (congrArg hU.fromSpec.base hx1).trans ((fromSpec_res hU hW inf_le_left _).trans
      ((fromSpec_res hV hW inf_le_right _).symm.trans (congrArg hV.fromSpec.base hy1).symm))

end LateralTheory.E.ChartOverlap₂
