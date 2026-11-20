import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtendPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtGen

open Polynomial UpperTheory.V.W

/- English proof (translation)
Take `⟨m, g, b, rfl⟩` from `UpperTheory.V.AlgebraTools.Det.genSpan (A := A) (G := G) (MvPolynomial σ A) x`. Establish `hP : D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1) ∈ Set.range (MvPolynomial.map ι)`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `c hc'`. Take `⟨β, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp hc'`.

Conclude with `hc m g β`. Take `⟨Q, hQ⟩` from `hP`. Establish `key` using `UpperTheory.V.AlgebraTools.Det.genEval D' (MvPolynomial σ A') m (fun j => MonoidAlgebra.single (g j) 1) (fun j => MvPolynomial.map ι (b j))`. Use `⟨MvPolynomial.aeval b Q, ?_⟩` and prove the remaining obligations. Establish `hx : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial σ A)) (MonoidAlgebra.single (g j) 1)) = ∑ j, (MvPolynomial.map ι (b j)) • MonoidAlgebra.mapRingHom G (algebraMap A' (MvPolynomial σ A')) (MonoidAlgebra.single ( …`.

Simplify using `[map_sum, MonoidAlgebra.mapRingHom_single]`. Rewrite using `[hx, key, ← hQ, MvPolynomial.map_aeval]`. Simplify using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_map]`. Rewrite using `[MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]`. Both sides reduce to the same expression.
-/
private theorem exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A']
    (ι : A →+* A') (D' : GDet n A' G)
    (hc : ∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      MvPolynomial.coeff β (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) ∈ ι.range)
    (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G) :
    D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) ∈ Set.range (MvPolynomial.map ι) := by
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) (G := G) (MvPolynomial σ A) x
  have hP : D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1) ∈ Set.range (MvPolynomial.map ι) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc'
    obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc'
    exact hc m g β
  obtain ⟨Q, hQ⟩ := hP
  have key := UpperTheory.V.AlgebraTools.Det.genEval D' (MvPolynomial σ A') m (fun j => MonoidAlgebra.single (g j) 1) (fun j => MvPolynomial.map ι (b j))
  refine ⟨MvPolynomial.aeval b Q, ?_⟩
  have hx : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial σ A)) (MonoidAlgebra.single (g j) 1)) = ∑ j, (MvPolynomial.map ι (b j)) • MonoidAlgebra.mapRingHom G (algebraMap A' (MvPolynomial σ A')) (MonoidAlgebra.single (g j) 1) := by
    simp [map_sum, MonoidAlgebra.mapRingHom_single]
  rw [hx, key, ← hQ, MvPolynomial.map_aeval]
  simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rfl

/- English proof (translation)
Simplify using `[GDet.gen, map_sum, MonoidAlgebra.mapRingHom_single]`.
-/
private theorem mapRingHom_gdet_gen_single_eq_gen_single {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A')
    (m : ℕ) (g : Fin m → G) :
    MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (GDet.gen (A := A) fun j => MonoidAlgebra.single (g j) 1) =
      GDet.gen (A := A') fun j => MonoidAlgebra.single (g j) 1 := by
  simp [GDet.gen, map_sum, MonoidAlgebra.mapRingHom_single]

/- English proof (translation)
Introduce `n A G _ _ A' _ ι D' hι hc`. Establish `hr` using `fun σ x => exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom ι D' hc σ x`. Establish `hinj : ∀ σ : Type, Function.Injective (MvPolynomial.map (σ` using `σ) ι) := fun σ => MvPolynomial.map_injective ι hι`. Set `d : (σ : Type) → MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A` to `fun σ => { toFun := fun x => Classical.choose (hr σ x) map_one' := hinj σ (by rw [Classical.choose_spec (hr σ 1), map_one, map_one, map_one]) map_mul' := fun x y => hinj σ (by`. Rewrite using `[Classical.choose_spec (hr σ (x * y)), map_mul, map_mul, map_mul, Classical.choose_spec (hr σ x), Classical.choose_spec (hr σ y)]) }`.

Establish `hd : ∀ σ x, MvPolynomial.map ι (d σ x) = D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x)` using `fun σ x => Classical.choose_spec (hr σ x)`. Establish `hnat : ∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G), d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)`. Introduce `σ τ f x`. Apply `hinj τ` to reduce the goal to its premises. Set `f' : MvPolynomial σ A' →ₐ[A'] MvPolynomial τ A'` to `MvPolynomial.aeval fun i => MvPolynomial.map ι (f (MvPolynomial.X i))`.

Establish `hf : (MvPolynomial.map ι).comp (f : MvPolynomial σ A →+* MvPolynomial τ A) = (f' : MvPolynomial σ A' →+* MvPolynomial τ A').comp (MvPolynomial.map ι)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Establish `ha` using `f.commutes a`. Simplify using `only [MvPolynomial.algebraMap_eq] at ha`.

Simplify using `[f', ha]`. Introduce `i`. Simplify using `[f']`. Establish `e1 : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = MonoidAlgebra.mapRingHom G (f' : MvPolynomial σ A' →+* MvPolynomial τ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x)`. Rewrite using `[← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, hf, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]`.

Rewrite using `[hd, e1, D'.nat (MvPolynomial σ A') (MvPolynomial τ A') f', ← hd]`. Conclude with `(RingHom.congr_fun hf _).symm`. Establish `hhom : ∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G), d σ (b • x) = b ^ n * d σ x`. Introduce `σ b x`. Apply `hinj σ` to reduce the goal to its premises.

Establish `hs : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (b • x) = MvPolynomial.map ι b • MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x`. Use extensionality with `g`. Simplify using `[MonoidAlgebra.mapRingHom_apply]`. Rewrite using `[hd, map_mul, map_pow, hd, hs, D'.homog]`. Take `⟨D, hD⟩` from `UpperTheory.V.AlgebraTools.Det.extendPoly d hnat hhom`.

Establish `hex : D.map ι = D'`. Apply `UpperTheory.V.AlgebraTools.Det.extGen` to reduce the goal to its premises. Introduce `m g`. Rewrite using `[← mapRingHom_gdet_gen_single_eq_gen_single ι m g, (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.1 (Fin m), hD, hd]`. Use `⟨D, hex, fun D2 h2 => ?_⟩` and prove the remaining obligations.

Conclude with `(UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => ι) (fun a ha => hι (by rw [ha (), map_zero])) ).1 D2 D (fun _ => by rw [h2, hex])`.
-/
theorem UpperTheory.V.AlgebraTools.Det.descend :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      MvPolynomial.coeff β (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) ∈ ι.range) →
    ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι hc
  have hr := fun σ x => exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom ι D' hc σ x
  have hinj : ∀ σ : Type, Function.Injective (MvPolynomial.map (σ := σ) ι) :=
    fun σ => MvPolynomial.map_injective ι hι
  let d : (σ : Type) → MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A := fun σ =>
    { toFun := fun x => Classical.choose (hr σ x)
      map_one' := hinj σ (by rw [Classical.choose_spec (hr σ 1), map_one, map_one, map_one])
      map_mul' := fun x y => hinj σ (by
        rw [Classical.choose_spec (hr σ (x * y)), map_mul, map_mul, map_mul,
          Classical.choose_spec (hr σ x), Classical.choose_spec (hr σ y)]) }
  have hd : ∀ σ x, MvPolynomial.map ι (d σ x) =
      D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) :=
    fun σ x => Classical.choose_spec (hr σ x)
  have hnat : ∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x) := by
    intro σ τ f x
    apply hinj τ
    let f' : MvPolynomial σ A' →ₐ[A'] MvPolynomial τ A' :=
      MvPolynomial.aeval fun i => MvPolynomial.map ι (f (MvPolynomial.X i))
    have hf : (MvPolynomial.map ι).comp (f : MvPolynomial σ A →+* MvPolynomial τ A) =
        (f' : MvPolynomial σ A' →+* MvPolynomial τ A').comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have ha := f.commutes a
        simp only [MvPolynomial.algebraMap_eq] at ha
        simp [f', ha]
      · intro i
        simp [f']
    have e1 : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) =
        MonoidAlgebra.mapRingHom G (f' : MvPolynomial σ A' →+* MvPolynomial τ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) := by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, hf, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]
    rw [hd, e1, D'.nat (MvPolynomial σ A') (MvPolynomial τ A') f', ← hd]
    exact (RingHom.congr_fun hf _).symm
  have hhom : ∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d σ (b • x) = b ^ n * d σ x := by
    intro σ b x
    apply hinj σ
    have hs : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (b • x) =
        MvPolynomial.map ι b • MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply]
    rw [hd, map_mul, map_pow, hd, hs, D'.homog]
  obtain ⟨D, hD⟩ := UpperTheory.V.AlgebraTools.Det.extendPoly d hnat hhom
  have hex : D.map ι = D' := by
    apply UpperTheory.V.AlgebraTools.Det.extGen
    intro m g
    rw [← mapRingHom_gdet_gen_single_eq_gen_single ι m g, (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.1 (Fin m), hD, hd]
  refine ⟨D, hex, fun D2 h2 => ?_⟩
  exact (UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => ι)
    (fun a ha => hι (by rw [ha (), map_zero])) ).1 D2 D (fun _ => by rw [h2, hex])
