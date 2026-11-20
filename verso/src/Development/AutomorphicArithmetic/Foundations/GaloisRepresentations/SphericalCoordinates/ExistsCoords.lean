import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Set `f : K →+* Module.End ℚ V` to `(rep : C →+* Module.End ℚ V).comp (algebraMap K C)`. Use `letI : Module K V := Module.compHom V f`. Establish `hsm : ∀ (x : K) (w : V), x • w = rep (algebraMap K C x) w` using `fun _ _ => rfl`. Use `haveI : IsScalarTower ℚ K V := by`. Use `⟨fun q x w => ?_⟩` and prove the remaining obligations.

Rewrite using `[hsm, hsm, ← IsScalarTower.toAlgHom_apply ℚ K C, map_smul, map_smul]`. Both sides reduce to the same expression. Use `haveI : Module.Finite K V := Module.Finite.of_restrictScalars_finite ℚ K V`. Establish `hfin : Module.finrank K V = n`. Establish `h` using `Module.finrank_mul_finrank ℚ K V`.

Establish `hpos : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Rewrite `h` using `[hdim, mul_comm n]`. Conclude with `Nat.eq_of_mul_eq_mul_left hpos h`. Set `b : Module.Basis (Fin n) K V` to `Module.finBasisOfFinrankEq K V hfin`. Set `r : C →ₐ[K] Module.End K V` to `AlgHom.ofLinearMap { toFun := fun c => { toFun := rep c map_add' := map_add _ map_smul' := fun x w => by`.

Simplify using `only [RingHom.id_apply, hsm]`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes] }`. Use the proof step `map_add' := fun c c' => by ext w; simp`. Use the proof step `map_smul' := fun x c => by`. Use extensionality with `w`.

Simplify using `[hsm, Algebra.smul_def, Module.End.mul_apply] }`. Use the proof step `(by ext w; simp) (fun c c' => by ext w; simp [Module.End.mul_apply])`. Establish `hr : ∀ c w, r c w = rep c w` using `fun _ _ => rfl`. Set `s : C →ₐ[K] Matrix (Fin n) (Fin n) K` to `(LinearMap.toMatrixAlgEquiv b).toAlgHom.comp r`. Establish `hsinj : Function.Injective s`.

Introduce `c c' h`. Establish `h' : r c = r c'` using `(LinearMap.toMatrixAlgEquiv b).injective h`. Apply `hinj` to reduce the goal to its premises. Use extensionality with `w`. Conclude with `congrArg (fun g => g w) h'`.

Establish `hrk : Module.finrank K C = Module.finrank K (Matrix (Fin n) (Fin n) K)`. Rewrite using `[hC, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsurj : Function.Surjective s` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := s.toLinearMap) hrk).1 hsinj`. Use `⟨b.equivFun.toAddEquiv, AlgEquiv.ofBijective s ⟨hsinj, hsurj⟩, fun c w => ?_⟩` and prove the remaining obligations.

Establish `h` using `LinearMap.toMatrix_mulVec_repr b b (r c) w`. Conclude with `h.symm`.
-/
private theorem exists_coords {K C V : Type} [Field K] [Ring C] [Algebra K C] [Algebra ℚ K] [Algebra ℚ C]
    [IsScalarTower ℚ K C] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [FiniteDimensional ℚ K]
    [FiniteDimensional K C] (n : ℕ)
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hinj : Function.Injective rep) (hC : Module.finrank K C = n ^ 2)
    (hdim : Module.finrank ℚ V = n * Module.finrank ℚ K) :
    ∃ (kp : V ≃+ (Fin n → K)) (σ : C ≃ₐ[K] Matrix (Fin n) (Fin n) K), ∀ c w, kp (rep c w) = σ c *ᵥ kp w := by
  let f : K →+* Module.End ℚ V := (rep : C →+* Module.End ℚ V).comp (algebraMap K C)
  letI : Module K V := Module.compHom V f
  have hsm : ∀ (x : K) (w : V), x • w = rep (algebraMap K C x) w := fun _ _ => rfl
  haveI : IsScalarTower ℚ K V := by
    refine ⟨fun q x w => ?_⟩
    rw [hsm, hsm, ← IsScalarTower.toAlgHom_apply ℚ K C, map_smul, map_smul]
    rfl
  haveI : Module.Finite K V := Module.Finite.of_restrictScalars_finite ℚ K V
  have hfin : Module.finrank K V = n := by
    have h := Module.finrank_mul_finrank ℚ K V
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hdim, mul_comm n] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  let b : Module.Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hfin
  let r : C →ₐ[K] Module.End K V := AlgHom.ofLinearMap
    { toFun := fun c =>
        { toFun := rep c
          map_add' := map_add _
          map_smul' := fun x w => by
            simp only [RingHom.id_apply, hsm]
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes] }
      map_add' := fun c c' => by ext w; simp
      map_smul' := fun x c => by
        ext w
        simp [hsm, Algebra.smul_def, Module.End.mul_apply] }
    (by ext w; simp) (fun c c' => by ext w; simp [Module.End.mul_apply])
  have hr : ∀ c w, r c w = rep c w := fun _ _ => rfl
  let s : C →ₐ[K] Matrix (Fin n) (Fin n) K := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp r
  have hsinj : Function.Injective s := by
    intro c c' h
    have h' : r c = r c' := (LinearMap.toMatrixAlgEquiv b).injective h
    apply hinj
    ext w
    exact congrArg (fun g => g w) h'
  have hrk : Module.finrank K C = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [hC, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
    ring
  have hsurj : Function.Surjective s :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := s.toLinearMap) hrk).1 hsinj
  refine ⟨b.equivFun.toAddEquiv, AlgEquiv.ofBijective s ⟨hsinj, hsurj⟩, fun c w => ?_⟩
  have h := LinearMap.toMatrix_mulVec_repr b b (r c) w
  exact h.symm

/- English proof (translation)
Introduce `p _ D G L hm`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Establish `hK : Module.finrank ℚ G.F = Module.finrank ℚ D.F` using `((AlgEquiv.ofRingEquiv (f := L.e) (fun q => map_ratCast L.e q)).toLinearEquiv.finrank_eq).symm`. Establish `hdim : Module.finrank ℚ (VQ D) = G.n * Module.finrank ℚ G.F`.

Rewrite using `[Module.finrank_baseChange, D.rankLa, hm, Nat.one_mul, L.n_eq, hK]`. Conclude with `exists_coords G.n L.rep L.rep_inj G.rankC hdim`.
-/
theorem UpperTheory.Gal.W2.fMat_of :
    UpperTheory.Gal.W2.FMat := by
  intro p _ D G L hm
  haveI := D.freeLa
  haveI := D.finLa
  have hK : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    ((AlgEquiv.ofRingEquiv (f := L.e) (fun q => map_ratCast L.e q)).toLinearEquiv.finrank_eq).symm
  have hdim : Module.finrank ℚ (VQ D) = G.n * Module.finrank ℚ G.F := by
    rw [Module.finrank_baseChange, D.rankLa, hm, Nat.one_mul, L.n_eq, hK]
  exact exists_coords G.n L.rep L.rep_inj G.rankC hdim
