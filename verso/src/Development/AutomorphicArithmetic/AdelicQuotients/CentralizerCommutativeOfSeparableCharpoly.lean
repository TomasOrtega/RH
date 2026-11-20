import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Establish `hl : ∀ (r : R) (x : F), φ (r * algebraMap F R x) = φ r * x`. Introduce `r x`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Establish `hr : ∀ (r : R) (x : F), φ (algebraMap F R x * r) = x * φ r`. Introduce `r x`.

Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`. Use `show s.map φ * γ = γ * s.map φ`. Use extensionality with `a c`. Establish `h` using `congrArg φ (congrFun (congrFun hs a) c)`. Simplify `h` using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, hl, hr]`.
-/
private theorem coord_comm {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (φ : R →ₗ[F] F) (s : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s) :
    Commute (s.map φ) γ := by
  have hl : ∀ (r : R) (x : F), φ (r * algebraMap F R x) = φ r * x := by
    intro r x
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hr : ∀ (r : R) (x : F), φ (algebraMap F R x * r) = x * φ r := by
    intro r x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  show s.map φ * γ = γ * s.map φ
  ext a c
  have h := congrArg φ (congrFun (congrFun hs a) c)
  simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, hl, hr] using h

/- English proof (translation)
Use extensionality with `a c`. Rewrite using `[Matrix.sum_apply]`. Use `conv_lhs => rw [← b.linearCombination_repr (s a c)]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hB a c) _ (by simp)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[Algebra.smul_def, mul_comm]`.
-/
private theorem coord_sum {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (b : Module.Basis ι F R) (B : Finset ι) (s : Matrix (Fin n) (Fin n) R)
    (hB : ∀ a c, (b.repr (s a c)).support ⊆ B) :
    s = ∑ i ∈ B, b i • (s.map (b.coord i)).map (algebraMap F R) := by
  ext a c
  rw [Matrix.sum_apply]
  conv_lhs => rw [← b.linearCombination_repr (s a c)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hB a c) _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

/- English proof (translation)
Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (e i), ← Matrix.map_mul, ← Matrix.map_mul, h]`.
-/
private theorem sum_comm_of {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (e : ι → R) (B : Finset ι) (S T : ι → Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, S i * T j = T j * S i) :
    (∑ i ∈ B, e i • (S i).map (algebraMap F R)) * (∑ j ∈ B, e j • (T j).map (algebraMap F R)) =
      (∑ j ∈ B, e j • (T j).map (algebraMap F R)) * (∑ i ∈ B, e i • (S i).map (algebraMap F R)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (e i), ← Matrix.map_mul, ← Matrix.map_mul, h]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace F R`. Set `B` to `Finset.univ.biUnion fun a => Finset.univ.biUnion fun c => (b.repr (s a c)).support ∪ (b.repr (t a c)).support`. Establish `hsB : ∀ a c, (b.repr (s a c)).support ⊆ B` using `fun a c i hi => Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_union_left _ hi⟩⟩`. Establish `htB : ∀ a c, (b.repr (t a c)).support ⊆ B` using `fun a c i hi => Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_union_right _ hi⟩⟩`. Establish `h` using `sum_comm_of (R := R) (fun i => b i) B (fun i => s.map (b.coord i)) (fun i => t.map (b.coord i)) fun i j => (UpperTheory.V.Z.Tf.Orb.centComm F n γ _ _ hγ (coord_comm γ _ s hs) (coord_comm γ _ t ht)).eq`.

Rewrite `h` using `[← coord_sum b B s hsB, ← coord_sum b B t htB]`. Then use the resulting hypothesis.
-/
private theorem comm_alg {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (hγ : γ.charpoly.Separable) (s t : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s)
    (ht : t * γ.map (algebraMap F R) = γ.map (algebraMap F R) * t) : s * t = t * s := by
  classical
  let b := Module.Basis.ofVectorSpace F R
  let B := Finset.univ.biUnion fun a => Finset.univ.biUnion fun c =>
    (b.repr (s a c)).support ∪ (b.repr (t a c)).support
  have hsB : ∀ a c, (b.repr (s a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_left _ hi⟩⟩
  have htB : ∀ a c, (b.repr (t a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_right _ hi⟩⟩
  have h := sum_comm_of (R := R) (fun i => b i) B (fun i => s.map (b.coord i))
    (fun i => t.map (b.coord i)) fun i j =>
      (UpperTheory.V.Z.Tf.Orb.centComm F n γ _ _ hγ (coord_comm γ _ s hs) (coord_comm γ _ t ht)).eq
  rwa [← coord_sum b B s hsB, ← coord_sum b B t htB] at h

/- English proof (translation)
Introduce `F R _ _ _ f n γ hγ s t hs ht`. Use `letI : Algebra F R := f.toAlgebra`. Conclude with `comm_alg γ hγ s t hs ht`.
-/
theorem UpperTheory.centralizer_commutative_of_separable_charpoly :
    CentComm := by
  intro F R _ _ _ f n γ hγ s t hs ht
  letI : Algebra F R := f.toAlgebra
  exact comm_alg γ hγ s t hs ht
