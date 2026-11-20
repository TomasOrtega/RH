import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.ClozelCohomologicalOf

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

/- English proof (translation)
Use `delta GlobalTheory.CuspRep.coord`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem coord_eq {E : Type} [Field E] (τ : E →+* ℂ) (c : Cinf E) :
    coord τ c = if (InfinitePlace.mk τ).embedding = τ then c (InfinitePlace.mk τ)
      else starRingEnd ℂ (c (InfinitePlace.mk τ)) := by
  delta GlobalTheory.CuspRep.coord
  split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[coord_eq, coord_eq]`. Apply the tactic sequence `split_ifs <;> simp [Pi.star_apply]`.
-/
theorem coord_star {E : Type} [Field E] (τ : E →+* ℂ) (c : Cinf E) :
    coord τ (star c) = star (coord τ c) := by
  rw [coord_eq, coord_eq]
  split_ifs <;> simp [Pi.star_apply]

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate τ ≠ τ`. Introduce `h`. Establish `hc` using `IsTotallyComplex.isComplex (InfinitePlace.mk τ)`. Rewrite `hc` using `[InfinitePlace.isComplex_mk_iff]`. Conclude with `hc (ComplexEmbedding.isReal_iff.2 h)`.

Establish `hcase` using `InfinitePlace.embedding_mk_eq τ`. Rewrite using `[coord_eq, coord_eq, InfinitePlace.mk_conjugate_eq]`. Use `split_ifs with h1 h2 h2`. Conclude with `absurd (h1.symm.trans h2) hne`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Break down `hcase with h | h` into its components or cases. Conclude with `absurd h h2`. Conclude with `absurd h h1`.
-/
theorem coord_conjugate {E : Type} [Field E] [IsTotallyComplex E] (τ : E →+* ℂ) (c : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) c = star (coord τ c) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := by
    intro h
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk τ)
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.2 h)
  have hcase := InfinitePlace.embedding_mk_eq τ
  rw [coord_eq, coord_eq, InfinitePlace.mk_conjugate_eq]
  split_ifs with h1 h2 h2
  · exact absurd (h1.symm.trans h2) hne
  · simp
  · simp
  · rcases hcase with h | h
    · exact absurd h h2
    · exact absurd h h1

/- English proof (translation)
Rewrite using `[coord_eq, InfinitePlace.mk_embedding, if_pos rfl]`.
-/
theorem coord_embedding {E : Type} [Field E] (w : InfinitePlace E) (c : Cinf E) :
    coord w.embedding c = c w := by
  rw [coord_eq, InfinitePlace.mk_embedding, if_pos rfl]

/- English proof (translation)
Establish `e : (coord τ : Cinf E → ℂ) = fun c => if (InfinitePlace.mk τ).embedding = τ then c (InfinitePlace.mk τ) else starRingEnd ℂ (c (InfinitePlace.mk τ))` using `funext (coord_eq τ)`. Rewrite using `[e]`. Distinguish the cases in `h : (InfinitePlace.mk τ).embedding = τ`. Simplify using `only [if_pos h]`. Conclude with `continuous_apply _`.

Simplify using `only [if_neg h]`. Conclude with `Complex.continuous_conj.comp (continuous_apply _)`.
-/
theorem continuous_coord {E : Type} [Field E] (τ : E →+* ℂ) : Continuous (coord τ : Cinf E → ℂ) := by
  have e : (coord τ : Cinf E → ℂ) = fun c => if (InfinitePlace.mk τ).embedding = τ then
      c (InfinitePlace.mk τ) else starRingEnd ℂ (c (InfinitePlace.mk τ)) := funext (coord_eq τ)
  rw [e]
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · simp only [if_pos h]
    exact continuous_apply _
  · simp only [if_neg h]
    exact Complex.continuous_conj.comp (continuous_apply _)

/- English proof (translation)
Establish `hK : IsCompact ((Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : InfinitePlace E => Metric.closedBall (0 : ℂ) 1) : Set (Matrix (Fin a) (Fin a) (Cinf E)))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Use `IsCompact.of_isClosed_subset hK ?_ ?_` and prove the remaining obligations. Establish `h1 : IsClosed {M : Matrix (Fin a) (Fin a) (Cinf E) | M * star M = 1}` using `isClosed_eq (continuous_id.mul continuous_star) continuous_const`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `M`.

Conclude with `Matrix.mem_unitaryGroup_iff`. Introduce `M hM i _ j _ w _`. Establish `hw : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M ∈ Matrix.unitaryGroup (Fin a) ℂ`. Establish `hM' : M * star M = 1` using `Matrix.mem_unitaryGroup_iff.1 hM`. Rewrite using `[Matrix.mem_unitaryGroup_iff]`.

Establish `hs : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix (star M) = star ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M)`. Use extensionality with `i' j'`. Simplify using `[Matrix.star_apply]`. Rewrite using `[← hs, ← map_mul, hM', map_one]`. Establish `hb` using `entry_norm_bound_of_unitary hw i j`.

Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Simplify using `using hb`.
-/
theorem isCompact_unitaryGroup (E : Type) [Field E] (a : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) := by
  have hK : IsCompact ((Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
      Set.univ.pi fun _ : InfinitePlace E => Metric.closedBall (0 : ℂ) 1) :
        Set (Matrix (Fin a) (Fin a) (Cinf E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hK ?_ ?_
  · have h1 : IsClosed {M : Matrix (Fin a) (Fin a) (Cinf E) | M * star M = 1} :=
      isClosed_eq (continuous_id.mul continuous_star) continuous_const
    convert h1 using 1
    ext M
    exact Matrix.mem_unitaryGroup_iff
  · intro M hM i _ j _ w _
    have hw : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M ∈
        Matrix.unitaryGroup (Fin a) ℂ := by
      have hM' : M * star M = 1 := Matrix.mem_unitaryGroup_iff.1 hM
      rw [Matrix.mem_unitaryGroup_iff]
      have hs : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix (star M) =
          star ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M) := by
        ext i' j'
        simp [Matrix.star_apply]
      rw [← hs, ← map_mul, hM', map_one]
    have hb := entry_norm_bound_of_unitary hw i j
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hb

/- English proof (translation)
Introduce `E _ _ _ a`. Use `⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `τ`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Introduce `τ h`. Establish `h1 : (InfinitePlace.mk τ).IsReal` using `InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1`. Introduce `τ show (1 : Matrix (Fin a) (Fin a) (Cinf E)).map (coord τ) = 1`. Conclude with `(coord τ).mapMatrix.map_one`.

Introduce `τ γ δ show (γ.1 * δ.1).map (coord τ) = γ.1.map (coord τ) * δ.1.map (coord τ)`. Conclude with `Matrix.map_mul`. Introduce `τ γ`. Establish `hu : γ.1 * star γ.1 = 1` using `Matrix.mem_unitaryGroup_iff.1 γ.2`. Establish `e : (γ.1.map (coord τ))ᴴ = (star γ.1).map (coord τ)`.

Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, Matrix.star_apply, coord_star]`. Use `show γ.1.map (coord τ) * (γ.1.map (coord τ))ᴴ = 1`. Rewrite using `[e, ← Matrix.map_mul, hu]`. Conclude with `(coord τ).mapMatrix.map_one`.

Introduce `τ γ i j show coord (ComplexEmbedding.conjugate τ) (γ.1 i j) = star (coord τ (γ.1 i j))`. Conclude with `coord_conjugate τ _`. Introduce `τ i j show Continuous fun γ : Kinf E a => coord τ (γ.1 i j)`. Conclude with `(continuous_coord τ).comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))`. Introduce `γ δ h`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j w`. Use `congrFun (congrFun (h w.embedding) i) j` as an intermediate fact. Simplify `this` using `[kap, Matrix.map_apply, coord_embedding]`. Conclude with `isCompact_iff_compactSpace.1 (isCompact_unitaryGroup E a)`.
-/
theorem kData_holds : KData := by
  intro E _ _ _ a
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro τ; ext x; simp
  · intro τ h
    have h1 : (InfinitePlace.mk τ).IsReal :=
      InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1
  · intro τ
    show (1 : Matrix (Fin a) (Fin a) (Cinf E)).map (coord τ) = 1
    exact (coord τ).mapMatrix.map_one
  · intro τ γ δ
    show (γ.1 * δ.1).map (coord τ) = γ.1.map (coord τ) * δ.1.map (coord τ)
    exact Matrix.map_mul
  · intro τ γ
    have hu : γ.1 * star γ.1 = 1 := Matrix.mem_unitaryGroup_iff.1 γ.2
    have e : (γ.1.map (coord τ))ᴴ = (star γ.1).map (coord τ) := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.star_apply, coord_star]
    show γ.1.map (coord τ) * (γ.1.map (coord τ))ᴴ = 1
    rw [e, ← Matrix.map_mul, hu]
    exact (coord τ).mapMatrix.map_one
  · intro τ γ i j
    show coord (ComplexEmbedding.conjugate τ) (γ.1 i j) = star (coord τ (γ.1 i j))
    exact coord_conjugate τ _
  · intro τ i j
    show Continuous fun γ : Kinf E a => coord τ (γ.1 i j)
    exact (continuous_coord τ).comp
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
  · intro γ δ h
    apply Subtype.ext
    ext i j w
    have := congrFun (congrFun (h w.embedding) i) j
    simpa [kap, Matrix.map_apply, coord_embedding] using this
  · exact isCompact_iff_compactSpace.1 (isCompact_unitaryGroup E a)

end PositivityTheory.Rg.Cz.J

end
