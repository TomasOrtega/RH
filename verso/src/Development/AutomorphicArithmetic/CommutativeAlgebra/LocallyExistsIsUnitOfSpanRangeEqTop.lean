import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Apply `T.toRingedSpace.isUnit_of_isUnit_germ` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `(T.mem_basicOpen f x trivial).1 (h hx)`.
-/
private theorem unit_on (T : Scheme.{0}) (f : Γ(T, ⊤)) (W : T.Opens) (h : W ≤ T.basicOpen f) :
    IsUnit ((T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact (T.mem_basicOpen f x trivial).1 (h hx)

/- English proof (translation)
Establish `hx : x ∈ (⨆ g ∈ Set.range v, T.basicOpen g)`. Rewrite using `[iSup_basicOpen_of_span_eq_top (X := T) ⊤ _ hv]`. Discharge the goal by the elementary cases of `trivial`. Simplify `hx` using `[TopologicalSpace.Opens.mem_iSup]`.
-/
private theorem unit_cover (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤))
    (hv : Ideal.span (Set.range v) = ⊤) (x : T) : ∃ i, x ∈ T.basicOpen (v i) := by
  have hx : x ∈ (⨆ g ∈ Set.range v, T.basicOpen g) := by
    rw [iSup_basicOpen_of_span_eq_top (X := T) ⊤ _ hv]
    trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

/- English proof (translation)
Introduce `T M v hv`. Set `S : Sieve T` to `{ arrows := fun V g => ∃ i, IsUnit (g.appTop.hom (v i)) downward_closed := by`. Introduce and unpack `Y Z g ⟨i, hi⟩ k`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`.

Conclude with `hi.map _ }`. Use `⟨S, ?_, fun V g hg => hg⟩` and prove the remaining obligations. Establish `hcov : TopologicalSpace.IsOpenCover (fun i : Fin M => T.basicOpen (v i))` using `eq_top_iff.2 (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (unit_cover T v hv x))`. Apply `Scheme.zariskiTopology_le_etaleTopology` to reduce the goal to its premises. Use `GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology (T.openCoverOfIsOpenCover _ hcov))` and prove the remaining obligations.

Introduce and unpack `Z g ⟨W, a, b, ⟨i⟩, rfl⟩`. Apply `S.downward_closed` to reduce the goal to its premises. Establish `hu` using `unit_on T (v i) ((T.basicOpen (v i)).ι ''ᵁ ⊤) (by rw [Scheme.Opens.ι_image_top])`. Conclude with `⟨i, hu⟩`.
-/
theorem UpperTheory.locally_exists_isUnit_of_span_range_eq_top :
    ∀ (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤)), Ideal.span (Set.range v) = ⊤ →
        Loc T fun V g => ∃ i, IsUnit (g.appTop.hom (v i)) := by
  intro T M v hv
  let S : Sieve T :=
    { arrows := fun V g => ∃ i, IsUnit (g.appTop.hom (v i))
      downward_closed := by
        rintro Y Z g ⟨i, hi⟩ k
        refine ⟨i, ?_⟩
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact hi.map _ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  have hcov : TopologicalSpace.IsOpenCover (fun i : Fin M => T.basicOpen (v i)) :=
    eq_top_iff.2 (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (unit_cover T v hv x))
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (T.openCoverOfIsOpenCover _ hcov))
  rintro Z g ⟨W, a, b, ⟨i⟩, rfl⟩
  apply S.downward_closed
  have hu := unit_on T (v i) ((T.basicOpen (v i)).ι ''ᵁ ⊤) (by rw [Scheme.Opens.ι_image_top])
  exact ⟨i, hu⟩
