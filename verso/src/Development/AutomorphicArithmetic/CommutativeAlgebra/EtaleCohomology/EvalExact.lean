import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull

open CategoryTheory

namespace UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Establish `hB` using `h.map_of_exact ((evaluation C AddCommGrpCat.{1}).obj B)`. Establish `hm` using `hB.mono_f`. Establish `he` using `hB.epi_g`. Conclude with `⟨(ShortComplex.ab_exact_iff_function_exact _).1 hB.exact, (AddCommGrpCat.mono_iff_injective _).1 hm, (AddCommGrpCat.epi_iff_surjective _).1 he⟩`.
-/
private lemma evalExact {C : Type 1} [Category.{0} C] (S : ShortComplex (Coef C))
    (h : S.ShortExact) (B : C) :
    Function.Exact (S.f.app B).hom (S.g.app B).hom ∧
      Function.Injective (S.f.app B).hom ∧ Function.Surjective (S.g.app B).hom := by
  have hB := h.map_of_exact ((evaluation C AddCommGrpCat.{1}).obj B)
  have hm := hB.mono_f
  have he := hB.epi_g
  exact ⟨(ShortComplex.ab_exact_iff_function_exact _).1 hB.exact,
    (AddCommGrpCat.mono_iff_injective _).1 hm, (AddCommGrpCat.epi_iff_surjective _).1 he⟩

end UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Introduce `C _ Pa S hS h1 h2 A T hT`. Establish `ex` using `fun B => UpperTheory.Ru.crystallineComparison.evalExact S hS B`. Establish `natf : ∀ (i : T.ι) (z : S.X₁.obj A), (S.f.app (T.B i)).hom ((S.X₁.map (T.f i)).hom z) = (S.X₂.map (T.f i)).hom ((S.f.app A).hom z)`. Introduce `i z`. Use `congrArg (fun φ => φ.hom z) (S.f.naturality (T.f i))` as an intermediate fact.

Simplify using `using this`. Establish `natg : ∀ (i : T.ι) (y : S.X₂.obj A), (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) = (S.X₃.map (T.f i)).hom ((S.g.app A).hom y)`. Introduce `i y`. Use `congrArg (fun φ => φ.hom y) (S.g.naturality (T.f i))` as an intermediate fact. Simplify using `using this`.

Establish `inj0 : ∀ x : S.X₃.obj A, (∀ i, (S.X₃.map (T.f i)).hom x = 0) → x = 0`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(ex A).2.2 x`. Establish `hz : ∀ i, ∃ z : S.X₁.obj (T.B i), (S.f.app (T.B i)).hom z = (S.X₂.map (T.f i)).hom y`. Introduce `i`.

Establish `: (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) = 0`. Rewrite using `[natg]`. Conclude with `hx i`. Conclude with `((ex (T.B i)).1 _).1 this`. Use `choose z hz using hz`.

Take `⟨w, hw⟩` from `(h1 A T hT).2 z`. Establish `hy : y = (S.f.app A).hom w`. Apply `(h2 A T hT).1` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `show (S.X₂.map (T.f i)).hom y = (S.X₂.map (T.f i)).hom ((S.f.app A).hom w)`.

Rewrite using `[← natf, ← hz i]`. Conclude with `congrArg _ (congrFun hw i).symm`. Rewrite using `[hy]`. Conclude with `((ex A).1 _).2 ⟨w, rfl⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `x x' e`. Rewrite using `[← sub_eq_zero]`. Apply `inj0` to reduce the goal to its premises. Introduce `i`. Use `congrFun e i` as an intermediate fact.

Simplify using `only at this`. Rewrite using `[map_sub, this, sub_self]`. Introduce `v`. Establish `hy : ∀ i, ∃ y : S.X₂.obj (T.B i), (S.g.app (T.B i)).hom y = v i` using `fun i => (ex (T.B i)).2.2 (v i)`. Use `choose y hy using hy`.

Take `⟨w, hw⟩` from `(h2 A T hT).2 y`. Use `⟨(S.g.app A).hom w, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show (S.X₃.map (T.f i)).hom ((S.g.app A).hom w) = v i`. Rewrite using `[← natg, ← hy i]`.

Conclude with `congrArg _ (congrFun hw i)`.
-/
theorem UpperTheory.Ru.crystallineComparison.quotAdd :
    UpperTheory.Ru.crystallineComparison.QuotAdd := by
  intro C _ Pa S hS h1 h2 A T hT
  have ex := fun B => UpperTheory.Ru.crystallineComparison.evalExact S hS B
  have natf : ∀ (i : T.ι) (z : S.X₁.obj A),
      (S.f.app (T.B i)).hom ((S.X₁.map (T.f i)).hom z) =
        (S.X₂.map (T.f i)).hom ((S.f.app A).hom z) := by
    intro i z
    have := congrArg (fun φ => φ.hom z) (S.f.naturality (T.f i))
    simpa using this
  have natg : ∀ (i : T.ι) (y : S.X₂.obj A),
      (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) =
        (S.X₃.map (T.f i)).hom ((S.g.app A).hom y) := by
    intro i y
    have := congrArg (fun φ => φ.hom y) (S.g.naturality (T.f i))
    simpa using this
  have inj0 : ∀ x : S.X₃.obj A, (∀ i, (S.X₃.map (T.f i)).hom x = 0) → x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (ex A).2.2 x
    have hz : ∀ i, ∃ z : S.X₁.obj (T.B i),
        (S.f.app (T.B i)).hom z = (S.X₂.map (T.f i)).hom y := by
      intro i
      have : (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) = 0 := by
        rw [natg]; exact hx i
      exact ((ex (T.B i)).1 _).1 this
    choose z hz using hz
    obtain ⟨w, hw⟩ := (h1 A T hT).2 z
    have hy : y = (S.f.app A).hom w := by
      apply (h2 A T hT).1
      funext i
      show (S.X₂.map (T.f i)).hom y = (S.X₂.map (T.f i)).hom ((S.f.app A).hom w)
      rw [← natf, ← hz i]
      exact congrArg _ (congrFun hw i).symm
    rw [hy]
    exact ((ex A).1 _).2 ⟨w, rfl⟩
  constructor
  · intro x x' e
    rw [← sub_eq_zero]
    apply inj0
    intro i
    have := congrFun e i
    simp only at this
    rw [map_sub, this, sub_self]
  · intro v
    have hy : ∀ i, ∃ y : S.X₂.obj (T.B i), (S.g.app (T.B i)).hom y = v i :=
      fun i => (ex (T.B i)).2.2 (v i)
    choose y hy using hy
    obtain ⟨w, hw⟩ := (h2 A T hT).2 y
    refine ⟨(S.g.app A).hom w, ?_⟩
    funext i
    show (S.X₃.map (T.f i)).hom ((S.g.app A).hom w) = v i
    rw [← natg, ← hy i]
    exact congrArg _ (congrFun hw i)
