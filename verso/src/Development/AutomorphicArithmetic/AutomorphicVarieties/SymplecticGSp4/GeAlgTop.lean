import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨g, rfl⟩` from `ha`.

Take `⟨h, rfl⟩` from `hb`. Conclude with `Submodule.subset_span ⟨g * h, map_mul r g h⟩`. Consider the case `zero => simp`. Consider the case `add b c _ _ hb hc => rw [mul_add]`. Conclude with `add_mem hb hc`.

Consider the case `smul c b _ hb => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hb`. Consider the case `zero => simp`. Consider the case `add b c _ _ hb hc => rw [add_mul]`. Conclude with `add_mem hb hc`.

Consider the case `smul c b _ hb => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ _ hb`.
-/
private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_mul {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K) {x y : M4 K}
    (hx : x ∈ Submodule.span K (Set.range r)) (hy : y ∈ Submodule.span K (Set.range r)) :
    x * y ∈ Submodule.span K (Set.range r) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, rfl⟩ := ha
      obtain ⟨h, rfl⟩ := hb
      exact Submodule.subset_span ⟨g * h, map_mul r g h⟩
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add b c _ _ hb hc => rw [add_mul]; exact add_mem hb hc
  | smul c b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[Matrix.matrix_eq_sum_single x]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `S.smul_mem (x i j) (h i j)` as an intermediate fact.

Simplify `this` using `[Matrix.smul_single]`.
-/
private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_top {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule K (Matrix n n K)) (h : ∀ i j, Matrix.single i j (1 : K) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have := S.smul_mem (x i j) (h i j)
  simpa [Matrix.smul_single] using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`. Establish `h1` using `geAlg_mul r (geAlg_mul r (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)`. Establish `h2` using `Submodule.smul_mem _ (r g i j)⁻¹ h1`. Rewrite `h2` using `[Matrix.single_mul_mul_single, Matrix.smul_single]`.

Simplify `h2` using `[hg]`. Introduce `h`. Assume the negation of the conclusion as `hn`. Establish `hz : ∀ g, r g i j = 0` using `fun g => by`. Assume the negation of the conclusion as `h'`.

Conclude with `hn ⟨g, h'⟩`. Establish `key : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha => obtain ⟨g, rfl⟩ := ha`.

Conclude with `hz g`. Consider the case `zero => rfl`. Consider the case `add b c _ _ hb hc => simp [hb, hc]`. Consider the case `smul c b _ hb => simp [hb]`. Simplify using `using key _ h`.
-/
private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_iff {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K)
    (he : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) (i j : Fin 4) :
    Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 := geAlg_mul r (geAlg_mul r (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)
    have h2 := Submodule.smul_mem _ (r g i j)⁻¹ h1
    rw [Matrix.single_mul_mul_single, Matrix.smul_single] at h2
    simpa [hg] using h2
  · intro h
    by_contra hn
    have hz : ∀ g, r g i j = 0 := fun g => by
      by_contra h'
      exact hn ⟨g, h'⟩
    have key : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem a ha => obtain ⟨g, rfl⟩ := ha; exact hz g
      | zero => rfl
      | add b c _ _ hb hc => simp [hb, hc]
      | smul c b _ hb => simp [hb]
    simpa using key _ h

/- English proof (translation)
Introduce `H _ K _ r ν hν he`. Establish `hiff` using `geAlg_iff r he`. Use `⟨hiff, fun i => (hiff i i).2 (he i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j k hij hjk`. Use `geAlg_mul r ((hiff i j).1 hij) ((hiff j k).1 hjk)` as an intermediate fact.

Rewrite `this` using `[Matrix.single_mul_single_same, mul_one]`. Conclude with `(hiff i k).2 this`. Introduce and unpack `i j ⟨g, hg⟩`. Use `⟨g⁻¹, fun h0 => hg ?_⟩` and prove the remaining obligations. Establish `h1 : adj (r g) = ν g • r g⁻¹`.

Establish `h2 : adj (r g) * r g * r g⁻¹ = ν g • (1 : M4 K) * r g⁻¹` using `by rw [hν g]`. Rewrite `h2` using `[mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, smul_mul_assoc, one_mul]`. Then use the resulting hypothesis. Establish `h3` using `congrFun (congrFun h1 j.rev) i.rev`. Rewrite `h3` using `[adj_apply, Fin.rev_rev, Fin.rev_rev, Matrix.smul_apply, h0, smul_zero]`. Establish `h4 : ∀ a b : Fin 4, sgn a * sgn b = 1 ∨ sgn a * sgn b = -1` using `by decide`.

Apply the tactic sequence `rcases h4 j.rev i.rev with h | h <;> rw [h] at h3 <;> simpa using h3`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Rewrite using `[hiff, h]`. Discharge the goal by the elementary cases of `trivial`.

Introduce `h`. Conclude with `geAlg_top _ fun i j => (hiff i j).1 (h i j)`. Introduce `h02 h20 _`. Set `f : M4 K →ₗ[K] Matrix (Fin 2) (Fin 2) K` to `{ toFun := fun x => x.submatrix ixA ixA map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hm : ∀ x ∈ Submodule.span K (Set.range r), f x ∈ Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA)`.

Introduce `x hx`. Use `Submodule.mem_map_of_mem (f := f) hx` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, ← Set.range_comp]`. Then use the resulting hypothesis. Establish `hs : ∀ a b : Fin 2, f (Matrix.single (ixA a) (ixA b) (1 : K)) = Matrix.single a b 1`. Introduce `a b`.

Use extensionality with `c d`. Establish `hinj : ∀ a b : Fin 2, ixA a = ixA b ↔ a = b` using `by decide`. Use `show Matrix.single (ixA a) (ixA b) (1 : K) (ixA c) (ixA d) = _`. Simplify using `only [Matrix.single_apply, hinj]`. Use `geAlg_top _ fun a b => ?_` and prove the remaining obligations.

Rewrite using `[← hs]`. Apply `hm` to reduce the goal to its premises. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Conclude with `he 0`. Conclude with `(hiff 0 2).1 h02`.

Conclude with `(hiff 2 0).1 h20`. Conclude with `he 2`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg :
    ∀ {H : Type} [Group H] (K : Type) [Field K] (r : H →* M4 K) (ν : H → K), (∀ g, IsGSp (ν g) (r g)) → (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) → (∀ i j, Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r)) ∧ (∀ i, Ge r i i) ∧ (∀ i j k, Ge r i j → Ge r j k → Ge r i k) ∧ (∀ i j, Ge r i j → Ge r j.rev i.rev) ∧ (Irr r ↔ ∀ i j, Ge r i j) ∧ (Ge r 0 2 → Ge r 2 0 → (∀ g, IsBlock (r g)) → Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) = ⊤) := by
  intro H _ K _ r ν hν he
  have hiff := geAlg_iff r he
  refine ⟨hiff, fun i => (hiff i i).2 (he i), ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have := geAlg_mul r ((hiff i j).1 hij) ((hiff j k).1 hjk)
    rw [Matrix.single_mul_single_same, mul_one] at this
    exact (hiff i k).2 this
  · rintro i j ⟨g, hg⟩
    refine ⟨g⁻¹, fun h0 => hg ?_⟩
    have h1 : adj (r g) = ν g • r g⁻¹ := by
      have h2 : adj (r g) * r g * r g⁻¹ = ν g • (1 : M4 K) * r g⁻¹ := by rw [hν g]
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, smul_mul_assoc, one_mul] at h2
    have h3 := congrFun (congrFun h1 j.rev) i.rev
    rw [adj_apply, Fin.rev_rev, Fin.rev_rev, Matrix.smul_apply, h0, smul_zero] at h3
    have h4 : ∀ a b : Fin 4, sgn a * sgn b = 1 ∨ sgn a * sgn b = -1 := by decide
    rcases h4 j.rev i.rev with h | h <;> rw [h] at h3 <;> simpa using h3
  · constructor
    · intro h i j
      rw [hiff, h]
      trivial
    · intro h
      exact geAlg_top _ fun i j => (hiff i j).1 (h i j)
  · intro h02 h20 _
    let f : M4 K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
      { toFun := fun x => x.submatrix ixA ixA
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hm : ∀ x ∈ Submodule.span K (Set.range r),
        f x ∈ Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) := by
      intro x hx
      have := Submodule.mem_map_of_mem (f := f) hx
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hs : ∀ a b : Fin 2, f (Matrix.single (ixA a) (ixA b) (1 : K)) = Matrix.single a b 1 := by
      intro a b
      ext c d
      have hinj : ∀ a b : Fin 2, ixA a = ixA b ↔ a = b := by decide
      show Matrix.single (ixA a) (ixA b) (1 : K) (ixA c) (ixA d) = _
      simp only [Matrix.single_apply, hinj]
    refine geAlg_top _ fun a b => ?_
    rw [← hs]
    apply hm
    fin_cases a <;> fin_cases b
    · exact he 0
    · exact (hiff 0 2).1 h02
    · exact (hiff 2 0).1 h20
    · exact he 2
