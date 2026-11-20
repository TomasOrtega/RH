import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.GrDeg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

abbrev FV (ι : K → Type) (ι₂ : K₂ → Type) : Type :=
  Σ k : FibreBlock (Sum.inl : K → K ⊕ K₂), fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k

def fb (k₂ : K₂) : FibreBlock (Sum.inl : K → K ⊕ K₂) := ⟨Sum.inr k₂, by simp⟩

def fib (p : Σ k₂, ι₂ k₂) : FV ι ι₂ := ⟨fb p.1, p.2⟩

def unfib : FV ι ι₂ → Σ k₂, ι₂ k₂
  | ⟨⟨.inl k, h⟩, _⟩ => (h ⟨k, rfl⟩).elim
  | ⟨⟨.inr k₂, _⟩, j⟩ => ⟨k₂, j⟩

/- English proof (translation)
Break down `q with ⟨⟨k | k₂, h⟩, j⟩` into its components or cases. Conclude with `(h ⟨k, rfl⟩).elim`. Both sides reduce to the same expression.
-/
theorem fib_unfib (q : FV ι ι₂) : fib (unfib q) = q := by
  rcases q with ⟨⟨k | k₂, h⟩, j⟩
  · exact (h ⟨k, rfl⟩).elim
  · rfl

/- English proof (translation)
Break down `p with ⟨k₂, j⟩` into its components or cases. Both sides reduce to the same expression.
-/
@[simp] theorem unfib_fib (p : Σ k₂, ι₂ k₂) : unfib (fib p : FV ι ι₂) = p := by
  rcases p with ⟨k₂, j⟩
  rfl

variable {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}

def xf (G : GenFibre inlV (graphIdeal P g)) : FV ι ι₂ → G.Φ' :=
  fun q => G.x' ⟨q.1.1, q.2⟩

def J (G : GenFibre inlV (graphIdeal P g)) :
    MRing (Sum.elim ι ι₂) →+* MvPolynomial (FV ι ι₂) G.Φ :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (G.x ⟨k, i⟩)
    | ⟨.inr k, j⟩ => X (fib ⟨k, j⟩)

/- English proof (translation)
Establish `h : (J G).comp (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)).toRingHom = (C : G.Φ →+* MvPolynomial (FV ι ι₂) G.Φ).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using the standard rewrite rules. Introduce and unpack `⟨k, i⟩`.

Simplify using `[J, inlV]`. Conclude with `congrArg (fun f => f u) h`.
-/
theorem J_rename (G : GenFibre inlV (graphIdeal P g)) (u : MRing ι) :
    J G (rename inlV u) = C (aeval G.x u) := by
  have h : (J G).comp (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)).toRingHom =
      (C : G.Φ →+* MvPolynomial (FV ι ι₂) G.Φ).comp
        (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · rintro ⟨k, i⟩
      simp [J, inlV]
  exact congrArg (fun f => f u) h

/- English proof (translation)
Establish `h : (aeval (xf G) : MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ').toRingHom.comp (J G) = (aeval G.x' : MRing (Sum.elim ι ι₂) →ₐ[ℤ] G.Φ').toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using the standard rewrite rules. Introduce and unpack `⟨k | k, i⟩`.

Use `G.compat ⟨k, i⟩` as an intermediate fact. Simplify using `only [inlV] at this`. Simplify using `[J, this]`. Simplify using `[J, xf, fib, fb]`. Conclude with `congrArg (fun f => f F) h`.
-/
theorem aeval_J (G : GenFibre inlV (graphIdeal P g)) (F : MRing (Sum.elim ι ι₂)) :
    aeval (xf G) (J G F) = aeval G.x' F := by
  have h : (aeval (xf G) : MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ').toRingHom.comp (J G) =
      (aeval G.x' : MRing (Sum.elim ι ι₂) →ₐ[ℤ] G.Φ').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · rintro ⟨k | k, i⟩
      · have := G.compat ⟨k, i⟩
        simp only [inlV] at this
        simp [J, this]
      · simp [J, xf, fib, fb]
  exact congrArg (fun f => f F) h

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Take `⟨u, v, hv, rfl⟩` from `G.gen a`. Use `⟨v, rename inlV u, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[J_rename, ← C_mul, mul_div_cancel₀ _ hv]`.

Consider the case `add f₁ f₂ h₁ h₂`. Take `⟨d₁, F₁, n₁, e₁⟩` from `h₁`. Take `⟨d₂, F₂, n₂, e₂⟩` from `h₂`. Use `⟨d₁ * d₂, rename inlV d₂ * F₁ + rename inlV d₁ * F₂, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using And.intro n₁ n₂`.

Rewrite using `[map_add (J G), map_mul (J G), map_mul (J G), J_rename, J_rename, ← e₁, ← e₂, map_mul (aeval G.x), map_mul C]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f q h`. Take `⟨d, F, n, e⟩` from `h`. Use `⟨d, F * X ⟨Sum.inr (unfib q).1, (unfib q).2⟩, n, ?_⟩` and prove the remaining obligations.

Establish `hq : J G (X ⟨Sum.inr (unfib q).1, (unfib q).2⟩) = X q`. Establish `: J G (X ⟨Sum.inr (unfib q).1, (unfib q).2⟩) = X (fib (unfib q))`. Simplify using `[J]`. Rewrite using `[this, fib_unfib]`. Rewrite using `[map_mul, ← e, hq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem clear_denoms (G : GenFibre inlV (graphIdeal P g))
    (f : MvPolynomial (FV ι ι₂) G.Φ) :
    ∃ (d : MRing ι) (F : MRing (Sum.elim ι ι₂)),
      (aeval G.x d : G.Φ) ≠ 0 ∧ C (aeval G.x d) * f = J G F := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨u, v, hv, rfl⟩ := G.gen a
    refine ⟨v, rename inlV u, hv, ?_⟩
    rw [J_rename, ← C_mul, mul_div_cancel₀ _ hv]
  | add f₁ f₂ h₁ h₂ =>
    obtain ⟨d₁, F₁, n₁, e₁⟩ := h₁
    obtain ⟨d₂, F₂, n₂, e₂⟩ := h₂
    refine ⟨d₁ * d₂, rename inlV d₂ * F₁ + rename inlV d₁ * F₂, ?_, ?_⟩
    · simpa using And.intro n₁ n₂
    · rw [map_add (J G), map_mul (J G), map_mul (J G), J_rename, J_rename, ← e₁, ← e₂,
        map_mul (aeval G.x), map_mul C]
      ring
  | mul_X f q h =>
    obtain ⟨d, F, n, e⟩ := h
    refine ⟨d, F * X ⟨Sum.inr (unfib q).1, (unfib q).2⟩, n, ?_⟩
    have hq : J G (X ⟨Sum.inr (unfib q).1, (unfib q).2⟩) = X q := by
      have : J G (X ⟨Sum.inr (unfib q).1, (unfib q).2⟩) = X (fib (unfib q)) := by
        simp [J]
      rw [this, fib_unfib]
    rw [map_mul, ← e, hq]
    ring

/- English proof (translation)
Establish `h : (graphMap P g).comp (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)).toRingHom = (C : (MRing ι ⧸ P) →+* MvPolynomial K₂ (MRing ι ⧸ P)).comp (Ideal.Quotient.mk P)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using the standard rewrite rules. Introduce and unpack `⟨k, i⟩`.

Simplify using `[graphMap, inlV]`. Conclude with `congrArg (fun f => f u) h`.
-/
theorem graphMap_rename (u : MRing ι) :
    graphMap P g (rename inlV u) = C (Ideal.Quotient.mk P u) := by
  have h : (graphMap P g).comp (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)).toRingHom =
      (C : (MRing ι ⧸ P) →+* MvPolynomial K₂ (MRing ι ⧸ P)).comp (Ideal.Quotient.mk P) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · rintro ⟨k, i⟩
      simp [graphMap, inlV]
  exact congrArg (fun f => f u) h

/- English proof (translation)
Rewrite using `[graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_rename, graphMap_rename]`. Establish `e : ∀ l : ι₂ k, graphMap P g (X ⟨Sum.inr k, l⟩) = C (Ideal.Quotient.mk P (g ⟨k, l⟩)) * X k`. Introduce `l`. Simplify using `[graphMap]`. Rewrite using `[e, e]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_graph (k : K₂) (j j' : ι₂ k) :
    rename inlV (g ⟨k, j⟩) * X ⟨Sum.inr k, j'⟩ - rename inlV (g ⟨k, j'⟩) * X ⟨Sum.inr k, j⟩ ∈
      graphIdeal P g := by
  rw [graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_rename, graphMap_rename]
  have e : ∀ l : ι₂ k, graphMap P g (X ⟨Sum.inr k, l⟩) =
      C (Ideal.Quotient.mk P (g ⟨k, l⟩)) * X k := by
    intro l
    simp [graphMap]
  rw [e, e]
  ring

def av (G : GenFibre inlV (graphIdeal P g)) (p : Σ k, ι₂ k) : G.Φ := aeval G.x (g p)

/- English proof (translation)
Establish `hJ : J G (rename inlV (g ⟨k, j⟩) * X ⟨Sum.inr k, j'⟩ - rename inlV (g ⟨k, j'⟩) * X ⟨Sum.inr k, j⟩) = C (av G ⟨k, j⟩) * X (fib ⟨k, j'⟩) - C (av G ⟨k, j'⟩) * X (fib ⟨k, j⟩)`. Rewrite using `[map_sub, map_mul, map_mul, J_rename, J_rename]`. Simplify using `[J, av]`. Establish `h` using `rel_graph (P := P) (g := g) k j j'`. Rewrite `h` using `[← G.genericFibre_ker_target, RingHom.mem_ker]`.

Rewrite using `[fibreIdeal, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `aeval (xf G) _ = 0`. Rewrite using `[← hJ, aeval_J]`. Conclude with `h`.
-/
theorem rel_fibre (G : GenFibre inlV (graphIdeal P g)) (k : K₂) (j j' : ι₂ k) :
    C (av G ⟨k, j⟩) * X (fib ⟨k, j'⟩) - C (av G ⟨k, j'⟩) * X (fib ⟨k, j⟩) ∈
      fibreIdeal (Sum.inl : K → K ⊕ K₂) G := by
  have hJ : J G (rename inlV (g ⟨k, j⟩) * X ⟨Sum.inr k, j'⟩ -
      rename inlV (g ⟨k, j'⟩) * X ⟨Sum.inr k, j⟩) =
      C (av G ⟨k, j⟩) * X (fib ⟨k, j'⟩) - C (av G ⟨k, j'⟩) * X (fib ⟨k, j⟩) := by
    rw [map_sub, map_mul, map_mul, J_rename, J_rename]
    simp [J, av]
  have h := rel_graph (P := P) (g := g) k j j'
  rw [← G.genericFibre_ker_target, RingHom.mem_ker] at h
  rw [fibreIdeal, RingHom.mem_ker]
  change aeval (xf G) _ = 0
  rw [← hJ, aeval_J]
  exact h

/- English proof (translation)
Rewrite using `[fibreIdeal, RingHom.mem_ker]`. Both sides reduce to the same expression.
-/
theorem mem_fibre_iff (G : GenFibre inlV (graphIdeal P g)) (f : MvPolynomial (FV ι ι₂) G.Φ) :
    f ∈ fibreIdeal (Sum.inl : K → K ⊕ K₂) G ↔ aeval (xf G) f = 0 := by
  rw [fibreIdeal, RingHom.mem_ker]
  rfl

/- English proof (translation)
Introduce `h0`. Take `⟨l, hl⟩` from `hg k`. Establish `h` using `(mem_fibre_iff G _).1 (rel_fibre G k j l)`. Rewrite `h` using `[map_sub, map_mul, map_mul, aeval_C, aeval_C, aeval_X, aeval_X, h0, map_zero, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero]`. Break down `h with h | h` into its components or cases.

Apply `hl` to reduce the goal to its premises. Establish `hm : g ⟨k, l⟩ ∈ RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ)`. Rewrite using `[RingHom.mem_ker]`. Conclude with `(map_eq_zero (algebraMap G.Φ G.Φ')).1 h`. Rewrite `hm` using `[G.ker_x, hP]`. Then use the resulting hypothesis.

Conclude with `hj h`.
-/
theorem av_ne (G : GenFibre inlV (graphIdeal P g))
    (hP : imageZ inlV (graphIdeal P g) = P) (hg : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P)
    (k : K₂) (j : ι₂ k) (hj : xf G (fib ⟨k, j⟩) ≠ 0) : av G ⟨k, j⟩ ≠ 0 := by
  intro h0
  obtain ⟨l, hl⟩ := hg k
  have h := (mem_fibre_iff G _).1 (rel_fibre G k j l)
  rw [map_sub, map_mul, map_mul, aeval_C, aeval_C, aeval_X, aeval_X, h0, map_zero, zero_mul,
    zero_sub, neg_eq_zero, mul_eq_zero] at h
  rcases h with h | h
  · apply hl
    have hm : g ⟨k, l⟩ ∈ RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ) := by
      rw [RingHom.mem_ker]
      exact (map_eq_zero (algebraMap G.Φ G.Φ')).1 h
    rwa [G.ker_x, hP] at hm
  · exact hj h

def Lq (G : GenFibre inlV (graphIdeal P g))
    (hP : imageZ inlV (graphIdeal P g) = P) : (MRing ι ⧸ P) →+* G.Φ :=
  Ideal.Quotient.lift P (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom fun a ha => by
    have hm : a ∈ RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ) := by
      rw [G.ker_x, hP]
      exact ha
    exact (RingHom.mem_ker).1 hm

def cpt (G : GenFibre inlV (graphIdeal P g)) (T : K₂ → G.Φ) : FV ι ι₂ → G.Φ :=
  fun q => av G (unfib q) * T (unfib q).1

/- English proof (translation)
Establish `h : (aeval (cpt G T) : MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ).toRingHom.comp (J G) = (eval₂Hom (Lq G hP) T).comp (graphMap P g)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using the standard rewrite rules. Introduce and unpack `⟨k | k, i⟩`.

Simplify using `[J, graphMap, Lq]`. Simplify using `[J, graphMap, Lq, cpt, av]`. Conclude with `congrArg (fun f => f F) h`.
-/
theorem aeval_cpt_J (G : GenFibre inlV (graphIdeal P g))
    (hP : imageZ inlV (graphIdeal P g) = P) (T : K₂ → G.Φ) (F : MRing (Sum.elim ι ι₂)) :
    aeval (cpt G T) (J G F) = eval₂Hom (Lq G hP) T (graphMap P g F) := by
  have h : (aeval (cpt G T) : MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ).toRingHom.comp (J G) =
      (eval₂Hom (Lq G hP) T).comp (graphMap P g) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · rintro ⟨k | k, i⟩
      · simp [J, graphMap, Lq]
      · simp [J, graphMap, Lq, cpt, av]
  exact congrArg (fun f => f F) h

/- English proof (translation)
Take `⟨d, F, n, e⟩` from `clear_denoms G f`. Establish `h1 : aeval G.x' F = 0`. Rewrite using `[← aeval_J, ← e, map_mul, (mem_fibre_iff G f).1 hf, mul_zero]`. Establish `h2 : F ∈ graphIdeal P g`. Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker]`.

Conclude with `h1`. Establish `h3 : graphMap P g F = 0` using `(RingHom.mem_ker).1 h2`. Establish `h4 : aeval (cpt G T) (J G F) = 0`. Rewrite using `[aeval_cpt_J G hP, h3, map_zero]`. Rewrite `h4` using `[← e, map_mul, aeval_C]`.

Conclude with `(mul_eq_zero.1 h4).resolve_left n`.
-/
theorem aeval_cpt_fibre (G : GenFibre inlV (graphIdeal P g))
    (hP : imageZ inlV (graphIdeal P g) = P) (T : K₂ → G.Φ)
    (f : MvPolynomial (FV ι ι₂) G.Φ) (hf : f ∈ fibreIdeal (Sum.inl : K → K ⊕ K₂) G) :
    aeval (cpt G T) f = 0 := by
  obtain ⟨d, F, n, e⟩ := clear_denoms G f
  have h1 : aeval G.x' F = 0 := by
    rw [← aeval_J, ← e, map_mul, (mem_fibre_iff G f).1 hf, mul_zero]
  have h2 : F ∈ graphIdeal P g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    exact h1
  have h3 : graphMap P g F = 0 := (RingHom.mem_ker).1 h2
  have h4 : aeval (cpt G T) (J G F) = 0 := by
    rw [aeval_cpt_J G hP, h3, map_zero]
  rw [← e, map_mul, aeval_C] at h4
  exact (mul_eq_zero.1 h4).resolve_left n

/- English proof (translation)
Use `set T : K₂ → G.Φ := fun k => (av G ⟨k, i (fb k)⟩)⁻¹ with hT`. Establish `hne : ∀ k, av G ⟨k, i (fb k)⟩ ≠ 0`. Introduce `k`. Apply `av_ne G hP hg` to reduce the goal to its premises. Introduce `h0`.

Apply `hi (fb k)` to reduce the goal to its premises. Rewrite using `[mem_fibre_iff, aeval_X]`. Conclude with `h0`. Establish `hX : ∀ q : FV ι ι₂, X q - C (cpt G T q) ∈ chartIdeal (fibreIdeal Sum.inl G) i`. Introduce `q`.

Rewrite using `[← fib_unfib q]`. Generalize the expression as in `unfib q = p`. Break down `p with ⟨k, j⟩` into its components or cases. Establish `r : C (av G ⟨k, i (fb k)⟩) * X (fib ⟨k, j⟩) - C (av G ⟨k, j⟩) * X (fib ⟨k, i (fb k)⟩) ∈ chartIdeal (fibreIdeal Sum.inl G) i` using `Ideal.mem_sup_left (rel_fibre G k (i (fb k)) j)`. Establish `s : X (fib ⟨k, i (fb k)⟩) - 1 ∈ chartIdeal (fibreIdeal Sum.inl G) i` using `Ideal.mem_sup_right (Ideal.subset_span ⟨fb k, rfl⟩)`.

Establish `one : (C (T k) * C (av G ⟨k, i (fb k)⟩) : MvPolynomial (FV ι ι₂) G.Φ) = 1`. Rewrite using `[← C_mul, hT, inv_mul_cancel₀ (hne k), C_1]`. Establish `e : (X (fib ⟨k, j⟩) - C (cpt G T (fib ⟨k, j⟩)) : MvPolynomial (FV ι ι₂) G.Φ) = C (T k) * (C (av G ⟨k, i (fb k)⟩) * X (fib ⟨k, j⟩) - C (av G ⟨k, j⟩) * X (fib ⟨k, i (fb k)⟩)) + C (av G ⟨k, j⟩) * C (T k) * (X (fib ⟨k, i (fb k)⟩) - 1)`. Establish `: cpt G T (fib ⟨k, j⟩) = av G ⟨k, j⟩ * T k` using `by simp [cpt]`. Rewrite using `[this, C_mul]`.

Take the linear combination `(-X (fib (ι := ι) ⟨k, j⟩)) * one`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ r) (Ideal.mul_mem_left _ _ s)`. Establish `hf : ∀ f : MvPolynomial (FV ι ι₂) G.Φ, f - C (aeval (cpt G T) f) ∈ chartIdeal (fibreIdeal Sum.inl G) i`. Introduce `f`.

Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add f₁ f₂ h₁ h₂`. Establish `: f₁ + f₂ - C (aeval (cpt G T) (f₁ + f₂)) = (f₁ - C (aeval (cpt G T) f₁)) + (f₂ - C (aeval (cpt G T) f₂))`. Rewrite using `[map_add, C_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ h₁ h₂`. Consider the case `mul_X f q h`. Establish `: f * X q - C (aeval (cpt G T) (f * X q)) = (f - C (aeval (cpt G T) f)) * X q + C (aeval (cpt G T) f) * (X q - C (cpt G T q))`.

Rewrite using `[map_mul, aeval_X, C_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ h) (Ideal.mul_mem_left _ _ (hX q))`. Apply `le_antisymm` to reduce the goal to its premises.

Use `sup_le (fun f h => aeval_cpt_fibre G hP T f h) (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Break down `k with ⟨k | k₂, h⟩` into its components or cases. Conclude with `(h ⟨k, rfl⟩).elim`. Establish `hc : cpt G T ⟨⟨Sum.inr k₂, h⟩, i ⟨Sum.inr k₂, h⟩⟩ = 1` using `mul_inv_cancel₀ (hne k₂)`.

Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_X, map_one, sub_eq_zero]`. Conclude with `hc`. Introduce `f h`. Establish `h0 : aeval (cpt G T) f = 0` using `(RingHom.mem_ker).1 h`. Use `hf f` as an intermediate fact.

Rewrite `this` using `[h0, C_0, sub_zero]`. Then use the resulting hypothesis.
-/
theorem chartIdeal_eq (G : GenFibre inlV (graphIdeal P g))
    (hg : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) (hP : imageZ inlV (graphIdeal P g) = P)
    (i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k)
    (hi : IsChart (fibreIdeal Sum.inl G) i) :
    chartIdeal (fibreIdeal Sum.inl G) i =
      RingHom.ker (aeval (cpt G fun k => (av G ⟨k, i (fb k)⟩)⁻¹) :
        MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ) := by
  set T : K₂ → G.Φ := fun k => (av G ⟨k, i (fb k)⟩)⁻¹ with hT
  have hne : ∀ k, av G ⟨k, i (fb k)⟩ ≠ 0 := by
    intro k
    apply av_ne G hP hg
    intro h0
    apply hi (fb k)
    rw [mem_fibre_iff, aeval_X]
    exact h0
  have hX : ∀ q : FV ι ι₂, X q - C (cpt G T q) ∈ chartIdeal (fibreIdeal Sum.inl G) i := by
    intro q
    rw [← fib_unfib q]
    generalize unfib q = p
    rcases p with ⟨k, j⟩
    have r : C (av G ⟨k, i (fb k)⟩) * X (fib ⟨k, j⟩) - C (av G ⟨k, j⟩) * X (fib ⟨k, i (fb k)⟩) ∈
        chartIdeal (fibreIdeal Sum.inl G) i :=
      Ideal.mem_sup_left (rel_fibre G k (i (fb k)) j)
    have s : X (fib ⟨k, i (fb k)⟩) - 1 ∈ chartIdeal (fibreIdeal Sum.inl G) i :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨fb k, rfl⟩)
    have one : (C (T k) * C (av G ⟨k, i (fb k)⟩) : MvPolynomial (FV ι ι₂) G.Φ) = 1 := by
      rw [← C_mul, hT, inv_mul_cancel₀ (hne k), C_1]
    have e : (X (fib ⟨k, j⟩) - C (cpt G T (fib ⟨k, j⟩)) : MvPolynomial (FV ι ι₂) G.Φ) =
        C (T k) * (C (av G ⟨k, i (fb k)⟩) * X (fib ⟨k, j⟩) -
            C (av G ⟨k, j⟩) * X (fib ⟨k, i (fb k)⟩)) +
          C (av G ⟨k, j⟩) * C (T k) * (X (fib ⟨k, i (fb k)⟩) - 1) := by
      have : cpt G T (fib ⟨k, j⟩) = av G ⟨k, j⟩ * T k := by simp [cpt]
      rw [this, C_mul]
      linear_combination (-X (fib (ι := ι) ⟨k, j⟩)) * one
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ r) (Ideal.mul_mem_left _ _ s)
  have hf : ∀ f : MvPolynomial (FV ι ι₂) G.Φ,
      f - C (aeval (cpt G T) f) ∈ chartIdeal (fibreIdeal Sum.inl G) i := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f₁ f₂ h₁ h₂ =>
      have : f₁ + f₂ - C (aeval (cpt G T) (f₁ + f₂)) =
          (f₁ - C (aeval (cpt G T) f₁)) + (f₂ - C (aeval (cpt G T) f₂)) := by
        rw [map_add, C_add]
        ring
      rw [this]
      exact Ideal.add_mem _ h₁ h₂
    | mul_X f q h =>
      have : f * X q - C (aeval (cpt G T) (f * X q)) =
          (f - C (aeval (cpt G T) f)) * X q +
            C (aeval (cpt G T) f) * (X q - C (cpt G T q)) := by
        rw [map_mul, aeval_X, C_mul]
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h) (Ideal.mul_mem_left _ _ (hX q))
  apply le_antisymm
  · refine sup_le (fun f h => aeval_cpt_fibre G hP T f h) (Ideal.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    rcases k with ⟨k | k₂, h⟩
    · exact (h ⟨k, rfl⟩).elim
    · have hc : cpt G T ⟨⟨Sum.inr k₂, h⟩, i ⟨Sum.inr k₂, h⟩⟩ = 1 := mul_inv_cancel₀ (hne k₂)
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_X, map_one, sub_eq_zero]
      exact hc
  · intro f h
    have h0 : aeval (cpt G T) f = 0 := (RingHom.mem_ker).1 h
    have := hf f
    rwa [h0, C_0, sub_zero] at this

/- English proof (translation)
Introduce `K _ ι _ K₂ _ ι₂ _ P g _ hg hP G i hi`. Rewrite using `[ptDeg, chartIdeal_eq G hg hP i hi]`. Establish `hs : Function.Surjective (aeval (cpt G fun k => (av G ⟨k, i (fb k)⟩)⁻¹) : MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ)` using `fun a => ⟨C a, by simp⟩`. Rewrite using `[(Ideal.quotientKerAlgEquivOfSurjective hs).toLinearEquiv.finrank_eq]`. Conclude with `Module.finrank_self G.Φ`.
-/
theorem graph_generic_fibre_ptDeg :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₂ : Type) [Fintype K₂]
      (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι),
      P.IsPrime → (∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) → imageZ inlV (graphIdeal P g) = P →
      ∀ (G : GenFibre inlV (graphIdeal P g))
        (i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k),
        IsChart (fibreIdeal Sum.inl G) i → ptDeg (fibreIdeal Sum.inl G) i = 1 := by
  intro K _ ι _ K₂ _ ι₂ _ P g _ hg hP G i hi
  rw [ptDeg, chartIdeal_eq G hg hP i hi]
  have hs : Function.Surjective (aeval (cpt G fun k => (av G ⟨k, i (fb k)⟩)⁻¹) :
      MvPolynomial (FV ι ι₂) G.Φ →ₐ[G.Φ] G.Φ) := fun a => ⟨C a, by simp⟩
  rw [(Ideal.quotientKerAlgEquivOfSurjective hs).toLinearEquiv.finrank_eq]
  exact Module.finrank_self G.Φ

end GlobalTheory.CompanionTheory.Ar.Giv.GrDeg
