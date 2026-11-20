import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL GlobalTheory.UnitaryBC
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

/- English proof (translation)
Establish `h1` using `h 1 φ ψ`. Establish `hI` using `h Complex.I φ ψ`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smulₛₗ, one_smul, star_one, Complex.star_def, Complex.conj_I, map_neg, neg_smul, map_one, RingHom.id_apply, smul_eq_mul, Complex.conj_conj, LinearMap.neg_apply] at h1 hI`. Take the linear combination `(1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI + ((H (A φ) ψ + H φ (B ψ) - H (B φ) ψ - H φ (A ψ)) / 2) * Complex.I_sq`.
-/
private theorem adj_of_skew {M : Type} [AddCommGroup M] [Module ℂ M] (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (A B : Module.End ℂ M)
    (h : ∀ (z : ℂ) (φ ψ : M), H ((z • A + star z • B) φ) ψ + H φ ((z • A + star z • B) ψ) = 0)
    (φ ψ : M) : H (A φ) ψ = - H φ (B ψ) := by
  have h1 := h 1 φ ψ
  have hI := h Complex.I φ ψ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smulₛₗ, one_smul, star_one,
    Complex.star_def, Complex.conj_I, map_neg, neg_smul, map_one, RingHom.id_apply, smul_eq_mul,
    Complex.conj_conj, LinearMap.neg_apply] at h1 hI
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI +
    ((H (A φ) ψ + H φ (B ψ) - H (B φ) ψ - H φ (A ψ)) / 2) * Complex.I_sq

/- English proof (translation)
Rewrite using `[PositivityTheory.Rg.Cz.GK.lieOp_atEmb, Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Matrix.single_apply, hj.symm]`. Simplify using the standard rewrite rules.

Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Simplify using `[Matrix.single_apply, hi.symm]`. Simplify using the standard rewrite rules.
-/
private theorem lie_single {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (z : ℂ) :
    lieOp π (fun i j => atEmb τ (Matrix.single a b z i j)) =
      z • cx τ (lieOp π) a b + star z • cx (PositivityTheory.Rg.Cz.barE E τ) (lieOp π) a b := by
  rw [PositivityTheory.Rg.Cz.GK.lieOp_atEmb, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Matrix.single_apply, hj.symm]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, hi.symm]
  · simp

/- English proof (translation)
Rewrite using `[← GlobalTheory.WigCap.res_Eop]`. Both sides reduce to the same expression.
-/
private theorem cx_val {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (ψ : π.V) : (cx τ (lieOp π) a b ψ).1 = Eop τ a b ψ.1 := by
  rw [← GlobalTheory.WigCap.res_Eop]
  rfl

/- English proof (translation)
Introduce `h`. Establish `hc : w.IsComplex` using `IsTotallyComplex.isComplex w`. Conclude with `(InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)`.
-/
private theorem emb_ne {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc : w.IsComplex := IsTotallyComplex.isComplex w
  exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)

/- English proof (translation)
Introduce `a b c d`. Use `LinearMap.ext fun u => hJ ?_` and prove the remaining obligations. Establish `key` using `LinearMap.congr_fun (hF a b c d) (J u)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢`. Rewrite using `[map_sub, map_sub, h, h, h, h, key]`.

Apply the tactic sequence `split_ifs <;> simp [h]`.
-/
private theorem gl_pull {U M : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (J : U →ₗ[ℂ] M) (hJ : Function.Injective J) (e : Fin n → Fin n → Module.End ℂ U)
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) (h : ∀ a b u, J (e a b u) = F a b (J u)) : GlRel e := by
  intro a b c d
  refine LinearMap.ext fun u => hJ ?_
  have key := LinearMap.congr_fun (hF a b c d) (J u)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, map_sub, h, h, h, h, key]
  split_ifs <;> simp [h]

/- English proof (translation)
Introduce `a b c d`. Establish `key` using `hF b a d c`. Simplify using `only [neg_mul_neg]`. Rewrite using `[key]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a`.

Substitute `h1` using the available equality. Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish `h2' : ¬ a = d` using `fun h => h2 h.symm`.

Substitute `h1` using the available equality. Simplify using `[h2, h2']`. Substitute `h2` using the available equality. Establish `h1' : ¬ c = b` using `fun h => h1 h.symm`. Simplify using `[h1, h1']`.

Establish `h2' : ¬ a = d` using `fun h => h2 h.symm`. Establish `h1' : ¬ c = b` using `fun h => h1 h.symm`. Simplify using `[h1, h1', h2, h2']`.
-/
private theorem gl_neg_swap {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) : GlRel (fun a b => -F b a) := by
  intro a b c d
  have key := hF b a d c
  simp only [neg_mul_neg]
  rw [key]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp; abel
  · have h2' : ¬ a = d := fun h => h2 h.symm
    subst h1
    simp [h2, h2']
  · subst h2
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1']
  · have h2' : ¬ a = d := fun h => h2 h.symm
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1', h2, h2']

end UpperTheory.V.Z.GSp4Splitting

/- English proof (translation)
Introduce `E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w`. Establish `hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding` using `emb_ne w`. Set `A : Fin n → Fin n → Module.End ℂ π.V` to `cx w.embedding (lieOp π)`. Set `B : Fin n → Fin n → Module.End ℂ π.V` to `cx (PositivityTheory.Rg.Cz.barE E w.embedding) (lieOp π)`. Establish `v1 : ∀ a b u, (D.i (D.E1 w a b u)).1 = Eop w.embedding a b (D.i u).1` using `fun a b u => D.hE1 w a b u`.

Establish `v2 : ∀ a b u, (D.i (D.E2 w a b u)).1 = -Eop (ComplexEmbedding.conjugate w.embedding) b a (D.i u).1` using `fun a b u => D.hE2 w a b u`. Establish `iE1 : ∀ a b u, D.i (D.E1 w a b u) = A a b (D.i u)` using `fun a b u => Subtype.ext ((v1 a b u).trans (cx_val π _ a b _).symm)`. Establish `iE2 : ∀ a b u, D.i (D.E2 w a b u) = -B b a (D.i u)` using `fun a b u => Subtype.ext ((v2 a b u).trans (congrArg Neg.neg (cx_val π _ b a _).symm))`. Establish `adjA : ∀ a b φ ψ, D.H (A a b φ) ψ = -D.H φ (B a b ψ)` using `fun a b => adj_of_skew D.H _ _ fun z φ ψ => by`. Rewrite using `[← lie_single]`.

Conclude with `D.pet.2.2.1 _ φ ψ`. Establish `adjB : ∀ a b φ ψ, D.H (B a b φ) ψ = -D.H φ (A a b ψ)` using `fun a b φ ψ => by`. Establish `h` using `congrArg (starRingEnd ℂ) (adjA a b ψ φ)`. Rewrite `h` using `[map_neg, D.pet.1, D.pet.1]`. Rewrite using `[h, neg_neg]`.

Establish `hJ : Function.Injective (π.V.subtype ∘ₗ D.i)` using `π.V.injective_subtype.comp D.inj`. Use `{ gl1 := ?_, gl2 := ?_, comm := ?_, unitK := ?_, unitP := ?_ }` and prove the remaining obligations. Conclude with `gl_pull _ hJ _ _ (glRel_Eop w.embedding) v1`. Conclude with `gl_pull _ hJ _ _ (gl_neg_swap _ (glRel_Eop (ComplexEmbedding.conjugate w.embedding))) v2`. Introduce `a b c d`.

Use `LinearMap.ext fun u => D.inj (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(D.i (D.E1 w a b (D.E2 w c d u))).1 = (D.i (D.E2 w c d (D.E1 w a b u))).1`. Rewrite using `[v1, v2, v2, v1, map_neg]`. Conclude with `congrArg Neg.neg (LinearMap.congr_fun (Eop_comm hne a b d c) (D.i u).1)`. Introduce `a b x y`.

Simplify using `only [kF, LinearMap.add_apply]`. Rewrite using `[D.inner_eq, D.inner_eq]`. Simplify using `only [map_add, iE1, iE2, map_neg, LinearMap.add_apply, LinearMap.neg_apply, adjA, adjB]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a b x y`.

Simplify using `only [pF, LinearMap.sub_apply]`. Rewrite using `[D.inner_eq, D.inner_eq]`. Simplify using `only [map_sub, iE1, iE2, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, adjA, adjB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.GSp4Splitting.rlPair :
    RlPair := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := emb_ne w
  let A : Fin n → Fin n → Module.End ℂ π.V := cx w.embedding (lieOp π)
  let B : Fin n → Fin n → Module.End ℂ π.V := cx (PositivityTheory.Rg.Cz.barE E w.embedding) (lieOp π)
  have v1 : ∀ a b u, (D.i (D.E1 w a b u)).1 = Eop w.embedding a b (D.i u).1 := fun a b u => D.hE1 w a b u
  have v2 : ∀ a b u, (D.i (D.E2 w a b u)).1 = -Eop (ComplexEmbedding.conjugate w.embedding) b a (D.i u).1 :=
    fun a b u => D.hE2 w a b u
  have iE1 : ∀ a b u, D.i (D.E1 w a b u) = A a b (D.i u) := fun a b u =>
    Subtype.ext ((v1 a b u).trans (cx_val π _ a b _).symm)
  have iE2 : ∀ a b u, D.i (D.E2 w a b u) = -B b a (D.i u) := fun a b u =>
    Subtype.ext ((v2 a b u).trans (congrArg Neg.neg (cx_val π _ b a _).symm))
  have adjA : ∀ a b φ ψ, D.H (A a b φ) ψ = -D.H φ (B a b ψ) := fun a b =>
    adj_of_skew D.H _ _ fun z φ ψ => by
      rw [← lie_single]
      exact D.pet.2.2.1 _ φ ψ
  have adjB : ∀ a b φ ψ, D.H (B a b φ) ψ = -D.H φ (A a b ψ) := fun a b φ ψ => by
    have h := congrArg (starRingEnd ℂ) (adjA a b ψ φ)
    rw [map_neg, D.pet.1, D.pet.1] at h
    rw [h, neg_neg]
  have hJ : Function.Injective (π.V.subtype ∘ₗ D.i) := π.V.injective_subtype.comp D.inj
  refine { gl1 := ?_, gl2 := ?_, comm := ?_, unitK := ?_, unitP := ?_ }
  · exact gl_pull _ hJ _ _ (glRel_Eop w.embedding) v1
  · exact gl_pull _ hJ _ _ (gl_neg_swap _ (glRel_Eop (ComplexEmbedding.conjugate w.embedding))) v2
  · intro a b c d
    refine LinearMap.ext fun u => D.inj (Subtype.ext ?_)
    change (D.i (D.E1 w a b (D.E2 w c d u))).1 = (D.i (D.E2 w c d (D.E1 w a b u))).1
    rw [v1, v2, v2, v1, map_neg]
    exact congrArg Neg.neg (LinearMap.congr_fun (Eop_comm hne a b d c) (D.i u).1)
  · intro a b x y
    simp only [kF, LinearMap.add_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_add, iE1, iE2, map_neg, LinearMap.add_apply, LinearMap.neg_apply, adjA, adjB]
    ring
  · intro a b x y
    simp only [pF, LinearMap.sub_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_sub, iE1, iE2, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, adjA, adjB]
    ring
