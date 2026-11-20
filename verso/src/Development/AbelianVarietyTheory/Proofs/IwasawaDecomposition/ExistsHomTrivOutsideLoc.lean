import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitEmb
open GlobalTheory.SplitLift

section General
variable {n : ℕ} {K : Type*} (A : Type*) [CommRing K] [CommRing A]

def triMat (M : GL (Fin n) K) : Matrix (Fin n) (Fin n) (K × K × A) :=
  fun i j => ((M : Matrix (Fin n) (Fin n) K) i j, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i,
    (1 : Matrix (Fin n) (Fin n) A) i j)

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem triMat_one : triMat A (1 : GL (Fin n) K) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]
  split_ifs <;> rfl

/- English proof (translation)
Use `symm`. Apply `matrix_prod_ext` to reduce the goal to its premises. Conclude with `Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))`. Establish `e` using `Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))`. Use `e.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose * ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose = (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose`. Rewrite using `[mul_inv_rev, Units.val_mul, Matrix.transpose_mul]`. Establish `e` using `Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))`. Use `e.trans ?_` and prove the remaining obligations. Conclude with `Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)`.
-/
theorem triMat_mul (M N : GL (Fin n) K) : triMat A (M * N) = triMat A M * triMat A N := by
  symm
  apply matrix_prod_ext
  · exact Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    change ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *
      ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    exact Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)

end General

/- English proof (translation)
Introduce `L _ _ _ n s`. Take `⟨y, hy⟩` from `DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)`. Use `set δ : L := y - IsCMField.complexConj L y with hδdef`. Establish `hδ : IsCMField.complexConj L δ = -δ`. Rewrite using `[hδdef, map_sub, IsCMField.complexConj_apply_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hδ0 : δ ≠ 0` using `sub_ne_zero.2 (Ne.symm hy)`. Establish `hfix : IsCMField.complexConj L (δ * δ) = δ * δ` using `by rw [map_mul, hδ]; ring`. Set `d : maximalRealSubfield L` to `⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩`. Establish `hd : δ * δ = algebraMap (maximalRealSubfield L) L d` using `rfl`.

Establish `hr : s.i δ ≠ 0` using `(map_ne_zero _).2 hδ0`. Set `X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L)` to `fun M => (triMat (AL L) M).map (θ s δ d hd hr)`. Establish `hX1 : X 1 = 1` using `by show (triMat (AL L) 1).map (θ s δ d hd hr) = 1`. Rewrite using `[triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hXm : ∀ M N, X (M * N) = X M * X N` using `fun M N => by show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _`.

Rewrite using `[triMat_mul, Matrix.map_mul]`. Establish `hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹` using `fun M => by`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[conj_θ s δ d hd hr hδ]`.

Use `congr 1`. Use `Prod.ext rfl (Prod.ext rfl ?_)` and prove the remaining obligations. Simplify using `only [triMat, Matrix.one_apply, eq_comm (a := j)]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hX : ∀ M, X M * conjT (conjAL L) (X M) = 1` using `fun M => by`.

Rewrite using `[hconj, ← hXm, mul_inv_cancel, hX1]`. Set `e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n` to `{ toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩ map_one' := Subtype.ext (Units.ext hX1) map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }`. Use `⟨e, fun M w hw => ?_, fun M => ?_⟩` and prove the remaining obligations. Establish `hw' : w ≠ s.v` using `hw`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j`. Rewrite using `[compAt_θ s δ d hd hr _ hw']`. Simplify using `only [triMat, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _`. Rewrite using `[proj_θ]`. Both sides reduce to the same expression.
-/
theorem exists_hom_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    ∃ e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n,
      (∀ g, TrivOutside {s.v} (e g)) ∧ ∀ g, s.loc n (e g) = g := by
  intro L _ _ _ n s
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L) :=
    fun M => (triMat (AL L) M).map (θ s δ d hd hr)
  have hX1 : X 1 = 1 := by
    show (triMat (AL L) 1).map (θ s δ d hd hr) = 1
    rw [triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXm : ∀ M N, X (M * N) = X M * X N := fun M N => by
    show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _
    rw [triMat_mul, Matrix.map_mul]
  have hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹ := fun M => by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [triMat, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have hX : ∀ M, X M * conjT (conjAL L) (X M) = 1 := fun M => by
    rw [hconj, ← hXm, mul_inv_cancel, hX1]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩
      map_one' := Subtype.ext (Units.ext hX1)
      map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }
  refine ⟨e, fun M w hw => ?_, fun M => ?_⟩
  · have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [triMat, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _
    rw [proj_θ]
    rfl

end GlobalTheory.SplitEmb
