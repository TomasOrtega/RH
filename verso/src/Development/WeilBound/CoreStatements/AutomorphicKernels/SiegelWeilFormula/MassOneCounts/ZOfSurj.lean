import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def zOf {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) : Fv F v ⊗[F] E :=
  ∑ k, ((w (0, k) : v.adicCompletionIntegers F) : Fv F v) • (Algebra.TensorProduct.basis (Fv F v) b) k

/- English proof (translation)
Unfold `zOf`. Rewrite using `[Module.Basis.repr_sum_self]`.
-/
private theorem tensorBasis_repr_zOf {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (zOf b v w) k = (w (0, k) : Fv F v) := by
  unfold zOf
  rw [Module.Basis.repr_sum_self]

/- English proof (translation)
Introduce `k`. Rewrite using `[tensorBasis_repr_zOf]`. Conclude with `(w (0, k)).2`.
-/
theorem zOf_mem {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) : zOf b v w ∈ Rv b v := by
  intro k
  rw [tensorBasis_repr_zOf]
  exact (w (0, k)).2

/- English proof (translation)
Use `⟨fun p => ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr z p.2, hz p.2⟩, ?_⟩` and prove the remaining obligations. Unfold `zOf`. Conclude with `(Algebra.TensorProduct.basis (Fv F v) b).sum_repr z`.
-/
theorem zOf_surj {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E)
    (hz : z ∈ Rv b v) : ∃ w, zOf b v w = z := by
  refine ⟨fun p => ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr z p.2, hz p.2⟩, ?_⟩
  unfold zOf
  exact (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z

/- English proof (translation)
The claim follows from `Valued.toNormedField.norm_lt_one_iff`.
-/
private theorem norm_lt_one_iff_valuation_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    ‖x‖ < 1 ↔ Valued.v x < 1 :=
  Valued.toNormedField.norm_lt_one_iff

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hd : ∀ p, ϖ ∣ w p - w' p` using `fun p => hϖd _ (by`. Rewrite using `[norm_lt_one_iff_valuation_lt_one]`. Use `push_cast`.

Conclude with `h p)`. Use `choose c hc using hd`. Use `⟨zOf b v c, zOf_mem b v c, ?_⟩` and prove the remaining obligations. Apply `(Algebra.TensorProduct.basis (Fv F v) b).repr.injective` to reduce the goal to its premises. Use extensionality with `k`.

Rewrite using `[← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, tensorBasis_repr_zOf, tensorBasis_repr_zOf, tensorBasis_repr_zOf, smul_eq_mul]`. Establish `hck` using `congrArg (fun t : v.adicCompletionIntegers F => (t : Fv F v)) (hc (0, k))`. Move the coercions through the operations in `at hck`. Use `first`. Consider the case `rw [hck]`.

Consider the case `(congr 1; exact hck)`. Consider the case `simpa using congrArg _ hck`. Introduce and unpack `⟨y, hy, hyeq⟩ ⟨i, k⟩`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Establish `hk` using `congrArg (fun x => (Algebra.TensorProduct.basis (Fv F v) b).repr x k) hyeq`.

Rewrite `hk` using `[← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, tensorBasis_repr_zOf, tensorBasis_repr_zOf, smul_eq_mul]`. Rewrite using `[hk, map_mul]`. Establish `h1 : Valued.v (ϖ : Fv F v) < 1` using `(norm_lt_one_iff_valuation_lt_one v _).mp hϖ1`. Establish `h2 : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr y k) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hy k)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem zOf_ker {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : (ϖ : Fv F v) ≠ 0) (hϖ1 : ‖(ϖ : Fv F v)‖ < 1)
    (hϖd : ∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x)
    (w w' : Fin 1 × Fin d → v.adicCompletionIntegers F) :
    (∀ p, Valued.v ((w p : Fv F v) - w' p) < 1) ↔
      ∃ y ∈ Rv b v, zOf b v w - zOf b v w' = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y := by
  constructor
  · intro h
    have hd : ∀ p, ϖ ∣ w p - w' p := fun p => hϖd _ (by
      rw [norm_lt_one_iff_valuation_lt_one]
      push_cast
      exact h p)
    choose c hc using hd
    refine ⟨zOf b v c, zOf_mem b v c, ?_⟩
    apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
    ext k
    rw [← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      tensorBasis_repr_zOf, tensorBasis_repr_zOf, tensorBasis_repr_zOf, smul_eq_mul]
    have hck := congrArg (fun t : v.adicCompletionIntegers F => (t : Fv F v)) (hc (0, k))
    push_cast at hck
    first
      | rw [hck]
      | (congr 1; exact hck)
      | simpa using congrArg _ hck
  · rintro ⟨y, hy, hyeq⟩ ⟨i, k⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have hk := congrArg (fun x => (Algebra.TensorProduct.basis (Fv F v) b).repr x k) hyeq
    rw [← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      tensorBasis_repr_zOf, tensorBasis_repr_zOf, smul_eq_mul] at hk
    rw [hk, map_mul]
    have h1 : Valued.v (ϖ : Fv F v) < 1 := (norm_lt_one_iff_valuation_lt_one v _).mp hϖ1
    have h2 : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr y k) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hy k)
    calc Valued.v (ϖ : Fv F v) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr y k)
        ≤ Valued.v (ϖ : Fv F v) * 1 := by gcongr
      _ = Valued.v (ϖ : Fv F v) := mul_one _
      _ < 1 := h1

end PositivityTheory.SiegelWeilFormula.MOne

end
