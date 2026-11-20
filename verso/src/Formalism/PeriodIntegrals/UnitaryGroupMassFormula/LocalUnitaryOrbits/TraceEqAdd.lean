import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by omega)`. Set `τ : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext hinv) (AlgHom.ext hinv)`. Establish `hτ : τ ≠ 1`. Introduce `h`. Take `⟨x0, hx0⟩` from `hnt`.

Apply `hx0` to reduce the goal to its premises. Use `congrArg (fun f : E ≃ₐ[F] E => f x0) h` as an intermediate fact. Simplify `this` using `[τ]`. Establish `hcard : Fintype.card (E ≃ₐ[F] E) = 2`. Use `le_antisymm (hfin ▸ AlgEquiv.card_le) ?_` and prove the remaining obligations.

Establish `h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2` using `Finset.card_pair hτ.symm`. Rewrite using `[← h2]`. Conclude with `Finset.card_le_univ _`. Establish `: IsGalois F E` using `IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfin])`. Rewrite using `[trace_eq_sum_automorphisms]`.

Establish `hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ}` using `(Finset.eq_univ_of_card _ (by rw [Finset.card_pair hτ.symm, hcard])).symm`. Rewrite using `[hu, Finset.sum_pair hτ.symm]`. Both sides reduce to the same expression.
-/
theorem trace_eq_add (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let τ : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hinv) (AlgHom.ext hinv)
  have hτ : τ ≠ 1 := by
    intro h
    obtain ⟨x0, hx0⟩ := hnt
    apply hx0
    have := congrArg (fun f : E ≃ₐ[F] E => f x0) h
    simpa [τ] using this
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hfin ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair hτ.symm
    rw [← h2]
    exact Finset.card_le_univ _
  have : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfin])
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hτ.symm, hcard])).symm
  rw [hu, Finset.sum_pair hτ.symm]
  rfl

variable (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `e : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (inclR (F` using `F) (Fv F v) x) = (Algebra.lmul F E x).baseChange (Fv F v) := by`. Apply `TensorProduct.AlgebraTensorModule.curry_injective` to reduce the goal to its premises. Use extensionality with `a e`. Simplify using `[inclR]`.

Rewrite using `[Algebra.trace_apply, e, LinearMap.trace_baseChange]`. Both sides reduce to the same expression.
-/
theorem trace_inclR (x : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      algebraMap F (Fv F v) (Algebra.trace F E x) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      (Algebra.lmul F E x).baseChange (Fv F v) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a e
    simp [inclR]
  rw [Algebra.trace_apply, e, LinearMap.trace_baseChange]
  rfl

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c e`. Establish `e1 : c ⊗ₜ[F] e = c • inclR (F` using `F) (Fv F v) e := by`. Simplify using `[inclR, TensorProduct.smul_tmul']`.

Establish `hL : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c ⊗ₜ[F] e) = algebraMap F (Fv F v) (Algebra.trace F E e) * c`. Rewrite using `[e1, map_smul, trace_inclR, smul_eq_mul, mul_comm]`. Rewrite using `[hL, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← Algebra.smul_def, TensorProduct.smul_tmul]`. Simplify using `only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[← TensorProduct.tmul_add, ← trace_eq_add σ hinv hnt hfin e, Algebra.algebraMap_eq_smul_one]`.

Consider the case `add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem trace_v (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (w : Fv F v ⊗[F] E) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c e =>
    have e1 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
      simp [inclR, TensorProduct.smul_tmul']
    have hL : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c ⊗ₜ[F] e) =
        algebraMap F (Fv F v) (Algebra.trace F E e) * c := by
      rw [e1, map_smul, trace_inclR, smul_eq_mul, mul_comm]
    rw [hL, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      ← Algebra.smul_def, TensorProduct.smul_tmul]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rw [← TensorProduct.tmul_add, ← trace_eq_add σ hinv hnt hfin e, Algebra.algebraMap_eq_smul_one]
  | add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2, map_add]; abel

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c e => simp [sigR, hinv]`. Consider the case `add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2]`.
-/
theorem sigR_sigR (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (w : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c e => simp [sigR, hinv]
  | add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩`.
-/
theorem b_inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.smul_mem (Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (⟨c, hc⟩ : v.adicCompletionIntegers F) hx`.
-/
theorem b_smul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v :=
  Submodule.smul_mem (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

/- English proof (translation)
Simplify using `using b_inclR_mem (E := E) v 1`.
-/
theorem b_one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using b_inclR_mem (E := E) v 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem b_sc_eq (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

/- English proof (translation)
Rewrite using `[b_sc_eq, Algebra.algebraMap_eq_smul_one]`. Conclude with `b_smul_mem v hc (b_one_mem v)`.
-/
theorem b_sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  rw [b_sc_eq, Algebra.algebraMap_eq_smul_one]
  exact b_smul_mem v hc (b_one_mem v)

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨a, -, rfl⟩` from `ha`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem b hb`.

Take `⟨b, -, rfl⟩` from `hb`. Use `b_inclR_mem (E := E) v (a * b)` as an intermediate fact. Simplify using `using this`. Consider the case `zero => rw [mul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y1 y2 _ _ h1 h2 => rw [mul_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c y _ h => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c h`. Consider the case `zero => rw [zero_mul]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x1 x2 _ _ h1 h2 => rw [add_mul]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c h`.
-/
theorem b_mul_mem {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      have := b_inclR_mem (E := E) v (a * b)
      simpa using this
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y1 y2 _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨a, -, rfl⟩` from `ha`. Rewrite using `[trace_inclR]`. Establish `hint : IsIntegral ℤ (Algebra.trace F E (a : E))` using `Algebra.isIntegral_trace a.2`.

Conclude with `HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨_, hint⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x1 x2 _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`.

Consider the case `smul c x _ h`. Establish `e : c • x = (c : Fv F v) • x` using `rfl`. Rewrite using `[e, map_smul, smul_eq_mul]`. Conclude with `(v.adicCompletionIntegers F).mul_mem _ _ c.2 h`.
-/
theorem b_trace_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x ∈ v.adicCompletionIntegers F := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    rw [trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) := Algebra.isIntegral_trace a.2
    exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨_, hint⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, map_smul, smul_eq_mul]
    exact (v.adicCompletionIntegers F).mul_mem _ _ c.2 h

/- English proof (translation)
Unfold `OEv at ho`. Rewrite `ho` using `[SetLike.mem_coe]`. Proceed by induction on `ho using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨e, -, rfl⟩` from `hy`.

Unfold `latLoc at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨l, hl, rfl⟩` from `hz`. Establish `hel : e • l ∈ L` using `L.smul_mem e hl`.

Establish `eq : inclR (F` using `F) (Fv F v) (e : E) • ratV (F := F) (Fv F v) l = ratV (F := F) (Fv F v) (e • l) := by`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, ratV]`. Rewrite using `[← map_mul]`. Both sides reduce to the same expression.

Rewrite using `[eq]`. Conclude with `Submodule.subset_span ⟨_, hel, rfl⟩`. Consider the case `zero`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add z w _ _ hz hw`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hz hw`. Consider the case `smul r z _ hz`. Rewrite using `[smul_comm]`.

Conclude with `Submodule.smul_mem _ r hz`. Consider the case `zero`. Rewrite using `[zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz`.

Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul r y _ hy`. Rewrite using `[smul_assoc]`. Conclude with `Submodule.smul_mem _ r hy`.
-/
theorem b_lat_smul {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {o : Fv F v ⊗[F] E} (ho : o ∈ OEv (E := E) v)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v (L : Set (Fin n → E))) :
    o • x ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
  unfold OEv at ho
  rw [SetLike.mem_coe] at ho
  induction ho using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, -, rfl⟩ := hy
    unfold latLoc at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      have hel : e • l ∈ L := L.smul_mem e hl
      have eq : inclR (F := F) (Fv F v) (e : E) • ratV (F := F) (Fv F v) l =
          ratV (F := F) (Fv F v) (e • l) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ratV]
        rw [← map_mul]
        rfl
      rw [eq]
      exact Submodule.subset_span ⟨_, hel, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add z w _ _ hz hw =>
      rw [smul_add]
      exact Submodule.add_mem _ hz hw
    | smul r z _ hz =>
      rw [smul_comm]
      exact Submodule.smul_mem _ r hz
  | zero =>
    rw [zero_smul]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [add_smul]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r hy

/- English proof (translation)
Take `⟨-, -, -, h4⟩` from `h`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h4, h4, star_star]`.
-/
theorem b_sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h4, h4, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Establish `hs : σ = AlgHom.id F E` using `AlgHom.ext hn`. Take `⟨-, htc, -, h4⟩` from `h`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom`.

Establish `hr : ComplexEmbedding.IsReal τ`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Use `h4 τ x` as an intermediate fact.

Rewrite `this` using `[hs, AlgHom.id_apply]`. Rewrite using `[starRingEnd_apply]`. Conclude with `this.symm`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ)) (InfinitePlace.isReal_mk_iff.2 hr)`.
-/
theorem b_sig_nt (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hn
  push Not at hn
  have hs : σ = AlgHom.id F E := AlgHom.ext hn
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

end Gen

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TrPerf : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ z : Fv F v ⊗[F] E,
    (∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) →
    z ∈ OEv (E := E) v

end Steps

end PI.OmLocU.SdB
