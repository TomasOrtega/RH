import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ F`. Establish `hc : ∀ {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n : ℤ), ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n)`. Introduce `E E' E'' f g n`. Use function extensionality and compare the values at `x`. Conclude with `pull_comp R f g F n x`.

Establish `hid : ∀ (E : Spc) (n : ℤ), ⇑(pull R (𝟙 E) F n) = id`. Introduce `E n`. Use function extensionality and compare the values at `x`. Conclude with `pull_id R E F n x`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `E E' f hf n haveI := hf`. Establish `h1 : Function.LeftInverse (pull R (inv f) F n) (pull R f F n)`. Introduce `x`. Use `congrFun (hc (inv f) f n) x` as an intermediate fact. Rewrite `this` using `[IsIso.inv_hom_id, hid]`.

Conclude with `this.symm`. Establish `h2 : Function.RightInverse (pull R (inv f) F n) (pull R f F n)`. Introduce `x`. Use `congrFun (hc f (inv f) n) x` as an intermediate fact. Rewrite `this` using `[IsIso.hom_inv_id, hid]`.

Conclude with `this.symm`. Conclude with `⟨h1.injective, h2.surjective⟩`. Introduce `E E' E'' f g`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hf hg n`.

Rewrite using `[hc]`. Conclude with `(hf n).comp (hg n)`. Introduce `hf hfg n`. Use `hfg n` as an intermediate fact. Rewrite `this` using `[hc]`.

Conclude with `(Function.Bijective.of_comp_iff' (hf n) _).mp this`. Introduce `hg hfg n`. Use `hfg n` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `(Function.Bijective.of_comp_iff _ (hg n)).mp this`.

Introduce `E E' f hq n`. Conclude with `GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map f) F n`. Introduce `E E' f hf`. Prove the components needed by the constructor for the conclusion. Introduce `h n hn haveI := h n hn`.

Conclude with `(hf n).1.subsingleton`. Introduce `h n hn haveI := h n hn`. Conclude with `(Equiv.ofBijective _ (hf n)).symm.subsingleton`.
-/
theorem eqv_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  intro R _ F
  have hc : ∀ {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n : ℤ),
      ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := by
    intro E E' E'' f g n
    funext x
    exact pull_comp R f g F n x
  have hid : ∀ (E : Spc) (n : ℤ), ⇑(pull R (𝟙 E) F n) = id := by
    intro E n
    funext x
    exact pull_id R E F n x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f hf n
    haveI := hf
    have h1 : Function.LeftInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc (inv f) f n) x
      rw [IsIso.inv_hom_id, hid] at this
      exact this.symm
    have h2 : Function.RightInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc f (inv f) n) x
      rw [IsIso.hom_inv_id, hid] at this
      exact this.symm
    exact ⟨h1.injective, h2.surjective⟩
  · intro E E' E'' f g
    refine ⟨?_, ?_, ?_⟩
    · intro hf hg n
      rw [hc]
      exact (hf n).comp (hg n)
    · intro hf hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff' (hf n) _).mp this
    · intro hg hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff _ (hg n)).mp this
  · intro E E' f hq n
    exact GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map f) F n
  · intro E E' f hf
    constructor
    · intro h n hn
      haveI := h n hn
      exact (hf n).1.subsingleton
    · intro h n hn
      haveI := h n hn
      exact (Equiv.ofBijective _ (hf n)).symm.subsingleton

end GlobalTheory.EtC
