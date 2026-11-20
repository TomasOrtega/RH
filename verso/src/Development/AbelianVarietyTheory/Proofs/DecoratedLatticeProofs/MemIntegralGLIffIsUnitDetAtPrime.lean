import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

/- English proof (translation)
Introduce `E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M`. Take `⟨-, -, h3, -⟩` from `GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU`. Set `e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ)` to `(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv`. Establish `he : ∀ a, ((e a : Fin _) : ℕ) = zPos a`. Apply the tactic sequence `rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring`.

Set `A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E` to `Matrix.of fun s s' => M s.1 s'.1`. Set `T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k` to `Matrix.of fun a b => ι (M (zPos a) (zPos b))`. Establish `hT : T = (A.map ι).submatrix e e`. Use extensionality with `a b`. Simplify using `[T, A, he]`.

Establish `hdet : T.det = ι A.det`. Rewrite using `[hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k]` using `fun x hx => (Valuation.mem_integer_iff (valuation k) x).2 hx.le`. Express the relevant statement in the definitionally equal form `(∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hgv⟩`. Establish `hI` using `intM_of_mem_KO hg`. Rewrite `hI` using `[hgv]`. Use `⟨fun p p' hp hp' => ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)`. Simplify using `only [T, Matrix.of_apply] at h`. Rewrite `h` using `[← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Conclude with `(hC.int _).1 h`. Establish `hv` using `valuation_det_of_mem_KO hg`.

Rewrite `hv` using `[Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet]`. Conclude with `(h3 _ ((hC.int _).1 (hint _ hv))).1 hv`. Introduce and unpack `⟨hent, hunit⟩`. Establish `hTint : ∀ a b, T a b ∈ 𝒪[k]` using `fun a b => (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))`. Set `B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k]` to `Matrix.of fun a b => ⟨T a b, hTint a b⟩`.

Establish `hB : B.map (algebraMap 𝒪[k] k) = T` using `by ext a b; rfl`. Establish `hBdet : algebraMap 𝒪[k] k B.det = ι A.det`. Rewrite using `[RingHom.map_det]`. Express the relevant statement in the definitionally equal form `(B.map (algebraMap 𝒪[k] k)).det = _`. Rewrite using `[hB, hdet]`.

Establish `hAint : IntAt P A.det` using `(hC.int _).1 (hBdet ▸ (B.det).2)`. Establish `hv : valuation k (ι A.det) = 1` using `(h3 _ hAint).2 hunit`. Establish `hBu : IsUnit B.det` using `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)`. Use `⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`.

Rewrite using `[Matrix.GeneralLinearGroup.map_apply]`. Both sides reduce to the same expression.
-/
theorem mem_KO_iff_intAt_isUnit_det : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  let e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
    (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = zPos a := by
    rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring
  let A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E := Matrix.of fun s s' => M s.1 s'.1
  let T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b))
  have hT : T = (A.map ι).submatrix e e := by
    ext a b; simp [T, A, he]
  have hdet : T.det = ι A.det := by
    rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (h3 _ ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k] :=
      Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (h3 _ hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.SymBridge
