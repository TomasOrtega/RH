import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVolB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHC

noncomputable section

namespace PI.VolStabW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `set B := Algebra.TensorProduct.basis (Fv F v) b with hBdef`. Establish `hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k` using `fun k => Algebra.TensorProduct.basis_apply _ _`. Establish `hs : ∀ k, sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) = (1 : Fv F v) ⊗ₜ[F] σ (b k)`. Introduce `k`. Simplify using `[sigR]`.

Use `conv_lhs => rw [← B.sum_repr z]`. Rewrite using `[map_sum]`. Simplify using `only [sigR_smul, hB, hs, crd, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, one_smul]`. Both sides reduce to the same expression.
-/
theorem crd_sigR (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) (l : Fin d) :
    crd b (Fv F v) (sigR (Fv F v) σ z) l =
      ∑ k, crd b (Fv F v) z k * algebraMap F (Fv F v) (b.repr (σ (b k)) l) := by
  set B := Algebra.TensorProduct.basis (Fv F v) b with hBdef
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hs : ∀ k, sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) = (1 : Fv F v) ⊗ₜ[F] σ (b k) := by
    intro k
    simp [sigR]
  conv_lhs => rw [← B.sum_repr z]
  rw [map_sum]
  simp only [sigR_smul, hB, hs, crd, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply, one_smul]
  rfl

/- English proof (translation)
Use `filter_upwards [ev_int_all (fun q : Fin d × Fin d => b.repr (σ (b q.1)) q.2)] with v h`. Introduce `z hz l`. Rewrite using `[crd_sigR]`. Conclude with `sum_mem fun k _ => mul_mem (hz k) (h (k, l))`.
-/
theorem ev_sig (σ : E →ₐ[F] E) :
    ∀ᶠ v in cofinite, ∀ z ∈ latA v b, sigR (Fv F v) σ z ∈ latA v b := by
  filter_upwards [ev_int_all (fun q : Fin d × Fin d => b.repr (σ (b q.1)) q.2)] with v h
  intro z hz l
  rw [crd_sigR]
  exact sum_mem fun k _ => mul_mem (hz k) (h (k, l))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h p i k`. Conclude with `h i p k`. Introduce `h i j k`. Conclude with `h j i k`.
-/
theorem mem_hermO_iff (σ : E →ₐ[F] E) {a : ℕ} (T : HermR (Fv F v) σ a) :
    T ∈ hermO b v σ a ↔
      (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) ∈ latV (M := a) (n := a) b v := by
  constructor
  · intro h p i k
    exact h i p k
  · intro h i j k
    exact h j i k

/- English proof (translation)
Use `filter_upwards [ev_dual b σ hσ (1 : Matrix (Fin a) (Fin a) E) (by simp) (a := a), ev_sig b σ, ev_int (1 / 2 : F)] with v hD hS hh`. Use extensionality with `T`. Prove the components needed by the constructor for the conclusion. Introduce `hT`. Rewrite `hT` using `[Set.mem_setOf_eq]`.

Rewrite using `[SetLike.mem_coe, mem_hermO_iff, ← hD]`. Introduce `X hX`. Rewrite using `[← pairHerm_iota v σ hσ X T]`. Apply `hT` to reduce the goal to its premises. Introduce `i j k`.

Establish `h1 : X i j ∈ latA v b` using `fun k => hX i j k`. Establish `h2 : X j i ∈ latA v b` using `fun k => hX j i k`. Conclude with `(add_mem (hS _ h1) h2) k`. Introduce `hT`. Rewrite `hT` using `[SetLike.mem_coe, mem_hermO_iff, ← hD]`.

Rewrite using `[Set.mem_setOf_eq]`. Introduce `S hS`. Use `set c : Fv F v := algebraMap F (Fv F v) (1 / 2) with hc`. Set `X : Fin a → Fin a → Fv F v ⊗[F] E` to `fun p q => c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p`. Establish `hX : X ∈ latV (M` using `a) (n := a) b v := by`.

Introduce `p q k`. Use `crd_smul v b c ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k` as an intermediate fact. Simplify using `only [crd] at this`. Use `show (Algebra.TensorProduct.basis (Fv F v) b).repr (c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k ∈ _`. Rewrite using `[this]`.

Conclude with `mul_mem hh (hS q p k)`. Establish `hcc : c + c = 1`. Rewrite using `[hc, ← map_add]`. Evaluate the numerical expressions. Establish `hSX : S = ⟨iota v σ X, iota_mem v σ hσ X⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `p q`. Simplify using `only [iota, X, sigR_smul]`. Rewrite using `[S.2 p q, ← add_smul, hcc, one_smul]`. Rewrite using `[hSX, pairHerm_iota v σ hσ X T]`.

Conclude with `hT X hX`.
-/
theorem ev_dualH [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    ∀ᶠ v in cofinite, {T : HermR (Fv F v) σ a | ∀ S ∈ hermO b v σ a,
      pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} = hermO b v σ a := by
  filter_upwards [ev_dual b σ hσ (1 : Matrix (Fin a) (Fin a) E) (by simp) (a := a), ev_sig b σ,
    ev_int (1 / 2 : F)] with v hD hS hh
  ext T
  constructor
  · intro hT
    rw [Set.mem_setOf_eq] at hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD]
    intro X hX
    rw [← pairHerm_iota v σ hσ X T]
    apply hT
    intro i j k
    have h1 : X i j ∈ latA v b := fun k => hX i j k
    have h2 : X j i ∈ latA v b := fun k => hX j i k
    exact (add_mem (hS _ h1) h2) k
  · intro hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD] at hT
    rw [Set.mem_setOf_eq]
    intro S hS
    set c : Fv F v := algebraMap F (Fv F v) (1 / 2) with hc
    let X : Fin a → Fin a → Fv F v ⊗[F] E := fun p q =>
      c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p
    have hX : X ∈ latV (M := a) (n := a) b v := by
      intro p q k
      have := crd_smul v b c ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k
      simp only [crd] at this
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
        (c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k ∈ _
      rw [this]
      exact mul_mem hh (hS q p k)
    have hcc : c + c = 1 := by
      rw [hc, ← map_add]
      norm_num
    have hSX : S = ⟨iota v σ X, iota_mem v σ hσ X⟩ := by
      apply Subtype.ext
      funext p q
      simp only [iota, X, sigR_smul]
      rw [S.2 p q, ← add_smul, hcc, one_smul]
    rw [hSX, pairHerm_iota v σ hσ X T]
    exact hT X hX

/- English proof (translation)
Use `locallyCompact_Fv F v` as an intermediate fact. Establish `hcl` using `(isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal`. Establish `e : (hermO b v σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹' ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)))`. Use extensionality with `S`. Conclude with `⟨fun h p _ q _ k => h p q k, fun h p q k => h p (Set.mem_univ _) q (Set.mem_univ _) k⟩`.

Establish `hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latA v b`. Establish `hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)))` using `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latA v b`. Rewrite using `[e]`. Conclude with `⟨hcl.isCompact_preimage hKc, hKo.preimage continuous_subtype_val⟩`.
-/
theorem isCompact_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) ∧
      IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  have hcl := (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
  have e : (hermO b v σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹'
      ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latA v b : Set (Fv F v ⊗[F] E))) :
        Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) := by
    ext S
    exact ⟨fun h p _ q _ k => h p q k, fun h p q k => h p (Set.mem_univ _) q (Set.mem_univ _) k⟩
  have hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latA v b
  have hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_latA v b
  rw [e]
  exact ⟨hcl.isCompact_preimage hKc, hKo.preimage continuous_subtype_val⟩

/- English proof (translation)
Introduce `s hs S hS`. Establish `hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a`. Introduce `p q`. Simplify using `only [Matrix.smul_apply, sigR_smul, S.2 p q]`. Use `⟨⟨_, hmem⟩, ?_, fun T => ?_⟩` and prove the remaining obligations.

Introduce `p q k`. Use `crd_smul v b s ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k` as an intermediate fact. Simplify using `only [crd] at this`. Use `show (Algebra.TensorProduct.basis (Fv F v) b).repr (s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k ∈ _`. Rewrite using `[this]`.

Conclude with `mul_mem hs (hS p q k)`. Simplify using `only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ S ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
      ∃ S' ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
        ∀ T, pairHerm (Fv F v) σ a S' T = s * pairHerm (Fv F v) σ a S T := by
  intro s hs S hS
  have hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a := by
    intro p q
    simp only [Matrix.smul_apply, sigR_smul, S.2 p q]
  refine ⟨⟨_, hmem⟩, ?_, fun T => ?_⟩
  · intro p q k
    have := crd_smul v b s ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k
    simp only [crd] at this
    show (Algebra.TensorProduct.basis (Fv F v) b).repr
      (s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k ∈ _
    rw [this]
    exact mul_mem hs (hS p q k)
  · simp only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
      smul_eq_mul]
    ring

/- English proof (translation)
Introduce `s hs x hx`. Use `⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩` and prove the remaining obligations. Introduce `p i l`. Use `crd_smul v b s (x p i) l` as an intermediate fact. Simplify using `only [crd] at this`.

Rewrite using `[Pi.smul_apply, Pi.smul_apply, this]`. Conclude with `mul_mem hs (hx p i l)`.
-/
theorem smul_latV (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ latV (M := M) (n := a) b v,
      ∃ x' ∈ latV (M := M) (n := a) b v, ∀ y, BR (Fv F v) σ J x' y = s * BR (Fv F v) σ J x y := by
  intro s hs x hx
  refine ⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩
  intro p i l
  have := crd_smul v b s (x p i) l
  simp only [crd] at this
  rw [Pi.smul_apply, Pi.smul_apply, this]
  exact mul_mem hs (hx p i l)

end VolAAW

end PI.VolStabW
