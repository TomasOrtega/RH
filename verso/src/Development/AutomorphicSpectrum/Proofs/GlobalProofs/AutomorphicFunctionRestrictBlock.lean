import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapQdetEtr

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.CoreGL.CapScalar

def linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun Z := ∑ a, ∑ b, Z a b • E a b
  map_add' Z W := by simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑ i, ∑ j, (Matrix.single a b (1 : ℂ)) i j • E i j = E a b`. Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Matrix.single_apply, Ne.symm hj]`.

Simplify using the standard rewrite rules. Introduce `i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [Matrix.single_apply, Ne.symm hi]`. Simplify using the standard rewrite rules.
-/
theorem linOf_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin n) :
    linOf E (Matrix.single a b 1) = E a b := by
  classical
  change ∑ i, ∑ j, (Matrix.single a b (1 : ℂ)) i j • E i j = E a b
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
  · simp
  · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [Matrix.single_apply, Ne.symm hi]
  · simp

/- English proof (translation)
Establish `h : Formalism.REAL.GlRel (fun i j => linOf E (Matrix.single i j 1))`. Simplify `hE` using `only [linOf_single]`. Introduce `a b c d`. Simplify using `only`. Rewrite using `[GlobalTheory.CapelliLowest.lie_of_glRel (linOf E) h, hM a b c d, map_sub, apply_ite (linOf E), apply_ite (linOf E), map_zero]`.
-/
theorem glRel_linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M) :
    Formalism.REAL.GlRel fun i j => linOf E (M i j) := by
  have h : Formalism.REAL.GlRel (fun i j => linOf E (Matrix.single i j 1)) := by
    simpa only [linOf_single] using hE
  intro a b c d
  simp only
  rw [GlobalTheory.CapelliLowest.lie_of_glRel (linOf E) h, hM a b c d, map_sub, apply_ite (linOf E), apply_ite (linOf E), map_zero]

/- English proof (translation)
Establish `hZ : Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hZ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `(Formalism.REAL.qDetCentral A n _ (glRel_linOf hE hM) v p.1 p.2).symm`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, add_mul, mul_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]`.
-/
theorem qdet_commute {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M)
    (hs : Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) = ⊤) (v : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    linOf E Z * Formalism.REAL.qdet (fun i j => linOf E (M i j)) v = Formalism.REAL.qdet (fun i j => linOf E (M i j)) v * linOf E Z := by
  have hZ : Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) := hs ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact (Formalism.REAL.qDetCentral A n _ (glRel_linOf hE hM) v p.1 p.2).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

end GlobalTheory.CompanionTheory.CoreGL.CapScalar

namespace GlobalTheory.CompanionTheory.CoreGL

open GlobalTheory.CompanionTheory.CoreGL.CapScalar GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `D θ hθ V τ M hM hsp c v`. Establish `R` using `(GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V`. Take `⟨P, Q, hPQ, h⟩` from `GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2`. Take `⟨h1, h2⟩` from `h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) (fun X Y => by rw [TensorProduct.tmul_add, map_add]) (fun c X => by`. Rewrite using `[← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']`.

Use the proof step `simp)`. Use the proof step `(fun X Y Z hZ => by`. Establish `: Z = ⁅X, Y⁆` using `Subtype.ext hZ`. Rewrite using `[this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])`. Use `set E : Fin V.rank → Fin V.rank → EnvAt V τ := fun a b => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] P a b) + Complex.I • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Q a b) with hEdef`.

Establish `hcomm` using `qdet_commute h1 hM hsp v`. Use `set z : EnvAt V τ := Formalism.REAL.qdet (fun i j => linOf E (M i j)) v with hz`. Establish `hι : ∀ X : LieAt V τ, UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * z = z * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)`. Introduce `X`. Establish `hX` using `h2 X`.

Generalize the expression as in `UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) = y at hX`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Use `hcomm (Matrix.single p.1 p.2 1)` as an intermediate fact.

Rewrite `this` using `[linOf_single]`. Then use the resulting hypothesis. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]`. Consider the case `smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]`. Take `⟨cg, hc, hg⟩` from `exists_gelf R τ`.

Establish `hcen : z ∈ Subalgebra.center ℂ (EnvAt V τ)`. Rewrite using `[Subalgebra.mem_center_iff]`. Introduce `u`. Establish `: u ∈ Subalgebra.centralizer ℂ ({z} : Set (EnvAt V τ))`. Take `⟨w, rfl⟩` from `GlobalTheory.T.enveloping_map_surjective D V τ u`.

Use `Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _` and prove the remaining obligations. Take `⟨X, -, rfl⟩` from `List.mem_map.1 hx`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce and unpack `_ rfl`. Conclude with `(hι X).symm`.

Rewrite `this` using `[Subalgebra.mem_centralizer_iff]`. Conclude with `(this z rfl).symm`. Establish `key : ∀ y ∈ Algebra.adjoin ℂ (Set.range cg), ∃ s : ℂ, ∀ ψ : SmF θ V, (∀ k, gelf θ V τ k ψ.1 = c k • ψ.1) → envRep R τ y ψ = s • ψ`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Conclude with `⟨c k, fun ψ e => Subtype.ext ((hg k ψ).symm.trans (e k))⟩`. Consider the case `algebraMap r => exact ⟨r, fun ψ _ => by rw [AlgHom.commutes]; rfl⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Conclude with `⟨s + t, fun ψ e => by rw [map_add, LinearMap.add_apply, hs ψ e, ht ψ e, add_smul]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`.

Take `⟨t, ht⟩` from `hy`. Conclude with `⟨s * t, fun ψ e => by`. Rewrite using `[map_mul, Module.End.mul_apply, ht ψ e, map_smul, hs ψ e, smul_smul, mul_comm]⟩`. Rewrite `hcen` using `[hc]`. Take `⟨s, hs⟩` from `key z hcen`.

Establish `e : GlobalTheory.Mem.AutSpace.SmFun θ V = SmF θ V` using `Submodule.ext fun φ => smooth_iff R φ`. Set `T` to `(LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ`. Establish `k0 : ∀ a b, T (GlobalTheory.Mem.RealTranslate.derEnd (V` using `V) hθ τ (Matrix.single a b 1)) = envRep R τ (E a b) := by`. Introduce `a b`. Rewrite using `[hEdef]`.

Simplify using `only [map_add, map_smul, envRep_ι]`. Use `LinearMap.ext fun φ => Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RderC θ V τ (Matrix.single a b 1) φ.1 = _`. Rewrite using `[RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]`. Both sides reduce to the same expression.

Establish `k1 : ∀ Z, T (GlobalTheory.Mem.RealTranslate.derEnd (V` using `V) hθ τ Z) = envRep R τ (linOf E Z) := by`. Introduce `Z`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`. Express the relevant statement in the definitionally equal form `_ = envRep R τ (∑ a, ∑ b, Z a b • E a b)`. Simplify using `only [map_sum]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `: Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ)`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, map_smul, map_smul, k0]`. Establish `k2 : T (Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v) = envRep R τ z`.

Establish `a1` using `GlobalTheory.CompanionTheory.CapelliMap.map_qdet T.toAlgHom (fun i j => GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (M i j)) v`. Establish `a2` using `GlobalTheory.CompanionTheory.CapelliMap.map_qdet (envRep R τ) (fun i j => linOf E (M i j)) v`. Express the relevant statement in the definitionally equal form `T _ = _ at a1`. Rewrite using `[a1, hz, a2]`. Use `congr 1`.

Use function extensionality and compare the values at `i j`. Conclude with `k1 (M i j)`. Use `⟨s, fun f hf => ?_⟩` and prove the remaining obligations. Establish `k3` using `congrArg (fun S : Module.End ℂ (SmF θ V) => (S (LinearEquiv.ofEq _ _ e f)).1) k2`. Establish `k4` using `hs (LinearEquiv.ofEq _ _ e f) hf`.

Conclude with `Subtype.ext (k3.trans (congrArg Subtype.val k4))`.
-/
theorem qdet_scalar_of_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Submodule.span ℂ (Set.range fun p : Fin V.rank × Fin V.rank => M p.1 p.2) = ⊤ → ∀ (c : ℕ → ℂ) (v : ℂ), ∃ s : ℂ,
      ∀ f : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ k, gelf θ V τ k f.1 = c k • f.1) →
        Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v f = s • f := by
  intro D θ hθ V τ M hM hsp c v
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2
  obtain ⟨h1, h2⟩ := h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add])
    (fun c X => by
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])
  set E : Fin V.rank → Fin V.rank → EnvAt V τ := fun a b =>
    UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] P a b) + Complex.I • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Q a b) with hEdef

  have hcomm := qdet_commute h1 hM hsp v
  set z : EnvAt V τ := Formalism.REAL.qdet (fun i j => linOf E (M i j)) v with hz
  have hι : ∀ X : LieAt V τ, UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * z = z * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
    intro X
    have hX := h2 X
    generalize UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) = y at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      have := hcomm (Matrix.single p.1 p.2 1)
      rwa [linOf_single] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨cg, hc, hg⟩ := exists_gelf R τ
  have hcen : z ∈ Subalgebra.center ℂ (EnvAt V τ) := by
    rw [Subalgebra.mem_center_iff]
    intro u
    have : u ∈ Subalgebra.centralizer ℂ ({z} : Set (EnvAt V τ)) := by
      obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
      refine Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (hι X).symm
    rw [Subalgebra.mem_centralizer_iff] at this
    exact (this z rfl).symm

  have key : ∀ y ∈ Algebra.adjoin ℂ (Set.range cg), ∃ s : ℂ, ∀ ψ : SmF θ V,
      (∀ k, gelf θ V τ k ψ.1 = c k • ψ.1) → envRep R τ y ψ = s • ψ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨c k, fun ψ e => Subtype.ext ((hg k ψ).symm.trans (e k))⟩
    | algebraMap r => exact ⟨r, fun ψ _ => by rw [AlgHom.commutes]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, fun ψ e => by rw [map_add, LinearMap.add_apply, hs ψ e, ht ψ e, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s * t, fun ψ e => by
        rw [map_mul, Module.End.mul_apply, ht ψ e, map_smul, hs ψ e, smul_smul, mul_comm]⟩
  rw [hc] at hcen
  obtain ⟨s, hs⟩ := key z hcen

  have e : GlobalTheory.Mem.AutSpace.SmFun θ V = SmF θ V := Submodule.ext fun φ => smooth_iff R φ
  let T := (LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ
  have k0 : ∀ a b, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1)) = envRep R τ (E a b) := by
    intro a b
    rw [hEdef]
    simp only [map_add, map_smul, envRep_ι]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change RderC θ V τ (Matrix.single a b 1) φ.1 = _
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl
  have k1 : ∀ Z, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ Z) = envRep R τ (linOf E Z) := by
    intro Z
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    change _ = envRep R τ (∑ a, ∑ b, Z a b • E a b)
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, k0]
  have k2 : T (Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v) = envRep R τ z := by
    have a1 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet T.toAlgHom (fun i j => GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (M i j)) v
    have a2 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet (envRep R τ) (fun i j => linOf E (M i j)) v
    change T _ = _ at a1
    rw [a1, hz, a2]
    congr 1
    funext i j
    exact k1 (M i j)
  refine ⟨s, fun f hf => ?_⟩
  have k3 := congrArg (fun S : Module.End ℂ (SmF θ V) => (S (LinearEquiv.ofEq _ _ e f)).1) k2
  have k4 := hs (LinearEquiv.ofEq _ _ e f) hf
  exact Subtype.ext (k3.trans (congrArg Subtype.val k4))

end GlobalTheory.CompanionTheory.CoreGL

end
