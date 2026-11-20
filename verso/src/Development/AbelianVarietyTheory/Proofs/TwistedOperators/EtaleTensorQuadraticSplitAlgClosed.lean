import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Use `haveI : Module.Finite F P := Algebra.FormallyUnramified.finite_of_free F P`. Use `haveI : IsArtinianRing (Ω ⊗[F] P) := isArtinian_of_tower Ω inferInstance`. Set `e` to `Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[F] P)`. Use `letI : Fintype (PrimeSpectrum (Ω ⊗[F] P)) := Fintype.ofFinite _`. Establish `hc : Fintype.card (PrimeSpectrum (Ω ⊗[F] P)) = Fintype.card n`.

Use `e.toLinearEquiv.finrank_eq` as an intermediate fact. Rewrite `this` using `[Module.finrank_baseChange, h, Module.finrank_fintype_fun_eq_card]`. Conclude with `this.symm`. Conclude with `⟨e.trans (AlgEquiv.piCongrLeft' Ω (fun _ => Ω) (Fintype.equivOfCardEq hc))⟩`.
-/
theorem splitClosed_etale (F P Ω n : Type) [Field F] [CommRing P] [Algebra F P] [Fintype n]
    [Algebra.Etale F P] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (h : Module.finrank F P = Fintype.card n) :
    Nonempty (Ω ⊗[F] P ≃ₐ[Ω] (n → Ω)) := by
  classical
  haveI : Module.Finite F P := Algebra.FormallyUnramified.finite_of_free F P
  haveI : IsArtinianRing (Ω ⊗[F] P) := isArtinian_of_tower Ω inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[F] P)
  letI : Fintype (PrimeSpectrum (Ω ⊗[F] P)) := Fintype.ofFinite _
  have hc : Fintype.card (PrimeSpectrum (Ω ⊗[F] P)) = Fintype.card n := by
    have := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, h, Module.finrank_fintype_fun_eq_card] at this
    exact this.symm
  exact ⟨e.trans (AlgEquiv.piCongrLeft' Ω (fun _ => Ω) (Fintype.equivOfCardEq hc))⟩

/- English proof (translation)
Use `haveI := h.etale`. Use `haveI := quad_finite h`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Take `⟨e⟩` from `splitClosed_etale F E Ω (Fin 2) (by simp [h.finrank_eq])`. Set `θ : E →ₐ[F] Ω` to `(((Pi.evalAlgHom Ω (fun _ : Fin 2 => Ω) 0).comp e.toAlgHom).restrictScalars F).comp Algebra.TensorProduct.includeRight`.

Take `⟨b, d, -, hb1, hd, hbb⟩` from `quad_exists_basis h`. Establish `hc : θ (b 1) ≠ 0`. Introduce `h0`. Use `congrArg θ hbb` as an intermediate fact. Rewrite `this` using `[map_mul, h0, mul_zero, AlgHom.commutes]`.

Conclude with `hd ((map_eq_zero _).1 this.symm)`. Set `f : Ω ⊗[F] E →ₐ[Ω] Ω × Ω` to `Algebra.TensorProduct.lift (Algebra.ofId Ω (Ω × Ω)) (θ.prod (θ.comp σ)) (fun _ _ => Commute.all _ _)`. Establish `hf : ∀ ω x, f (ω ⊗ₜ x) = (ω * θ x, ω * θ (σ x))`. Introduce `ω x`. Simplify using `[f, Algebra.ofId_apply]`.

Establish `hs : Function.Surjective f`. Introduce and unpack `⟨x, y⟩`. Use `⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * θ (b 1))) ⊗ₜ b 1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hf, hf, hb1, map_neg, map_one, map_one]`. Apply the tactic sequence `ext <;> simp <;> field_simp <;> ring`.

Establish `hi : Function.Injective f` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) (by simp [h.finrank_eq])).2 hs`. Use `⟨(Algebra.TensorProduct.comm F E Ω).trans ((AlgEquiv.ofBijective f ⟨hi, hs⟩).restrictScalars F), fun ω => (hf ω 1).trans (by simp), fun u => ?_⟩` and prove the remaining obligations. Proceed by induction on `u with`. Consider the case `zero => simp`. Consider the case `tmul a w`.

Express the relevant statement in the definitionally equal form `f (w ⊗ₜ σ a) = (f (w ⊗ₜ a)).swap`. Rewrite using `[hf, hf, h.invol]`. Both sides reduce to the same expression. Consider the case `add a w ha hw => rw [map_add, map_add, map_add, ha, hw, Prod.swap_add]`.
-/
theorem splitClosed_quad {F E : Type} [Field F] [CharZero F] [CommRing E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsQuadInvol F E σ) (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    ∃ φ : E ⊗[F] Ω ≃ₐ[F] Ω × Ω, (∀ ω : Ω, φ (1 ⊗ₜ ω) = (ω, ω)) ∧
      ∀ u, φ (Algebra.TensorProduct.map σ (AlgHom.id F Ω) u) = (φ u).swap := by
  haveI := h.etale
  haveI := quad_finite h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨e⟩ := splitClosed_etale F E Ω (Fin 2) (by simp [h.finrank_eq])
  let θ : E →ₐ[F] Ω := (((Pi.evalAlgHom Ω (fun _ : Fin 2 => Ω) 0).comp e.toAlgHom).restrictScalars F).comp
    Algebra.TensorProduct.includeRight
  obtain ⟨b, d, -, hb1, hd, hbb⟩ := quad_exists_basis h
  have hc : θ (b 1) ≠ 0 := by
    intro h0
    have := congrArg θ hbb
    rw [map_mul, h0, mul_zero, AlgHom.commutes] at this
    exact hd ((map_eq_zero _).1 this.symm)
  let f : Ω ⊗[F] E →ₐ[Ω] Ω × Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω (Ω × Ω)) (θ.prod (θ.comp σ)) (fun _ _ => Commute.all _ _)
  have hf : ∀ ω x, f (ω ⊗ₜ x) = (ω * θ x, ω * θ (σ x)) := by
    intro ω x; simp [f, Algebra.ofId_apply]
  have hs : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * θ (b 1))) ⊗ₜ b 1, ?_⟩
    rw [map_add, hf, hf, hb1, map_neg, map_one, map_one]
    ext <;> simp <;> field_simp <;> ring
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by simp [h.finrank_eq])).2 hs
  refine ⟨(Algebra.TensorProduct.comm F E Ω).trans
    ((AlgEquiv.ofBijective f ⟨hi, hs⟩).restrictScalars F), fun ω => (hf ω 1).trans (by simp), fun u => ?_⟩
  induction u with
  | zero => simp
  | tmul a w =>
    change f (w ⊗ₜ σ a) = (f (w ⊗ₜ a)).swap
    rw [hf, hf, h.invol]; rfl
  | add a w ha hw => rw [map_add, map_add, map_add, ha, hw, Prod.swap_add]

def splitClosedPair (F Ω n : Type) [Field F] [Field Ω] [Algebra F Ω] :
    ((n → Ω) × (n → Ω)) ≃ₐ[F] (n → Ω × Ω) where
  toFun x i := (x.1 i, x.2 i)
  invFun y := (fun i => (y i).1, fun i => (y i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/- English proof (translation)
Introduce `F E _ _ _ _ σ h P _ _ n _ hP ⟨b⟩ Ω _ _ _`. Take `⟨e⟩` from `splitClosed_etale F P Ω n (Module.finrank_eq_card_basis b)`. Take `⟨g, hg1, hg⟩` from `splitClosed_quad h Ω`. Set `e' : P ⊗[F] Ω ≃ₐ[F] (n → Ω)` to `(Algebra.TensorProduct.comm F P Ω).trans (e.restrictScalars F)`. Establish `he' : ∀ ω : Ω, e' (1 ⊗ₜ ω) = fun _ => ω` using `fun ω => e.commutes ω`.

Set `φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω)` to `((Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[F] P) g).trans (Algebra.TensorProduct.prodRight F F P Ω Ω)).trans ((AlgEquiv.prodCongr e' e').trans (splitClosedPair F Ω n))`. Establish `hφ : ∀ p x i, φ (p ⊗ₜ x) i = (e' (p ⊗ₜ (g x).1) i, e' (p ⊗ₜ (g x).2) i)`. Introduce `p x i`. Both sides reduce to the same expression. Use `⟨φ, fun ω => funext fun i => by rw [hφ, hg1, he'], fun u i => ?_⟩` and prove the remaining obligations.

Proceed by induction on `u with`. Consider the case `zero => simp`. Consider the case `tmul p x => rw [tConj3, Algebra.TensorProduct.map_tmul, hφ, hφ, hg]`. Both sides reduce to the same expression. Consider the case `add a w ha hw => rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, ha, hw, Prod.swap_add]`.
-/
theorem splitClosed : SplitClosed := by
  intro F E _ _ _ _ σ h P _ _ n _ hP ⟨b⟩ Ω _ _ _
  obtain ⟨e⟩ := splitClosed_etale F P Ω n (Module.finrank_eq_card_basis b)
  obtain ⟨g, hg1, hg⟩ := splitClosed_quad h Ω
  let e' : P ⊗[F] Ω ≃ₐ[F] (n → Ω) := (Algebra.TensorProduct.comm F P Ω).trans (e.restrictScalars F)
  have he' : ∀ ω : Ω, e' (1 ⊗ₜ ω) = fun _ => ω := fun ω => e.commutes ω
  let φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[F] P) g).trans
      (Algebra.TensorProduct.prodRight F F P Ω Ω)).trans
      ((AlgEquiv.prodCongr e' e').trans (splitClosedPair F Ω n))
  have hφ : ∀ p x i, φ (p ⊗ₜ x) i = (e' (p ⊗ₜ (g x).1) i, e' (p ⊗ₜ (g x).2) i) := by
    intro p x i; rfl
  refine ⟨φ, fun ω => funext fun i => by rw [hφ, hg1, he'], fun u i => ?_⟩
  induction u with
  | zero => simp
  | tmul p x => rw [tConj3, Algebra.TensorProduct.map_tmul, hφ, hφ, hg]; rfl
  | add a w ha hw => rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, ha, hw, Prod.swap_add]

end GlobalTheory.RegSS
