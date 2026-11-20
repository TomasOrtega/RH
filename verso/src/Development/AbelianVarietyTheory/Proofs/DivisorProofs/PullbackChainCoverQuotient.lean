import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

noncomputable section

namespace GlobalTheory.ChainDesc

/- English proof (translation)
Rewrite using `[mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]`. Both sides reduce to the same expression.
-/
private theorem mv_one_eq {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {h : ℕ} (x : Fin h → A) :
    mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

/- English proof (translation)
Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul R a, map_smul, k]`. Both sides reduce to the same expression.
-/
private theorem rho_smul {p h o : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {π : R} {γ : ℕ → R}
    {Lie Om : Type} [AddCommGroup Lie] [Module R Lie] [AddCommGroup Om] [Module A Om]
    (C : RChain p R h o π γ Lie (R ⊗[A] Om)) (a : A) (s : Om) (y : C.L 0)
    (k : C.ρ (1 ⊗ₜ s) = Submodule.Quotient.mk (Submodule.Quotient.mk y)) :
    C.ρ (1 ⊗ₜ (a • s)) = Submodule.Quotient.mk (Submodule.Quotient.mk (algebraMap A R a • y)) := by
  rw [TensorProduct.tmul_smul, ← algebraMap_smul R a, map_smul, k]; rfl

/- English proof (translation)
Rewrite using `[TensorProduct.tmul_add, map_add, k, k']`. Both sides reduce to the same expression.
-/
private theorem rho_add {p h o : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {π : R} {γ : ℕ → R}
    {Lie Om : Type} [AddCommGroup Lie] [Module R Lie] [AddCommGroup Om] [Module A Om]
    (C : RChain p R h o π γ Lie (R ⊗[A] Om)) (s s' : Om) (y y' : C.L 0)
    (k : C.ρ (1 ⊗ₜ s) = Submodule.Quotient.mk (Submodule.Quotient.mk y))
    (k' : C.ρ (1 ⊗ₜ s') = Submodule.Quotient.mk (Submodule.Quotient.mk y')) :
    C.ρ (1 ⊗ₜ (s + s')) = Submodule.Quotient.mk (Submodule.Quotient.mk (y + y')) := by
  rw [TensorProduct.tmul_add, map_add, k, k']; rfl

/- English proof (translation)
Rewrite using `[TensorProduct.tmul_zero, map_zero]`. Both sides reduce to the same expression.
-/
private theorem rho_zero {p h o : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {π : R} {γ : ℕ → R}
    {Lie Om : Type} [AddCommGroup Lie] [Module R Lie] [AddCommGroup Om] [Module A Om]
    (C : RChain p R h o π γ Lie (R ⊗[A] Om)) :
    C.ρ (1 ⊗ₜ 0) = Submodule.Quotient.mk (Submodule.Quotient.mk 0) := by
  rw [TensorProduct.tmul_zero, map_zero]; rfl

section
variable {A A' : Type} [CommRing A] [CommRing A'] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie]
  [Module A Lie] [AddCommGroup Om] [Module A Om] {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type} [AddCommGroup Lie']
  [Module A' Lie'] [AddCommGroup Om'] [Module A' Om']

/- English proof (translation)
Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ (C.ρ w)`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `⟨y, hz.symm⟩`.
-/
private theorem rho_rep (C : RChain p A h o π γ Lie Om) (w : Om) :
    ∃ y : C.L 0, C.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk y) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (C.ρ w)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨y, hz.symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨_, k.mem 0 _ y.2⟩, mv_one_eq _ _, hw ▸ k.ρ w y _ rfl hy⟩`.
-/
private theorem rho_map {C : RChain p A h o π γ Lie Om} {C' : RChain p A' h o π' γ' Lie' Om'} {φ : A →+* A'}
    {l : Lie → Lie'} {m : Om → Om'} (k : C.Map C' φ 1 l m) {w : Om} {w' : Om'} (hw : m w = w') {y : C.L 0}
    (hy : C.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk y)) :
    ∃ y' : C'.L 0, y'.1 = piMap φ (Fin h) y.1 ∧ C'.ρ w' = Submodule.Quotient.mk (Submodule.Quotient.mk y') :=
  ⟨⟨_, k.mem 0 _ y.2⟩, mv_one_eq _ _, hw ▸ k.ρ w y _ rfl hy⟩

end

set_option maxHeartbeats 2400000 in

/- English proof (translation)
Introduce `O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t ρ hq hS hc hι U S D hD hR U' hle s`. Establish `hfit : D.L 0 = latOf (ι 0) _` using `hD.fits hι 0 (Nat.zero_le _)`. Take `⟨l, m, -, hm, hM, -⟩` from `hD`. Take `⟨-, l', m', -, hm', hM'⟩` from `hS.1 U U' hle`. Use `letI := GlobalTheory.QCoh.resAlgebra (X := B.X) hle`.

Use `letI := GlobalTheory.QCoh.resModule Om.V hle`. Use `haveI := GlobalTheory.QCoh.res_isScalarTower Om.V hle`. Proceed by induction on `s using (isBaseChange_resLinear Om.V U.2.1 U'.2.1 hle).inductionOn with`. Consider the case `zero`. Use `⟨0, 0, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero, map_zero]`. Both sides reduce to the same expression. Conclude with `rho_zero _`. Rewrite using `[map_zero, map_zero, map_zero]`. Consider the case `tmul s`.

Take `⟨y, hz⟩` from `rho_rep D (pullbackSections f.f Om.V le_rfl s)`. Take `⟨x, hx⟩ : y.1 ∈ latOf (ι 0) _` from `hfit.le y.2`. Establish `h1` using `hR _ x y hx.symm hz`. Take `⟨y₁, e₁, h2⟩` from `rho_map hM (hm s) hz`. Take `⟨y₂, e₂, h3⟩` from `rho_map hM' (hm' s) h2`.

Use `⟨resM (E 0) (f.f.preimage_mono hle) x, y₂, ?_, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[crd_resM, hx, e₂, e₁]`. Use function extensionality and compare the values at `i`. Conclude with `(hc.2.2.2.2 U U' hle _).symm`. Rewrite using `[GlobalTheory.Twist.app_resM, ← h1]`.

Use `Eq.trans (congrArg _ ?_) (GlobalTheory.Twist.app_resM ρ (f.f.preimage_mono hle) _)` and prove the remaining obligations. Conclude with `(pullbackSections_res f.f Om.V le_rfl hle s).trans (res_pullbackSections f.f Om.V le_rfl (f.f.preimage_mono hle) s).symm`. Consider the case `smul a s ih`. Take `⟨x, y, h1, h2, h3⟩` from `ih`. Use `⟨(f.f.app U'.1).hom a • x, algebraMap Γ(B.X, U'.1) U'.Bp a • y, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, LinearMap.map_smulₛₗ, hc.2.2.2.1, ← h1]`. Both sides reduce to the same expression. Conclude with `rho_smul _ a s y h2`. Rewrite using `[pullbackSections_smul, Scheme.Hom.appLE_eq_app, Scheme.Modules.Hom.app_smul, ← h3]`. Conclude with `Scheme.Modules.Hom.app_smul ρ _ _`.

Consider the case `add s s' ih ih'`. Take `⟨x, y, h1, h2, h3⟩` from `ih`. Take `⟨x', y', h1', h2', h3'⟩` from `ih'`. Use `⟨x + x', y + y', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, ← h1, ← h1']`.

Both sides reduce to the same expression. Conclude with `rho_add _ s s' y y' h2 h2'`. Rewrite using `[map_add, map_add, map_add, h3, h3']`.
-/
theorem rUp_of_le : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : B'.X.Modules) (t : E 0 ⟶ Q) (ρ : ((pullA f.f).obj Om).V ⟶ Q), Om.V.IsQuasicoherent → IsSys C M → IsCov f g → IsLatOf C f g ι → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)), IsDown C f g U S D → ROn (ι 0) D t ρ → ∀ U' : AffOp B.X, U'.1 ≤ U.1 → RUp C f g U' (ι 0) t ρ := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t ρ hq hS hc hι U S D hD hR U' hle s
  have hfit : D.L 0 = latOf (ι 0) _ := hD.fits hι 0 (Nat.zero_le _)
  obtain ⟨l, m, -, hm, hM, -⟩ := hD
  obtain ⟨-, l', m', -, hm', hM'⟩ := hS.1 U U' hle
  letI := GlobalTheory.QCoh.resAlgebra (X := B.X) hle
  letI := GlobalTheory.QCoh.resModule Om.V hle
  haveI := GlobalTheory.QCoh.res_isScalarTower Om.V hle
  induction s using (isBaseChange_resLinear Om.V U.2.1 U'.2.1 hle).inductionOn with
  | zero =>
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · rw [map_zero, map_zero]; rfl
    · exact rho_zero _
    · rw [map_zero, map_zero, map_zero]
  | tmul s =>
    obtain ⟨y, hz⟩ := rho_rep D (pullbackSections f.f Om.V le_rfl s)
    obtain ⟨x, hx⟩ : y.1 ∈ latOf (ι 0) _ := hfit.le y.2
    have h1 := hR _ x y hx.symm hz
    obtain ⟨y₁, e₁, h2⟩ := rho_map hM (hm s) hz
    obtain ⟨y₂, e₂, h3⟩ := rho_map hM' (hm' s) h2
    refine ⟨resM (E 0) (f.f.preimage_mono hle) x, y₂, ?_, h3, ?_⟩
    · rw [crd_resM, hx, e₂, e₁]
      funext i
      exact (hc.2.2.2.2 U U' hle _).symm
    · rw [GlobalTheory.Twist.app_resM, ← h1]
      refine Eq.trans (congrArg _ ?_) (GlobalTheory.Twist.app_resM ρ (f.f.preimage_mono hle) _)
      exact (pullbackSections_res f.f Om.V le_rfl hle s).trans
        (res_pullbackSections f.f Om.V le_rfl (f.f.preimage_mono hle) s).symm
  | smul a s ih =>
    obtain ⟨x, y, h1, h2, h3⟩ := ih
    refine ⟨(f.f.app U'.1).hom a • x, algebraMap Γ(B.X, U'.1) U'.Bp a • y, ?_, ?_, ?_⟩
    · rw [map_smul, LinearMap.map_smulₛₗ, hc.2.2.2.1, ← h1]; rfl
    · exact rho_smul _ a s y h2
    · rw [pullbackSections_smul, Scheme.Hom.appLE_eq_app, Scheme.Modules.Hom.app_smul, ← h3]
      exact Scheme.Modules.Hom.app_smul ρ _ _
  | add s s' ih ih' =>
    obtain ⟨x, y, h1, h2, h3⟩ := ih
    obtain ⟨x', y', h1', h2', h3'⟩ := ih'
    refine ⟨x + x', y + y', ?_, ?_, ?_⟩
    · rw [map_add, map_add, ← h1, ← h1']; rfl
    · exact rho_add _ s s' y y' h2 h2'
    · rw [map_add, map_add, map_add, h3, h3']

end GlobalTheory.ChainDesc

end
