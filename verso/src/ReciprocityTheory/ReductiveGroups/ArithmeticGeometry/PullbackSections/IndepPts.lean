import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.JInjCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DetAlg
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

variable {K : Type} [Field K]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
    (S →ₐ[K] T) → pts S → pts T → Prop)

/- English proof (translation)
Establish `hT : FromTest pts mapR w` using `⟨p, φ, y, h⟩`. Unfold `evalAt`. Rewrite using `[dif_pos hT]`. Conclude with `hWD f hf S _ p _ φ _ y w hT.choose_spec.choose_spec.choose_spec h`.
-/
theorem evalAt_eq_of (hWD : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (w : pts S)
    (h : mapR φ y w) : evalAt pts mapR f w = φ (f p y) := by
  have hT : FromTest pts mapR w := ⟨p, φ, y, h⟩
  unfold evalAt
  rw [dif_pos hT]
  exact hWD f hf S _ p _ φ _ y w hT.choose_spec.choose_spec.choose_spec h

/- English proof (translation)
Use `haveI : CharZero K := (algebraMap K ℂ).charZero`. Set `F` to `AlgebraicClosure K`. Use `haveI : IsAlgClosed ℂ := Complex.isAlgClosed`. Use `haveI : Normal K F := IsAlgClosure.normal K F`. Use `haveI : Algebra.IsSeparable K F := IsAlgClosure.separable K F`.

Use `haveI : IsGalois K F := ⟨⟩`. Set `ι : F →ₐ[K] ℂ` to `IsAlgClosed.lift`. Set `Pt` to `Σ p : TRing K, pts p.R × (p.R →ₐ[K] F)`. Set `v : Rules pts →ₗ[K] (Pt → F)` to `{ toFun := fun f q => q.2.2 (f q.1 q.2.1) map_add' := by`. Introduce `f g`.

Use function extensionality and compare the values at `q`. Express the relevant statement in the definitionally equal form `q.2.2 (f q.1 q.2.1 + g q.1 q.2.1) = q.2.2 (f q.1 q.2.1) + q.2.2 (g q.1 q.2.1)`. Conclude with `map_add _ _ _`. Use the proof step `map_smul' := by`. Introduce `a f`.

Use function extensionality and compare the values at `q`. Express the relevant statement in the definitionally equal form `q.2.2 (a • f q.1 q.2.1) = a • q.2.2 (f q.1 q.2.1)`. Conclude with `map_smul _ _ _ }`. Set `act : (F ≃ₐ[K] F) → Pt → Pt` to `fun g q => ⟨q.1, q.2.1, (g : F →ₐ[K] F).comp q.2.2⟩`. Establish `hbij : ∀ g, Function.Bijective (act g)`.

Introduce `g`. Use `Function.bijective_iff_has_inverse.mpr ⟨act g.symm, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨p, y, φ⟩`. Conclude with `Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))`. Introduce and unpack `⟨p, y, φ⟩`.

Conclude with `Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))`. Establish `heq : ∀ g f y, v f (act g y) = g (v f y)` using `fun _ _ _ => rfl`. Establish `hinj : Function.Injective v`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `f hf0`.

Use function extensionality and compare the values at `p y`. Apply `detAlg_holds K p.n p.I p.3 (f p y)` to reduce the goal to its premises. Introduce `L _ _ _ φ`. Set `e : L →ₐ[K] F` to `IsAlgClosed.lift`. Establish `h1 : e (φ (f p y)) = 0` using `congrFun hf0 ⟨p, y, e.comp φ⟩`.

Conclude with `e.toRingHom.injective (h1.trans (map_zero e).symm)`. Establish `hli` using `indepDescent_holds K F ι.toRingHom (Rules pts) Pt v act hbij heq hinj n b hb`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `i`. Use `hli c ?_ i` and prove the remaining obligations.

Use function extensionality and compare the values at `q`. Take `⟨p, y, φ⟩` from `q`. Set `ψ : p.R →ₐ[K] ℂ` to `ι.comp φ`. Take `⟨z, hz⟩` from `hBC p ψ y`. Establish `h0` using `hc z ⟨p, ψ, y, hz⟩`.

Simplify using `only [evalAt_eq_of pts mapR hWD (b _) (hnat _) p ψ y z hz] at h0`. Simplify `h0` using `[Finset.sum_apply, v, ψ]`.
-/
theorem indep_of_complex [Algebra K ℂ] (hWD : EvalWD pts mapR)
    (hBC : ∀ (p : TRing K) (φ : p.R →ₐ[K] ℂ) (y : pts p.R), ∃ z : pts ℂ, mapR φ y z)
    {n : ℕ} (b : Fin n → Rules pts) (hnat : ∀ i, IsNatural pts mapR (b i)) (hb : LinearIndependent K b)
    (c : Fin n → ℂ) (hc : ∀ z : pts ℂ, FromTest pts mapR z → ∑ i, c i * evalAt pts mapR (b i) z = 0) :
    c = 0 := by
  classical
  haveI : CharZero K := (algebraMap K ℂ).charZero
  let F := AlgebraicClosure K
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI : Normal K F := IsAlgClosure.normal K F
  haveI : Algebra.IsSeparable K F := IsAlgClosure.separable K F
  haveI : IsGalois K F := ⟨⟩
  let ι : F →ₐ[K] ℂ := IsAlgClosed.lift
  let Pt := Σ p : TRing K, pts p.R × (p.R →ₐ[K] F)
  let v : Rules pts →ₗ[K] (Pt → F) :=
    { toFun := fun f q => q.2.2 (f q.1 q.2.1)
      map_add' := by
        intro f g; funext q
        change q.2.2 (f q.1 q.2.1 + g q.1 q.2.1) = q.2.2 (f q.1 q.2.1) + q.2.2 (g q.1 q.2.1)
        exact map_add _ _ _
      map_smul' := by
        intro a f; funext q
        change q.2.2 (a • f q.1 q.2.1) = a • q.2.2 (f q.1 q.2.1)
        exact map_smul _ _ _ }
  let act : (F ≃ₐ[K] F) → Pt → Pt := fun g q => ⟨q.1, q.2.1, (g : F →ₐ[K] F).comp q.2.2⟩
  have hbij : ∀ g, Function.Bijective (act g) := by
    intro g
    refine Function.bijective_iff_has_inverse.mpr ⟨act g.symm, ?_, ?_⟩
    · rintro ⟨p, y, φ⟩
      exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))
    · rintro ⟨p, y, φ⟩
      exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))
  have heq : ∀ g f y, v f (act g y) = g (v f y) := fun _ _ _ => rfl
  have hinj : Function.Injective v := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf0
    funext p y
    apply detAlg_holds K p.n p.I p.3 (f p y)
    intro L _ _ _ φ
    let e : L →ₐ[K] F := IsAlgClosed.lift
    have h1 : e (φ (f p y)) = 0 := congrFun hf0 ⟨p, y, e.comp φ⟩
    exact e.toRingHom.injective (h1.trans (map_zero e).symm)
  have hli := indepDescent_holds K F ι.toRingHom (Rules pts) Pt v act hbij heq hinj n b hb
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli c ?_ i
  funext q
  obtain ⟨p, y, φ⟩ := q
  let ψ : p.R →ₐ[K] ℂ := ι.comp φ
  obtain ⟨z, hz⟩ := hBC p ψ y
  have h0 := hc z ⟨p, ψ, y, hz⟩
  simp only [evalAt_eq_of pts mapR hWD (b _) (hnat _) p ψ y z hz] at h0
  simpa [Finset.sum_apply, v, ψ] using h0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
