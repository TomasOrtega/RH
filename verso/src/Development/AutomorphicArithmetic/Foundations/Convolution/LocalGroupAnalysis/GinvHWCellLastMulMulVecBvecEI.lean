import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmHasse
open PositivityTheory.Rg.Tf.Geo

noncomputable section

open NumberField IsDedekindDomain Polynomial PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.D
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.G

/- English proof (translation)
Unfold `twNorm nm`. Rewrite using `[map_list_prod, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun i hi => ?_` and prove the remaining obligations. Use `clear hi`.

Simplify using `only [Function.comp_apply]`. Proceed by induction on `i with`. Consider the case `zero`. Use extensionality with `a b`. Both sides reduce to the same expression.

Consider the case `succ i ih`. Use `(congrArg (mapGL n p) (pow_succ_apply' (G := GL (Fin n) B) (mapGL n s) i δ)).trans ?_` and prove the remaining obligations. Use extensionality with `a b`. Use `congrArg (fun g : GL (Fin n) R => τ ((g : Matrix (Fin n) (Fin n) R) a b)) ih` as an intermediate fact. Use `(h _).trans (this.trans ?_)` and prove the remaining obligations.

Rewrite using `[pow_succ']`. Both sides reduce to the same expression.
-/
private theorem map_twNorm {n : ℕ} {k R B : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing B]
    (p : B →+* R) (s : B →+* B) (τ : R ≃ₐ[k] R) (h : ∀ b, p (s b) = τ (p b)) (q : ℕ) (δ : GL (Fin n) B) :
    mapGL n p (twNorm (mapGL n s) q δ) = nm τ q (mapGL n p δ) := by
  unfold twNorm nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  clear hi
  simp only [Function.comp_apply]
  induction i with
  | zero =>
    ext a b
    rfl
  | succ i ih =>
    refine (congrArg (mapGL n p) (pow_succ_apply' (G := GL (Fin n) B) (mapGL n s) i δ)).trans ?_
    ext a b
    have := congrArg (fun g : GL (Fin n) R => τ ((g : Matrix (Fin n) (Fin n) R) a b)) ih
    refine (h _).trans (this.trans ?_)
    rw [pow_succ']
    rfl

/- English proof (translation)
Set `ψ : E ⊗[F] A →ₐ[F] k ⊗[F] E` to `(Algebra.TensorProduct.comm F E k).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id F E) φ)`. Establish `hψ : ∀ x a, ψ (x ⊗ₜ a) = φ a ⊗ₜ x` using `fun x a => by simp [ψ]`. Set `p : B →+* k ⊗[F] E` to `(ψ : E ⊗[F] A →+* k ⊗[F] E).comp (e.symm : B →+* E ⊗[F] A)`. Establish `hp : ∀ z, p (e z) = ψ z` using `fun z => by simp [p]`. Establish `h1 : ∀ b, p (galOf e σ b) = ext k σ (p b)`.

Introduce `b`. Take `⟨z, rfl⟩` from `e.surjective b`. Establish `: galOf e σ (e z) = e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) z)`. Simplify using `[galOf]`. Rewrite using `[this, hp, hp]`.

Use `clear this`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a => simp [hψ, D.ext]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Use `⟨mapGL n p δ, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_twNorm p _ _ h1, hδ, cp, cp, ← Matrix.charpoly_map]`. Use `congr 1`. Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `p (ι (algebraMap F A _)) = inc k (algebraMap F E _)`.

Rewrite using `[← hι, hp, hψ, φ.commutes]`. Express the relevant statement in the definitionally equal form `_ = (1 : k) ⊗ₜ[F] algebraMap F E _`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
private theorem transport {n : ℕ} {F E A B k : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] [CommRing k] [Algebra F k]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (ι : A →+* B) (hι : ∀ a, e (1 ⊗ₜ a) = ι a) (φ : A →ₐ[F] k)
    (γ : GL (Fin n) F) (q : ℕ) (δ : GL (Fin n) B)
    (hδ : twNorm (mapGL n (galOf e σ)) q δ = mapGL n ι (mapGL n (algebraMap F A) γ)) :
    ∃ d, cp (nm (ext k σ) q (n := n) d) = (cp γ).map ((inc k).comp (algebraMap F E)) := by
  let ψ : E ⊗[F] A →ₐ[F] k ⊗[F] E :=
    (Algebra.TensorProduct.comm F E k).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id F E) φ)
  have hψ : ∀ x a, ψ (x ⊗ₜ a) = φ a ⊗ₜ x := fun x a => by simp [ψ]
  let p : B →+* k ⊗[F] E := (ψ : E ⊗[F] A →+* k ⊗[F] E).comp (e.symm : B →+* E ⊗[F] A)
  have hp : ∀ z, p (e z) = ψ z := fun z => by simp [p]
  have h1 : ∀ b, p (galOf e σ b) = ext k σ (p b) := by
    intro b
    obtain ⟨z, rfl⟩ := e.surjective b
    have : galOf e σ (e z) = e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) z) := by
      simp [galOf]
    rw [this, hp, hp]
    clear this
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x a => simp [hψ, D.ext]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨mapGL n p δ, ?_⟩
  rw [← map_twNorm p _ _ h1, hδ, cp, cp, ← Matrix.charpoly_map]
  congr 1
  ext a b
  change p (ι (algebraMap F A _)) = inc k (algebraMap F E _)
  rw [← hι, hp, hψ, φ.commutes]
  change _ = (1 : k) ⊗ₜ[F] algebraMap F E _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end UpperTheory.ConvolutionTheory.G

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ _ σ hσ n _ _ γ hγ hinf hfin`. Take `⟨a, ha, -⟩` from `nmHasse F E σ hσ n γ hγ.separable (fun v => by`. Take `⟨δ, hδ⟩` from `hfin v`. Use `transport (tensorEquiv' E v) σ (incFin E v) (fun a => ?_) (AlgHom.id F _) γ _ δ (hδ.trans ?_)` and prove the remaining obligations. Rewrite using `[tensorEquiv'_tmul, map_one, one_mul]`.

Both sides reduce to the same expression. Use `congr 1) (fun v => by`. Take `⟨δ, hδ⟩` from `hinf`. Use `transport (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (fun a => ?_) (Pi.evalAlgHom F (fun v : InfinitePlace F => v.Completion) v) γ _ δ (hδ.trans ?_)` and prove the remaining obligations. Rewrite using `[GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]`.

Use `congr 1)`. Use `⟨a, Eq.trans ?_ ha⟩` and prove the remaining obligations. Conclude with `map_twNorm (RingHom.id E) (σ : E →+* E) σ (fun _ => rfl) _ a`.
-/
theorem UpperTheory.ConvolutionTheory.G.ginvH_wCell_last_mul_mulVec_bvec_eI :
    GlobalTheory.Published.HasseNorm → H1 := by
  intro _ F E _ _ _ _ _ _ σ hσ n _ _ γ hγ hinf hfin
  obtain ⟨a, ha, -⟩ := nmHasse F E σ hσ n γ hγ.separable (fun v => by
    obtain ⟨δ, hδ⟩ := hfin v
    refine transport (tensorEquiv' E v) σ (incFin E v) (fun a => ?_) (AlgHom.id F _) γ _ δ (hδ.trans ?_)
    · rw [tensorEquiv'_tmul, map_one, one_mul]
      rfl
    · congr 1) (fun v => by
    obtain ⟨δ, hδ⟩ := hinf
    refine transport (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (fun a => ?_)
      (Pi.evalAlgHom F (fun v : InfinitePlace F => v.Completion) v) γ _ δ (hδ.trans ?_)
    · rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    · congr 1)
  refine ⟨a, Eq.trans ?_ ha⟩
  exact map_twNorm (RingHom.id E) (σ : E →+* E) σ (fun _ => rfl) _ a
