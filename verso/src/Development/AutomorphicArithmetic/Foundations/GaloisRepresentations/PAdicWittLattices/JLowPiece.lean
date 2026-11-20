import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open Formalism.ConjugateSelfDual (Qbar)
universe u v

/- English proof (translation)
Set `f' : W₁ →ₗ[K] W₀` to `f.restrict hW`. Establish `hf' : Function.Injective f'` using `fun x y h => Subtype.ext (hf (congrArg Subtype.val h))`. Set `A` to `LinearMap.toMatrix b₁ b₀ f'`. Establish `hA : ∀ j, f (b₁ j).1 = ∑ i, A i j • (b₀ i).1`. Introduce `j`.

Establish `e2` using `congrArg W₀.subtype (b₀.sum_repr (f' (b₁ j)))`. Rewrite `e2` using `[map_sum]`. Simplify using `only [map_smul, Submodule.subtype_apply] at e2`. Simplify using `only [A, LinearMap.toMatrix_apply]`. Conclude with `e2.symm`.

Use `⟨A, ?_, fun σ => ?_⟩` and prove the remaining obligations. Introduce `v w h`. Establish `key : ∀ u : Fin d₁ → K, A.mulVec u = b₀.repr (f' (b₁.equivFun.symm u))`. Introduce `u`. Establish `hu : ⇑(b₁.repr (b₁.equivFun.symm u)) = u`.

Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Use `LinearMap.toMatrix_mulVec_repr b₁ b₀ f' (b₁.equivFun.symm u)` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`. Rewrite `h` using `[key, key]`.

Conclude with `b₁.equivFun.symm.injective (hf' (b₀.repr.injective (Finsupp.ext fun i => congrFun h i)))`. Establish `hli : LinearIndependent K (fun i => (b₀ i).1)` using `b₀.linearIndependent.map' W₀.subtype (Submodule.ker_subtype _)`. Use extensionality with `i j`. Establish `e₁ : g₀ σ (f (b₁ j).1) = ∑ i, (ρ₀ σ * A) i j • (b₀ i).1`. Rewrite using `[hA, map_sum]`.

Simplify using `only [map_smul, h₀, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`. Establish `e₂ : f (g₁ σ (b₁ j).1) = ∑ i, (A * ρ₁ σ) i j • (b₀ i).1`. Rewrite using `[h₁, map_sum]`.

Simplify using `only [map_smul, hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`. Establish `e₃ : ∑ i, ((ρ₀ σ * A) i j - (A * ρ₁ σ) i j) • (b₀ i).1 = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[← e₁, ← e₂, hc, sub_self]`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.1 hli _ e₃ i)`.
-/
private theorem intertwine_of_restrict {K V₁ V₀ G : Type*} [Field K] [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₀] [Module K V₀] (f : V₁ →ₗ[K] V₀) (hf : Function.Injective f) {d₁ d₀ : ℕ}
    (W₁ : Submodule K V₁) (W₀ : Submodule K V₀) (b₁ : Module.Basis (Fin d₁) K W₁)
    (b₀ : Module.Basis (Fin d₀) K W₀) (hW : ∀ x ∈ W₁, f x ∈ W₀)
    (g₁ : G → V₁ →ₗ[K] V₁) (g₀ : G → V₀ →ₗ[K] V₀) (hc : ∀ σ x, g₀ σ (f x) = f (g₁ σ x))
    (ρ₁ : G → Matrix (Fin d₁) (Fin d₁) K) (ρ₀ : G → Matrix (Fin d₀) (Fin d₀) K)
    (h₁ : ∀ σ j, g₁ σ (b₁ j).1 = ∑ i, ρ₁ σ i j • (b₁ i).1)
    (h₀ : ∀ σ j, g₀ σ (b₀ j).1 = ∑ i, ρ₀ σ i j • (b₀ i).1) :
    ∃ A : Matrix (Fin d₀) (Fin d₁) K, Function.Injective A.mulVec ∧ ∀ σ, ρ₀ σ * A = A * ρ₁ σ := by
  let f' : W₁ →ₗ[K] W₀ := f.restrict hW
  have hf' : Function.Injective f' := fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h))
  let A := LinearMap.toMatrix b₁ b₀ f'
  have hA : ∀ j, f (b₁ j).1 = ∑ i, A i j • (b₀ i).1 := by
    intro j
    have e2 := congrArg W₀.subtype (b₀.sum_repr (f' (b₁ j)))
    rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simp only [A, LinearMap.toMatrix_apply]
    exact e2.symm
  refine ⟨A, ?_, fun σ => ?_⟩
  · intro v w h
    have key : ∀ u : Fin d₁ → K, A.mulVec u = b₀.repr (f' (b₁.equivFun.symm u)) := by
      intro u
      have hu : ⇑(b₁.repr (b₁.equivFun.symm u)) = u := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      have := LinearMap.toMatrix_mulVec_repr b₁ b₀ f' (b₁.equivFun.symm u)
      rw [hu] at this
      exact this
    rw [key, key] at h
    exact b₁.equivFun.symm.injective (hf' (b₀.repr.injective (Finsupp.ext fun i => congrFun h i)))
  · have hli : LinearIndependent K (fun i => (b₀ i).1) :=
      b₀.linearIndependent.map' W₀.subtype (Submodule.ker_subtype _)
    ext i j
    have e₁ : g₀ σ (f (b₁ j).1) = ∑ i, (ρ₀ σ * A) i j • (b₀ i).1 := by
      rw [hA, map_sum]
      simp only [map_smul, h₀, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₂ : f (g₁ σ (b₁ j).1) = ∑ i, (A * ρ₁ σ) i j • (b₀ i).1 := by
      rw [h₁, map_sum]
      simp only [map_smul, hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₃ : ∑ i, ((ρ₀ σ * A) i j - (A * ρ₁ σ) i j) • (b₀ i).1 = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← e₁, ← e₂, hc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.1 hli _ e₃ i)

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, bcMap_fst, galMap_fst, bcMap_fst, galMap_fst_assoc]`. Rewrite using `[Category.assoc, Category.assoc, bcMap_snd, galMap_snd, galMap_snd, reassoc_of% bcMap_snd]`.
-/
private theorem galMap_bcMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ sp k} {q : Y ⟶ sp k} (f : Y ⟶ X) (h : f ≫ p = q) (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω q σ ≫ bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h =
      bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h ≫ galMap Ω p σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, galMap_fst, bcMap_fst, galMap_fst_assoc]
  · rw [Category.assoc, Category.assoc, bcMap_snd, galMap_snd, galMap_snd, reassoc_of% bcMap_snd]

/- English proof (translation)
Introduce `hL hP E Ω _ _ _ _ _ l _ H θ O _ _ C D hN hO d₁ d₀ ρ₁ ρ₀ ⟨b₁, h₁⟩ ⟨b₀, h₀⟩`. Establish `hl : (l : E) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`. Take `⟨hinj, -⟩` from `hP l hl C hO Ω`. Establish `hop'` using `fun g => hL l hl C D hN Ω g`. Set `P : Htot l (sch.obj ((low D).geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω))` to `(etG l E Ω).pull (piK C) (piK_snd C)`.

Establish `hop'' : ∀ g, hop l H Ω g ∘ₗ P = (D.m g : ℚ_[l]) • (P ∘ₗ hop l (low D) Ω g)` using `hop'`. Establish `hinj' : Function.Injective (P.baseChange (Qbar l))` using `hinj`. Establish `hW : ∀ x ∈ piece l (low D) Ω (Qbar l) (fun g => θ g / D.m g), P.baseChange (Qbar l) x ∈ piece l H Ω (Qbar l) θ`. Introduce `x hx`. Simplify using `only [piece, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢`.

Introduce `g`. Establish `hm : ((D.m g : ℕ) : Qbar l) ≠ 0` using `Nat.cast_ne_zero.mpr (D.lies g).1.ne'`. Establish `e : (hop l H Ω g).baseChange (Qbar l) (P.baseChange (Qbar l) x) = ((hop l H Ω g ∘ₗ P).baseChange (Qbar l)) x`. Rewrite using `[LinearMap.baseChange_comp]`. Both sides reduce to the same expression.

Rewrite using `[e, hop'', LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.baseChange_comp, LinearMap.comp_apply, hx g, map_smul, ← algebraMap_smul (Qbar l) (D.m g : ℚ_[l]), map_natCast, smul_smul, mul_div_cancel₀ _ hm]`. Establish `hc : ∀ (σ : Ω ≃ₐ[E] Ω) x, galV l H Ω (Qbar l) σ (P.baseChange (Qbar l) x) = P.baseChange (Qbar l) (galV l (low D) Ω (Qbar l) σ x)`. Introduce `σ x`. Establish `e : galTot l Ω H.q σ ∘ₗ P = P ∘ₗ galTot l Ω (low D).q σ`. Establish `e'` using `congrArg (fun u => pullTot l (sch.map u)) (galMap_bcMap (Ω := Ω) (piK C) (piK_snd C) σ)`.

Simplify using `only [Functor.map_comp, pullTot_comp] at e'`. Conclude with `e'`. Establish `e2` using `congrArg (fun u => LinearMap.baseChange (Qbar l) u x) e`. Simplify using `only [LinearMap.baseChange_comp] at e2`. Conclude with `e2`.

Conclude with `intertwine_of_restrict _ hinj' _ _ b₁ b₀ hW (galV l (low D) Ω (Qbar l)) (galV l H Ω (Qbar l)) hc (fun σ => (ρ₁ σ).val) (fun σ => (ρ₀ σ).val) h₁ h₀`.
-/
theorem UpperTheory.Gal.G3.jLowPiece :
    HopLies → PieceLe → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := by
  intro hL hP E Ω _ _ _ _ _ l _ H θ O _ _ C D hN hO d₁ d₀ ρ₁ ρ₀ ⟨b₁, h₁⟩ ⟨b₀, h₀⟩
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  obtain ⟨hinj, -⟩ := hP l hl C hO Ω
  have hop' := fun g => hL l hl C D hN Ω g
  let P : Htot l (sch.obj ((low D).geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    (etG l E Ω).pull (piK C) (piK_snd C)
  have hop'' : ∀ g, hop l H Ω g ∘ₗ P = (D.m g : ℚ_[l]) • (P ∘ₗ hop l (low D) Ω g) := hop'
  have hinj' : Function.Injective (P.baseChange (Qbar l)) := hinj
  have hW : ∀ x ∈ piece l (low D) Ω (Qbar l) (fun g => θ g / D.m g),
      P.baseChange (Qbar l) x ∈ piece l H Ω (Qbar l) θ := by
    intro x hx
    simp only [piece, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro g
    have hm : ((D.m g : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
    have e : (hop l H Ω g).baseChange (Qbar l) (P.baseChange (Qbar l) x) =
        ((hop l H Ω g ∘ₗ P).baseChange (Qbar l)) x := by
      rw [LinearMap.baseChange_comp]; rfl
    rw [e, hop'', LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx g, map_smul, ← algebraMap_smul (Qbar l) (D.m g : ℚ_[l]), map_natCast,
      smul_smul, mul_div_cancel₀ _ hm]
  have hc : ∀ (σ : Ω ≃ₐ[E] Ω) x, galV l H Ω (Qbar l) σ (P.baseChange (Qbar l) x) =
      P.baseChange (Qbar l) (galV l (low D) Ω (Qbar l) σ x) := by
    intro σ x
    have e : galTot l Ω H.q σ ∘ₗ P = P ∘ₗ galTot l Ω (low D).q σ := by
      have e' := congrArg (fun u => pullTot l (sch.map u))
        (galMap_bcMap (Ω := Ω) (piK C) (piK_snd C) σ)
      simp only [Functor.map_comp, pullTot_comp] at e'
      exact e'
    have e2 := congrArg (fun u => LinearMap.baseChange (Qbar l) u x) e
    simp only [LinearMap.baseChange_comp] at e2
    exact e2
  exact intertwine_of_restrict _ hinj' _ _ b₁ b₀ hW (galV l (low D) Ω (Qbar l)) (galV l H Ω (Qbar l)) hc
    (fun σ => (ρ₁ σ).val) (fun σ => (ρ₀ σ).val) h₁ h₀
