import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨h1.const_smul c, h2.mono (Function.support_const_smul_subset c ψ), ?_⟩` and prove the remaining obligations. Introduce `d₁ d₂ e₁ e₂`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[integral_const_mul, h3 d₁ d₂ e₁ e₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lefAt_smul {a b : ℕ} [MeasurableSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)]
    {ν₁ : Measure (GL (Fin a) ℂ)} {ν₂ : Measure (GL (Fin b) ℂ)} {l₁ : DomWeight a} {l₂ : DomWeight b}
    {val : ℂ} {ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ} (c : ℂ) (h : LefAt ν₁ ν₂ l₁ l₂ val ψ) :
    LefAt ν₁ ν₂ l₁ l₂ (c * val) (c • ψ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.const_smul c, h2.mono (Function.support_const_smul_subset c ψ), ?_⟩
  intro d₁ d₂ e₁ e₂
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h3 d₁ d₂ e₁ e₂]
  ring

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀), ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ v₀), Function.update_self, mul_assoc]`. Use `congr 2`. Conclude with `Finset.prod_congr rfl fun v hv => Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _`.
-/
private theorem prod_update_mul {V : Type*} [Fintype V] [DecidableEq V] (g : V → ℂ) (v₀ : V) (c : ℂ) :
    ∏ v, Function.update g v₀ (c * g v₀) v = c * ∏ v, g v := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ v₀), Function.update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun v hv => Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [adel, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc]`. Use `congr 1`. Rewrite using `[← prod_update_mul (fun v => ψ v (GeneralLinearGroup.map (cV v) x.1, GeneralLinearGroup.map (cV v) x.2)) v₀ c]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v = v₀`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hv]`.
-/
private theorem adel_update {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (S : Set (Pl E))
    (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (v₀ : InfinitePlace E) (c : ℂ) :
    adel S u₁ u₂ (Function.update ψ v₀ (c • ψ v₀)) φ₁ φ₂ = c • adel S u₁ u₂ ψ φ₁ φ₂ := by
  funext x
  simp only [adel, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← prod_update_mul (fun v => ψ v (GeneralLinearGroup.map (cV v) x.1, GeneralLinearGroup.map (cV v) x.2)) v₀ c]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v = v₀
  · subst hv
    simp
  · simp [Function.update_of_ne hv]

/- English proof (translation)
Introduce `hE E _ _ _ n μ e lam C S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg val ψ hL s z hz`. Take `⟨v₀⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hL' : ∀ i v, LefAt (C.νC (C.a i)) (C.νC (n - C.a i)) (C.l₁ i v) (C.l₂ i v) (Function.update (val i) v₀ (s i * val i v₀) v) (Function.update (ψ i) v₀ (s i • ψ i v₀) v)`. Introduce `i v`. Distinguish the cases in `hv : v = v₀`.

Substitute `hv` using the available equality. Simplify using `using lefAt_smul (s i) (hL i v)`. Simplify `hL i v` using `[Function.update_of_ne hv]`. Establish `hz' : ∀ i, ∏ v, Function.update (val i) v₀ (s i * val i v₀) v = z` using `fun i => by`. Rewrite using `[prod_update_mul, hz i]`.

Establish `key` using `C.eq S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg _ _ hL' z hz'`. Rewrite using `[key]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[adel_update, hE]`.
-/
theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.chainsc_pf :
    FBL.EllHom → ChainSc := by
  intro hE E _ _ _ n μ e lam C S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg val ψ hL s z hz
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hL' : ∀ i v, LefAt (C.νC (C.a i)) (C.νC (n - C.a i)) (C.l₁ i v) (C.l₂ i v)
      (Function.update (val i) v₀ (s i * val i v₀) v) (Function.update (ψ i) v₀ (s i • ψ i v₀) v) := by
    intro i v
    by_cases hv : v = v₀
    · subst hv
      simpa using lefAt_smul (s i) (hL i v)
    · simpa [Function.update_of_ne hv] using hL i v
  have hz' : ∀ i, ∏ v, Function.update (val i) v₀ (s i * val i v₀) v = z := fun i => by
    rw [prod_update_mul, hz i]
  have key := C.eq S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg _ _ hL' z hz'
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adel_update, hE]

end
