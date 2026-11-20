import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `hA E _ _ _ a C hC ℓ hℓ W f c`. Set `e : UA E a → UA E a` to `fun g => (((ℓ g)⁻¹ * c : C) : UA E a)`. Establish `he : ∀ g, e g ∈ finU E a` using `fun g => hC.fin ((ℓ g)⁻¹ * c).2`. Set `F : W.Sp →ₗ[ℂ] (UA E a → ℂ)` to `{ toFun := fun v g => f.1 v (g * e g) map_add' := fun v w => by funext g; simp map_smul' := fun r v => by funext g; simp }`. Establish `hF : ∀ v g, F v g = f.1 v (g * e g)` using `fun _ _ => rfl`.

Establish `hleft : ∀ γ ∈ ratU E a, ∀ v g, F v (γ * g) = F v g`. Introduce `γ hγ v g`. Establish `h : e (γ * g) = e g` using `by simp only [e, hℓ.left γ hγ g]`. Rewrite using `[hF, hF, h, mul_assoc]`. Conclude with `(f.2.1 v).left γ hγ _`.

Establish `hlev : ∀ k ∈ C, ∀ v g, F v (g * k) = F v g`. Introduce `k hk v g`. Establish `h : g * k * e (g * k) = g * e g`. Simplify using `only [e, hℓ.lev ⟨k, hk⟩ g, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`.

Rewrite using `[hF, hF, h]`. Establish `hinf : ∀ x ∈ infU E a, ∀ v g, F v (g * x) = f.1 v (g * x * e g)`. Introduce `x hx v g`. Establish `h : e (g * x) = e g` using `by simp only [e, hℓ.inf x hx g]`. Rewrite using `[hF, h]`.

Establish `heqv : ∀ (x : infU E a) v, F (W.rep x v) = RU E a x (F v)`. Introduce `x v`. Use function extensionality and compare the values at `g`. Rewrite using `[RU_apply, hinf x x.2, hF, f.2.2 x v, RU_apply, mul_assoc g, mul_assoc g, fin_mul_inf (he g) x.2]`. Establish `haut : ∀ v, IsAutFormU (F v)`.

Introduce `v`. Use `hA E a C hC (F v) (fun γ hγ g => hleft γ hγ v g) (fun k hk g => hlev k hk v g) ?_ (LinearMap.range F) inferInstance fun x hx => ⟨W.rep ⟨x, hx⟩ v, heqv ⟨x, hx⟩ v⟩` and prove the remaining obligations. Introduce `g`. Establish `h : (fun x : infU E a => F v (g * x)) = fun x : infU E a => f.1 v (g * x * e g)`. Use function extensionality and compare the values at `fun x => hinf x x.2 v g`.

Rewrite using `[h]`. Conclude with `(f.2.1 v).cont.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)`. Conclude with `⟨⟨F, haut, heqv⟩, UpperTheory.Gal.Gen.mem_fixedBy.2 fun k hk v g => hlev k hk v g, fun _ _ => rfl⟩`.
-/
theorem UpperTheory.Gal.Wt.twist_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.Twist := by
  intro hA E _ _ _ a C hC ℓ hℓ W f c
  let e : UA E a → UA E a := fun g => (((ℓ g)⁻¹ * c : C) : UA E a)
  have he : ∀ g, e g ∈ finU E a := fun g => hC.fin ((ℓ g)⁻¹ * c).2
  let F : W.Sp →ₗ[ℂ] (UA E a → ℂ) :=
    { toFun := fun v g => f.1 v (g * e g)
      map_add' := fun v w => by funext g; simp
      map_smul' := fun r v => by funext g; simp }
  have hF : ∀ v g, F v g = f.1 v (g * e g) := fun _ _ => rfl
  have hleft : ∀ γ ∈ ratU E a, ∀ v g, F v (γ * g) = F v g := by
    intro γ hγ v g
    have h : e (γ * g) = e g := by simp only [e, hℓ.left γ hγ g]
    rw [hF, hF, h, mul_assoc]
    exact (f.2.1 v).left γ hγ _
  have hlev : ∀ k ∈ C, ∀ v g, F v (g * k) = F v g := by
    intro k hk v g
    have h : g * k * e (g * k) = g * e g := by
      simp only [e, hℓ.lev ⟨k, hk⟩ g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hF, hF, h]
  have hinf : ∀ x ∈ infU E a, ∀ v g, F v (g * x) = f.1 v (g * x * e g) := by
    intro x hx v g
    have h : e (g * x) = e g := by simp only [e, hℓ.inf x hx g]
    rw [hF, h]
  have heqv : ∀ (x : infU E a) v, F (W.rep x v) = RU E a x (F v) := by
    intro x v
    funext g
    rw [RU_apply, hinf x x.2, hF, f.2.2 x v, RU_apply, mul_assoc g, mul_assoc g, fin_mul_inf (he g) x.2]
  have haut : ∀ v, IsAutFormU (F v) := by
    intro v
    refine hA E a C hC (F v) (fun γ hγ g => hleft γ hγ v g) (fun k hk g => hlev k hk v g) ?_
      (LinearMap.range F) inferInstance fun x hx => ⟨W.rep ⟨x, hx⟩ v, heqv ⟨x, hx⟩ v⟩
    intro g
    have h : (fun x : infU E a => F v (g * x)) = fun x : infU E a => f.1 v (g * x * e g) :=
      funext fun x => hinf x x.2 v g
    rw [h]
    exact (f.2.1 v).cont.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  exact ⟨⟨F, haut, heqv⟩, UpperTheory.Gal.Gen.mem_fixedBy.2 fun k hk v g => hlev k hk v g, fun _ _ => rfl⟩
