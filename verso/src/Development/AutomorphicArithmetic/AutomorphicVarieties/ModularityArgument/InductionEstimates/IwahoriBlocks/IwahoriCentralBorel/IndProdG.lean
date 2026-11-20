import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndSeed
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrCases

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

noncomputable section

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Tools

variable {G V Y H : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [Group H]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qe20.irrCases ρ h W hW`.
-/
private theorem irrCases (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe20.irrCases ρ h W hW

/- English proof (translation)
Use `{ toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Conclude with `bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)`. Break down `h S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e` into its components or cases. Conclude with `Or.inl (Subrepresentation.ext e)`. Conclude with `Or.inr (Subrepresentation.ext e)`.
-/
private theorem irrOf (ρ : Representation ℂ G V) (hn : Nontrivial V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) : ρ.IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · rcases h S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · exact Or.inl (Subrepresentation.ext e)
    · exact Or.inr (Subrepresentation.ext e)

/- English proof (translation)
Establish `e1 : y (a, 1) (y (1, b) v) = y (a, b) v`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Establish `e2 : y (1, b) (y (a, 1) v) = y (a, b) v`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, e2]`.
-/
private theorem commY {A B : Type} [Group A] [Group B] (y : Representation ℂ (A × B) Y) (a : A) (b : B) (v : Y) :
    y (a, 1) (y (1, b) v) = y (1, b) (y (a, 1) v) := by
  have e1 : y (a, 1) (y (1, b) v) = y (a, b) v := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have e2 : y (1, b) (y (a, 1) v) = y (a, b) v := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [e1, e2]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Set `T : Subgroup G` to `{ carrier := {g | ρ g v = v} mul_mem' := by`. Introduce `a b ha hb`. Establish `ha' : ρ a v = v` using `ha`. Establish `hb' : ρ b v = v` using `hb`. Use `show ρ (a * b) v = v`.

Rewrite using `[map_mul, Module.End.mul_apply, hb', ha']`. Use the proof step `one_mem' := by show ρ 1 v = v`. Simplify using the standard rewrite rules. Use the proof step `inv_mem' := by`. Introduce `a ha`.

Establish `ha' : ρ a v = v` using `ha`. Use `show ρ a⁻¹ v = v`. Combine the equalities or inequalities in the displayed calculation. Conclude with `T.isOpen_of_mem_nhds (g := 1) h`.
-/
private theorem smNhds (ρ : Representation ℂ G V) (v : V) (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) :
    v ∈ GlobalTheory.PRep.smoothPart ρ := by
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 v = v
        simp
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul]; simp }
  exact T.isOpen_of_mem_nhds (g := 1) h

/- English proof (translation)
The claim follows from `(Submodule.mem_inf.1 hf).1.2 h g`.
-/
private theorem indLaw {j : H →* G} {y : Representation ℂ H Y} {X : Submodule ℂ Y} {f : G → Y} (hf : f ∈ IndF j y X)
    (h : H) (g : G) : f (j h * g) = y h (f g) := (Submodule.mem_inf.1 hf).1.2 h g

/- English proof (translation)
The claim follows from `IsOpen.mem_nhds (Submodule.mem_inf.1 hf).2 (by simp)`.
-/
private theorem indSm {j : H →* G} {y : Representation ℂ H Y} {X : Submodule ℂ Y} {f : G → Y} (hf : f ∈ IndF j y X) :
    {g : G | rightReg ℂ G Y g f = f} ∈ nhds (1 : G) :=
  IsOpen.mem_nhds (Submodule.mem_inf.1 hf).2 (by simp)

/- English proof (translation)
The claim follows from `Submodule.mem_inf.2 ⟨⟨fun _ => trivial, h1⟩, smNhds _ _ h2⟩`.
-/
private theorem indMk {j : H →* G} {y : Representation ℂ H Y} {f : G → Y} (h1 : ∀ h g, f (j h * g) = y h (f g))
    (h2 : {g : G | rightReg ℂ G Y g f = f} ∈ nhds (1 : G)) : f ∈ IndF j y ⊤ :=
  Submodule.mem_inf.2 ⟨⟨fun _ => trivial, h1⟩, smNhds _ _ h2⟩

end Tools

section Trans

variable {G₁ G₂ H₁ H₂ Γ Y : Type} [Group G₁] [Group G₂] [Group H₁] [Group H₂] [AddCommGroup Y] [Module ℂ Y]
  [TopologicalSpace G₁] [IsTopologicalGroup G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

/- English proof (translation)
Use `indMk (fun h g => ?_) ?_` and prove the remaining obligations. Use `show f (e (j₁ h * g)) = y₁ h (f (e g))`. Rewrite using `[map_mul, hj, indLaw hf, hy]`. Establish `hs : {g : G₂ | rightReg ℂ G₂ Y g f = f} ∈ nhds (e 1)`. Rewrite using `[map_one]`.

Conclude with `indSm hf`. Use `Filter.mem_of_superset (he.continuousAt.preimage_mem_nhds hs) ?_` and prove the remaining obligations. Introduce `g hg`. Use function extensionality and compare the values at `x`. Use `congrFun (show rightReg ℂ G₂ Y (e g) f = f from hg) (e x)` as an intermediate fact.

Use `show f (e (x * g)) = f (e x)`. Rewrite using `[map_mul]`. Conclude with `this`.
-/
private theorem memTrans (e : G₁ ≃* G₂) (he : Continuous e) (j₁ : H₁ →* G₁) (j₂ : H₂ →* G₂) (eh : H₁ ≃* H₂)
    (hj : ∀ h, e (j₁ h) = j₂ (eh h)) (y₁ : Representation ℂ H₁ Y) (y₂ : Representation ℂ H₂ Y)
    (hy : ∀ h, y₁ h = y₂ (eh h)) {f : G₂ → Y} (hf : f ∈ IndF j₂ y₂ ⊤) : (fun x => f (e x)) ∈ IndF j₁ y₁ ⊤ := by
  refine indMk (fun h g => ?_) ?_
  · show f (e (j₁ h * g)) = y₁ h (f (e g))
    rw [map_mul, hj, indLaw hf, hy]
  · have hs : {g : G₂ | rightReg ℂ G₂ Y g f = f} ∈ nhds (e 1) := by
      rw [map_one]; exact indSm hf
    refine Filter.mem_of_superset (he.continuousAt.preimage_mem_nhds hs) ?_
    intro g hg
    funext x
    have := congrFun (show rightReg ℂ G₂ Y (e g) f = f from hg) (e x)
    show f (e (x * g)) = f (e x)
    rw [map_mul]
    exact this

/- English proof (translation)
Establish `hback : ∀ {f : G₁ → Y}, f ∈ IndF j₁ y₁ ⊤ → (fun x => f (e.symm x)) ∈ IndF j₂ y₂ ⊤`. Introduce `f hf`. Use `memTrans e.symm he' j₂ j₁ eh.symm (fun h => ?_) y₂ y₁ (fun h => ?_) hf` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply, hj, MulEquiv.apply_symm_apply]`.

Rewrite using `[hy, MulEquiv.apply_symm_apply]`. Introduce `Q hQ h1 h2`. Set `W : (G₂ → Y) →ₗ[ℂ] (G₁ → Y)` to `LinearMap.funLeft ℂ Y e`. Establish `hWa : ∀ (f : G₂ → Y) x, W f x = f (e x)` using `fun _ _ => rfl`. Establish `hup : ∀ f, W f ∈ Q → f ∈ IndF j₂ y₂ ⊤`.

Introduce `f hf`. Use `hback (hQ hf)` as an intermediate fact. Establish `e' : (fun x => W f (e.symm x)) = f`. Use function extensionality and compare the values at `x`. Simplify using `[hWa]`.

Rewrite `this` using `[e']`. Then use the resulting hypothesis. Establish `hmem : ∀ f, W f ∈ Q → f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤` using `fun f hf => Submodule.mem_inf.2 ⟨hf, hup f hf⟩`. Establish `hsurj : ∀ φ : G₁ → Y, W (fun x => φ (e.symm x)) = φ`. Introduce `φ`. Use function extensionality and compare the values at `x`.

Simplify using `[hWa]`. Establish `st1 : ∀ g, ∀ f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤, rightReg ℂ G₂ Y g f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤`. Introduce `g f hf`. Use `hmem _ ?_` and prove the remaining obligations. Use `h1 (e.symm g) _ (Submodule.mem_inf.1 hf).1` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Use `show f (e x * g) = f (e (x * e.symm g))`. Simplify using the standard rewrite rules. Establish `st2 : ∀ c, ∀ f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤, (fun x => γ c (f x)) ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤`.

Introduce `c f hf`. Conclude with `hmem _ (h2 c _ (Submodule.mem_inf.1 hf).1)`. Break down `hS (Q.comap W ⊓ IndF j₂ y₂ ⊤) inf_le_right st1 st2 with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff _).2 fun φ hφ => ?_` and prove the remaining obligations.

Establish `hm` using `hmem (fun x => φ (e.symm x)) (by rw [hsurj]; exact hφ)`. Rewrite `hm` using `[h]`. Establish `h0` using `(Submodule.mem_bot ℂ).1 hm`. Rewrite using `[← hsurj φ, h0, map_zero]`. Use `right`.

Use `le_antisymm hQ fun φ hφ => ?_` and prove the remaining obligations. Establish `hm` using `hback hφ`. Rewrite `hm` using `[← h]`. Use `(Submodule.mem_inf.1 hm).1` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, hsurj]`.

Conclude with `this`.
-/
private theorem simpleTrans (e : G₁ ≃* G₂) (he : Continuous e) (he' : Continuous e.symm) (j₁ : H₁ →* G₁) (j₂ : H₂ →* G₂)
    (eh : H₁ ≃* H₂) (hj : ∀ h, e (j₁ h) = j₂ (eh h)) (y₁ : Representation ℂ H₁ Y) (y₂ : Representation ℂ H₂ Y)
    (hy : ∀ h, y₁ h = y₂ (eh h)) (γ : Γ → Y →ₗ[ℂ] Y) (hS : SimpleG (IndF j₂ y₂ ⊤) γ) : SimpleG (IndF j₁ y₁ ⊤) γ := by
  have hback : ∀ {f : G₁ → Y}, f ∈ IndF j₁ y₁ ⊤ → (fun x => f (e.symm x)) ∈ IndF j₂ y₂ ⊤ := by
    intro f hf
    refine memTrans e.symm he' j₂ j₁ eh.symm (fun h => ?_) y₂ y₁ (fun h => ?_) hf
    · apply e.injective
      rw [MulEquiv.apply_symm_apply, hj, MulEquiv.apply_symm_apply]
    · rw [hy, MulEquiv.apply_symm_apply]
  intro Q hQ h1 h2
  let W : (G₂ → Y) →ₗ[ℂ] (G₁ → Y) := LinearMap.funLeft ℂ Y e
  have hWa : ∀ (f : G₂ → Y) x, W f x = f (e x) := fun _ _ => rfl
  have hup : ∀ f, W f ∈ Q → f ∈ IndF j₂ y₂ ⊤ := by
    intro f hf
    have := hback (hQ hf)
    have e' : (fun x => W f (e.symm x)) = f := by
      funext x; simp [hWa]
    rwa [e'] at this
  have hmem : ∀ f, W f ∈ Q → f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤ := fun f hf => Submodule.mem_inf.2 ⟨hf, hup f hf⟩
  have hsurj : ∀ φ : G₁ → Y, W (fun x => φ (e.symm x)) = φ := by
    intro φ; funext x; simp [hWa]
  have st1 : ∀ g, ∀ f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤, rightReg ℂ G₂ Y g f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤ := by
    intro g f hf
    refine hmem _ ?_
    have := h1 (e.symm g) _ (Submodule.mem_inf.1 hf).1
    convert this using 1
    funext x
    show f (e x * g) = f (e (x * e.symm g))
    simp
  have st2 : ∀ c, ∀ f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤, (fun x => γ c (f x)) ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤ := by
    intro c f hf
    exact hmem _ (h2 c _ (Submodule.mem_inf.1 hf).1)
  rcases hS (Q.comap W ⊓ IndF j₂ y₂ ⊤) inf_le_right st1 st2 with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    have hm := hmem (fun x => φ (e.symm x)) (by rw [hsurj]; exact hφ)
    rw [h] at hm
    have h0 := (Submodule.mem_bot ℂ).1 hm
    rw [← hsurj φ, h0, map_zero]
  · right
    refine le_antisymm hQ fun φ hφ => ?_
    have hm := hback hφ
    rw [← h] at hm
    have := (Submodule.mem_inf.1 hm).1
    rw [Submodule.mem_comap, hsurj] at this
    exact this

end Trans

section Base

variable {G H Γ Y : Type} [Group G] [Group H] [Group Γ] [AddCommGroup Y] [Module ℂ Y]
  [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Introduce `Q hQ _ h2`. Set `ev : (G → Y) →ₗ[ℂ] Y` to `LinearMap.proj 1`. Establish `hext : ∀ φ ψ : G → Y, φ 1 = ψ 1 → φ = ψ`. Introduce `φ ψ h`. Use function extensionality and compare the values at `x`.

Rewrite using `[Subsingleton.elim x 1]`. Conclude with `h`. Establish `st : ∀ x, ∀ v ∈ Q.map ev, y x v ∈ Q.map ev`. Introduce and unpack `⟨h, c⟩ v ⟨ψ, hψ, rfl⟩`. Rewrite using `[Subsingleton.elim h 1]`.

Conclude with `⟨_, h2 c ψ hψ, rfl⟩`. Break down `irrCases y hy (Q.map ev) st with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff _).2 fun φ hφ => ?_` and prove the remaining obligations. Establish `: φ 1 ∈ Q.map ev` using `⟨φ, hφ, rfl⟩`.

Rewrite `this` using `[h]`. Conclude with `hext _ _ ((Submodule.mem_bot ℂ).1 this)`. Use `right`. Use `le_antisymm hQ fun φ hφ => ?_` and prove the remaining obligations. Establish `: φ 1 ∈ Q.map ev` using `by rw [h]; trivial`.

Take `⟨ψ, hψ, e⟩` from `this`. Rewrite using `[← hext ψ φ e]` and apply the resulting hypothesis.
-/
private theorem simpleBase [Subsingleton G] [Subsingleton H] (j : H →* G) (y : Representation ℂ (H × Γ) Y)
    (hy : y.IsIrreducible) : SimpleG (IndF j (y.comp (MonoidHom.inl H Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro Q hQ _ h2
  let ev : (G → Y) →ₗ[ℂ] Y := LinearMap.proj 1
  have hext : ∀ φ ψ : G → Y, φ 1 = ψ 1 → φ = ψ := by
    intro φ ψ h; funext x; rw [Subsingleton.elim x 1]; exact h
  have st : ∀ x, ∀ v ∈ Q.map ev, y x v ∈ Q.map ev := by
    rintro ⟨h, c⟩ v ⟨ψ, hψ, rfl⟩
    rw [Subsingleton.elim h 1]
    exact ⟨_, h2 c ψ hψ, rfl⟩
  rcases irrCases y hy (Q.map ev) st with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    have : φ 1 ∈ Q.map ev := ⟨φ, hφ, rfl⟩
    rw [h] at this
    exact hext _ _ ((Submodule.mem_bot ℂ).1 this)
  · right
    refine le_antisymm hQ fun φ hφ => ?_
    have : φ 1 ∈ Q.map ev := by rw [h]; trivial
    obtain ⟨ψ, hψ, e⟩ := this
    rwa [← hext ψ φ e]

end Base

section Prod

variable {A B H L Γ Y V : Type} [Group A] [Group B] [Group H] [Group L] [Group Γ] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup V] [Module ℂ V]

private def zAct (y : Representation ℂ (H × L) Y) : Representation ℂ (B × L) (B → Y) where
  toFun x := (rightReg ℂ B Y x.1) ∘ₗ (LinearMap.compLeft (y (1, x.2)) B)
  map_one' := by
    apply LinearMap.ext; intro φ; funext b
    show y (1, 1) (φ (b * 1)) = φ b
    have e : ((1, 1) : H × L) = 1 := rfl
    rw [e, map_one, mul_one]; rfl
  map_mul' a c := by
    apply LinearMap.ext; intro φ; funext b
    show y (1, a.2 * c.2) (φ (b * (a.1 * c.1))) = y (1, a.2) (y (1, c.2) (φ (b * a.1 * c.1)))
    have e : ((1 : H), a.2 * c.2) = (1, a.2) * (1, c.2) := by simp
    rw [e, map_mul, Module.End.mul_apply, mul_assoc]

variable [TopologicalSpace B] [IsTopologicalGroup B]

/- English proof (translation)
Introduce `φ hφ`. Use `indMk (fun h g => ?_) ?_` and prove the remaining obligations. Use `show y (1, x.2) (φ (j h * g * x.1)) = y (h, 1) (y (1, x.2) (φ (g * x.1)))`. Establish `e : φ (j h * (g * x.1)) = y (h, 1) (φ (g * x.1))` using `indLaw hφ h _`. Rewrite using `[mul_assoc, e, commY]`.

Establish `hc : Continuous fun g : B => x.1 * g * x.1⁻¹` using `by fun_prop`. Establish `hs : {g : B | rightReg ℂ B Y g φ = φ} ∈ nhds (x.1⁻¹ * 1 * x.1)`. Establish `e : x.1⁻¹ * 1 * x.1 = 1` using `by group`. Rewrite using `[e]`. Conclude with `indSm hφ`.

Establish `hc' : Continuous fun g : B => x.1⁻¹ * g * x.1` using `by fun_prop`. Use `Filter.mem_of_superset (hc'.continuousAt.preimage_mem_nhds hs) ?_` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : ∀ b, φ (b * (x.1⁻¹ * g * x.1)) = φ b` using `fun b => congrFun (show rightReg ℂ B Y (x.1⁻¹ * g * x.1) φ = φ from hg) b`. Use function extensionality and compare the values at `b`.

Use `show y (1, x.2) (φ (b * g * x.1)) = y (1, x.2) (φ (b * x.1))`. Rewrite using `[show b * g * x.1 = (b * x.1) * (x.1⁻¹ * g * x.1) by group, hg']`.
-/
private theorem zStab (j : H →* B) (y : Representation ℂ (H × L) Y) (x : B × L) :
    ∀ φ ∈ IndF j (y.comp (MonoidHom.inl H L)) ⊤, zAct y x φ ∈ IndF j (y.comp (MonoidHom.inl H L)) ⊤ := by
  intro φ hφ
  refine indMk (fun h g => ?_) ?_
  · show y (1, x.2) (φ (j h * g * x.1)) = y (h, 1) (y (1, x.2) (φ (g * x.1)))
    have e : φ (j h * (g * x.1)) = y (h, 1) (φ (g * x.1)) := indLaw hφ h _
    rw [mul_assoc, e, commY]
  · have hc : Continuous fun g : B => x.1 * g * x.1⁻¹ := by fun_prop
    have hs : {g : B | rightReg ℂ B Y g φ = φ} ∈ nhds (x.1⁻¹ * 1 * x.1) := by
      have e : x.1⁻¹ * 1 * x.1 = 1 := by group
      rw [e]; exact indSm hφ
    have hc' : Continuous fun g : B => x.1⁻¹ * g * x.1 := by fun_prop
    refine Filter.mem_of_superset (hc'.continuousAt.preimage_mem_nhds hs) ?_
    intro g hg
    have hg' : ∀ b, φ (b * (x.1⁻¹ * g * x.1)) = φ b := fun b =>
      congrFun (show rightReg ℂ B Y (x.1⁻¹ * g * x.1) φ = φ from hg) b
    funext b
    show y (1, x.2) (φ (b * g * x.1)) = y (1, x.2) (φ (b * x.1))
    rw [show b * g * x.1 = (b * x.1) * (x.1⁻¹ * g * x.1) by group, hg']

private def zRep (j : H →* B) (y : Representation ℂ (H × L) Y) :
    Representation ℂ (B × L) (IndF j (y.comp (MonoidHom.inl H L)) ⊤) where
  toFun x := (zAct y x).restrict (zStab j y x)
  map_one' := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    show zAct y 1 φ.1 = φ.1
    rw [map_one]; rfl
  map_mul' a c := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    show zAct y (a * c) φ.1 = zAct y a (zAct y c φ.1)
    rw [map_mul]; rfl

private def swp (P : Type) [Group P] : P × (B × Γ) →* B × (P × Γ) where
  toFun x := (x.2.1, (x.1, x.2.2))
  map_one' := rfl
  map_mul' _ _ := rfl

private def y3 (P : Type) [Group P] (y : Representation ℂ (H × (P × Γ)) Y) : Representation ℂ (P × H) Y :=
  y.comp
    { toFun := fun x => (x.2, (x.1, 1))
      map_one' := rfl
      map_mul' := fun a b => by simp }

variable [TopologicalSpace A] [IsTopologicalGroup A] [TopologicalSpace H]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by`. Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `hf (LinearMap.ext hh)`. Take `⟨U, F, hU, hF⟩` from `indSeed j y (f v₀) hj hsm (hopen _)`.

Set `Wf : Submodule ℂ V` to `{ carrier := {v | ∀ h, j h ∈ U → y (h, 1) (f v) = f v} add_mem' := by`. Introduce `a b ha hb h hh`. Rewrite using `[map_add, map_add, ha h hh, hb h hh]`. Use the proof step `zero_mem' := by intro h _; simp`. Use the proof step `smul_mem' := by`.

Introduce `c a ha h hh`. Rewrite using `[map_smul, map_smul, ha h hh] }`. Establish `hWst : ∀ p, ∀ v ∈ Wf, ρ p v ∈ Wf`. Introduce `p v hv h hh`. Rewrite using `[hfρ, commY, hv h hh]`.

Establish `hWtop : Wf = ⊤`. Break down `irrCases ρ hL.irr Wf hWst with e | e` into its components or cases. It suffices to derive a contradiction. Establish `: v₀ ∈ Wf` using `fun h hh => hU h hh`. Rewrite `this` using `[e]`.

Conclude with `hv₀ (by rw [(Submodule.mem_bot ℂ).1 this, map_zero])`. Conclude with `e`. Establish `hWv : ∀ v h, j h ∈ U → y (h, 1) (f v) = f v`. Introduce `v`. Establish `: v ∈ Wf` using `by rw [hWtop]; trivial`.

Conclude with `this`. Set `Z` to `IndF j (y.comp (MonoidHom.inl H (P × Γ))) ⊤`. Set `fz : V →ₗ[ℂ] Z` to `LinearMap.codRestrict Z (F ∘ₗ f) fun v => (hF (f v) (hWv v)).1`. Establish `hfza : ∀ v, (fz v : B → Y) = F (f v)` using `fun _ => rfl`. Establish `hfz : fz ≠ 0`.

Introduce `e`. Apply `hv₀` to reduce the goal to its premises. Establish `h1` using `(hF (f v₀) (hWv v₀)).2.1`. Rewrite using `[← h1, ← hfza, e]`. Both sides reduce to the same expression.

Set `y₂ : Representation ℂ (P × (B × Γ)) Z` to `(zRep j y).comp (swp P)`. Establish `hy₂a : ∀ (x : P × (B × Γ)) (ζ : Z) (b : B), (y₂ x ζ : B → Y) b = y (1, (x.1, x.2.2)) ((ζ : B → Y) (b * x.2.1))` using `fun _ _ _ => rfl`. Establish `hZn : Nontrivial Z`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, fz v ≠ 0 := by`. Assume the negation of the conclusion as `hh`.

Use `push_neg at hh`. Conclude with `hfz (LinearMap.ext hh)`. Conclude with `⟨⟨_, _, hv⟩⟩`. Establish `hy₂ : y₂.IsIrreducible`. Use `irrOf y₂ hZn fun W hW => ?_` and prove the remaining obligations.

Establish `hQ : W.map Z.subtype ≤ Z` using `Submodule.map_subtype_le Z W`. Establish `s1 : ∀ g, ∀ φ ∈ W.map Z.subtype, rightReg ℂ B Y g φ ∈ W.map Z.subtype`. Introduce and unpack `g _ ⟨w, hw, rfl⟩`. Use `⟨_, hW (1, (g, 1)) w hw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`.

Use `show y (1, (1, 1)) ((w : B → Y) (b * g)) = (w : B → Y) (b * g)`. Establish `e : ((1, (1, 1)) : H × (P × Γ)) = 1` using `rfl`. Rewrite using `[e, map_one]`. Both sides reduce to the same expression. Establish `s2 : ∀ c : P × Γ, ∀ φ ∈ W.map Z.subtype, (fun x => y (1, c) (φ x)) ∈ W.map Z.subtype`.

Introduce and unpack `c _ ⟨w, hw, rfl⟩`. Use `⟨_, hW (c.1, (1, c.2)) w hw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Use `show y (1, (c.1, c.2)) ((w : B → Y) (b * 1)) = y (1, c) ((w : B → Y) b)`. Rewrite using `[mul_one]`.

Break down `hIH _ hQ s1 s2 with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff _).2 fun w hw => ?_` and prove the remaining obligations. Establish `: (w : B → Y) ∈ W.map Z.subtype` using `⟨w, hw, rfl⟩`. Rewrite `this` using `[h]`.

Conclude with `Subtype.ext ((Submodule.mem_bot ℂ).1 this)`. Use `right`. Use `(Submodule.eq_top_iff').2 fun w => ?_` and prove the remaining obligations. Establish `: (w : B → Y) ∈ W.map Z.subtype` using `by rw [h]; exact w.2`. Take `⟨w', hw', e⟩` from `this`.

Rewrite using `[← Subtype.ext (a1 := w') (a2 := w) e]` and apply the resulting hypothesis. Establish `hint : ∀ p v, fz (ρ p v) = y₂ (p, 1) (fz v)`. Introduce `p v`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `b`.

Rewrite using `[hy₂a, hfza, hfza, hfρ]`. Establish `e` using `(hF (f v) (hWv v)).2.2 (p, 1) b`. Rewrite using `[e, show ((p, 1) : P × (B × Γ)).2.1 = (1 : B) from rfl, mul_one]`. Both sides reduce to the same expression. Establish `hS` using `UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indStep P ρ y₂ fz hL hy₂ hfz hint`.

Set `Sp` to `IndF P.subtype (y₂.comp (MonoidHom.inl P (B × Γ))) ⊤`. Set `W' : (A → Z) →ₗ[ℂ] (A × B → Y)` to `{ toFun := fun Ψ x => (Ψ x.1 : B → Y) x.2 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hinj : ∀ Ψ Ψ', W' Ψ = W' Ψ' → Ψ = Ψ'`. Introduce `Ψ Ψ' e`. Use function extensionality and compare the values at `a`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Conclude with `congrFun e (a, b)`. Establish `hcur : ∀ φ ∈ IndF (MonoidHom.prodMap P.subtype j) (y3 P y) ⊤, ∃ Ψ ∈ Sp, W' Ψ = φ`. Introduce `φ hφ`.

Establish `hs : {g : A × B | rightReg ℂ (A × B) Y g φ = φ} ∈ nhds (((1 : A), (1 : B)) : A × B)` using `indSm hφ`. Establish `hb : ∀ a, (fun b => φ (a, b)) ∈ Z`. Introduce `a`. Use `indMk (fun h g => ?_) ?_` and prove the remaining obligations. Establish `t` using `indLaw hφ ((1 : P), h) (a, g)`.

Establish `e : (MonoidHom.prodMap P.subtype j) ((1 : P), h) * (a, g) = (a, j h * g)` using `by simp`. Rewrite `t` using `[e]`. Conclude with `t`. Establish `hc : Continuous fun b : B => ((1 : A), b)` using `by fun_prop`. Use `Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hs) ?_` and prove the remaining obligations.

Introduce `b hb`. Use function extensionality and compare the values at `x`. Establish `t` using `congrFun (show rightReg ℂ (A × B) Y ((1 : A), b) φ = φ from hb) (a, x)`. Establish `t' : φ ((a, x) * ((1 : A), b)) = φ (a, x)` using `t`. Use `show φ (a, x * b) = φ (a, x)`.

Simplify using `using t'`. Use `⟨fun a => ⟨fun b => φ (a, b), hb a⟩, indMk (fun p a => ?_) ?_, rfl⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Establish `t` using `indLaw hφ (p, (1 : H)) (a, b)`.

Establish `e : (MonoidHom.prodMap P.subtype j) (p, (1 : H)) * (a, b) = ((p : A) * a, b)` using `by simp`. Rewrite `t` using `[e]`. Use `show φ ((p : A) * a, b) = y (1, (p, 1)) (φ (a, b * 1))`. Rewrite using `[mul_one]`. Conclude with `t`.

Establish `hc : Continuous fun a : A => (a, (1 : B))` using `by fun_prop`. Use `Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hs) ?_` and prove the remaining obligations. Introduce `a' ha'`. Use function extensionality and compare the values at `a`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `b`. Establish `t` using `congrFun (show rightReg ℂ (A × B) Y (a', (1 : B)) φ = φ from ha') (a, b)`. Establish `t' : φ ((a, b) * (a', (1 : B))) = φ (a, b)` using `t`. Use `show φ (a * a', b) = φ (a, b)`. Simplify using `using t'`.

Introduce `Q hQ h1 h2`. Establish `hback : ∀ Ψ, W' Ψ ∈ Q → Ψ ∈ Q.comap W' ⊓ Sp`. Introduce `Ψ h`. Take `⟨Ψ', h', e⟩` from `hcur _ (hQ h)`. Rewrite using `[← hinj _ _ e]`.

Conclude with `Submodule.mem_inf.2 ⟨by rw [Submodule.mem_comap, e]; exact h, h'⟩`. Establish `st1 : ∀ g, ∀ Ψ ∈ Q.comap W' ⊓ Sp, rightReg ℂ A Z g Ψ ∈ Q.comap W' ⊓ Sp`. Introduce `g Ψ hΨ`. Use `hback _ ?_` and prove the remaining obligations. Establish `t` using `h1 (g, 1) _ (Submodule.mem_inf.1 hΨ).1`.

Establish `e : W' (rightReg ℂ A Z g Ψ) = rightReg ℂ (A × B) Y (g, 1) (W' Ψ)`. Use function extensionality and compare the values at `x`. Use `show ((Ψ (x.1 * g) : Z) : B → Y) x.2 = ((Ψ (x * (g, 1)).1 : Z) : B → Y) (x * (g, 1)).2`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `t`. Establish `st2 : ∀ c : B × Γ, ∀ Ψ ∈ Q.comap W' ⊓ Sp, (fun x => y₂ (1, c) (Ψ x)) ∈ Q.comap W' ⊓ Sp`. Introduce `c Ψ hΨ`. Use `hback _ ?_` and prove the remaining obligations. Establish `t1` using `h1 ((1 : A), c.1) _ (Submodule.mem_inf.1 hΨ).1`.

Establish `t2` using `h2 c.2 _ t1`. Establish `e : W' (fun x => y₂ (1, c) (Ψ x)) = fun x => y (1, (1, c.2)) (rightReg ℂ (A × B) Y ((1 : A), c.1) (W' Ψ) x)`. Use function extensionality and compare the values at `x`. Use `show y (1, (1, c.2)) ((Ψ x.1 : B → Y) (x.2 * c.1)) = y (1, (1, c.2)) ((Ψ (x * ((1 : A), c.1)).1 : B → Y) (x * ((1 : A), c.1)).2)`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `t2`. Break down `hS (Q.comap W' ⊓ Sp) inf_le_right st1 st2 with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff _).2 fun φ hφ => ?_` and prove the remaining obligations.

Take `⟨Ψ, hΨ, e⟩` from `hcur φ (hQ hφ)`. Establish `hm : Ψ ∈ Q.comap W' ⊓ Sp` using `hback Ψ (by rw [e]; exact hφ)`. Rewrite `hm` using `[h]`. Rewrite using `[← e, (Submodule.mem_bot ℂ).1 hm, map_zero]`. Use `right`.

Use `le_antisymm hQ fun φ hφ => ?_` and prove the remaining obligations. Take `⟨Ψ, hΨ, e⟩` from `hcur φ hφ`. Establish `hm : Ψ ∈ Q.comap W' ⊓ Sp` using `by rw [h]; exact hΨ`. Use `(Submodule.mem_inf.1 hm).1` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, e]`.

Conclude with `this`.
-/
private theorem prodStep (P : Subgroup A) (j : H →* B) (hj : Topology.IsEmbedding j)
    (hsm : ∀ N ∈ nhds (1 : B), ∃ U : Subgroup B, IsOpen (U : Set B) ∧ (U : Set B) ⊆ N)
    (y : Representation ℂ (H × (P × Γ)) Y) (ρ : Representation ℂ P V) (f : V →ₗ[ℂ] Y) (hL : LocOk P ρ) (hf : f ≠ 0)
    (hfρ : ∀ p v, f (ρ p v) = y (1, (p, 1)) (f v)) (hopen : ∀ v, IsOpen {h : H | y (h, 1) v = v})
    (hIH : SimpleG (IndF j (y.comp (MonoidHom.inl H (P × Γ))) ⊤) fun c : P × Γ => y (1, c)) :
    SimpleG (IndF (MonoidHom.prodMap P.subtype j) (y3 P y) ⊤) fun c : Γ => y (1, (1, c)) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (LinearMap.ext hh)
  obtain ⟨U, F, hU, hF⟩ := indSeed j y (f v₀) hj hsm (hopen _)
  let Wf : Submodule ℂ V :=
    { carrier := {v | ∀ h, j h ∈ U → y (h, 1) (f v) = f v}
      add_mem' := by
        intro a b ha hb h hh
        rw [map_add, map_add, ha h hh, hb h hh]
      zero_mem' := by intro h _; simp
      smul_mem' := by
        intro c a ha h hh
        rw [map_smul, map_smul, ha h hh] }
  have hWst : ∀ p, ∀ v ∈ Wf, ρ p v ∈ Wf := by
    intro p v hv h hh
    rw [hfρ, commY, hv h hh]
  have hWtop : Wf = ⊤ := by
    rcases irrCases ρ hL.irr Wf hWst with e | e
    · exfalso
      have : v₀ ∈ Wf := fun h hh => hU h hh
      rw [e] at this
      exact hv₀ (by rw [(Submodule.mem_bot ℂ).1 this, map_zero])
    · exact e
  have hWv : ∀ v h, j h ∈ U → y (h, 1) (f v) = f v := by
    intro v
    have : v ∈ Wf := by rw [hWtop]; trivial
    exact this
  let Z := IndF j (y.comp (MonoidHom.inl H (P × Γ))) ⊤
  let fz : V →ₗ[ℂ] Z := LinearMap.codRestrict Z (F ∘ₗ f) fun v => (hF (f v) (hWv v)).1
  have hfza : ∀ v, (fz v : B → Y) = F (f v) := fun _ => rfl
  have hfz : fz ≠ 0 := by
    intro e
    apply hv₀
    have h1 := (hF (f v₀) (hWv v₀)).2.1
    rw [← h1, ← hfza, e]
    rfl
  let y₂ : Representation ℂ (P × (B × Γ)) Z := (zRep j y).comp (swp P)
  have hy₂a : ∀ (x : P × (B × Γ)) (ζ : Z) (b : B), (y₂ x ζ : B → Y) b = y (1, (x.1, x.2.2)) ((ζ : B → Y) (b * x.2.1)) :=
    fun _ _ _ => rfl
  have hZn : Nontrivial Z := by
    obtain ⟨v, hv⟩ : ∃ v, fz v ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hfz (LinearMap.ext hh)
    exact ⟨⟨_, _, hv⟩⟩
  have hy₂ : y₂.IsIrreducible := by
    refine irrOf y₂ hZn fun W hW => ?_
    have hQ : W.map Z.subtype ≤ Z := Submodule.map_subtype_le Z W
    have s1 : ∀ g, ∀ φ ∈ W.map Z.subtype, rightReg ℂ B Y g φ ∈ W.map Z.subtype := by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨_, hW (1, (g, 1)) w hw, ?_⟩
      funext b
      show y (1, (1, 1)) ((w : B → Y) (b * g)) = (w : B → Y) (b * g)
      have e : ((1, (1, 1)) : H × (P × Γ)) = 1 := rfl
      rw [e, map_one]; rfl
    have s2 : ∀ c : P × Γ, ∀ φ ∈ W.map Z.subtype, (fun x => y (1, c) (φ x)) ∈ W.map Z.subtype := by
      rintro c _ ⟨w, hw, rfl⟩
      refine ⟨_, hW (c.1, (1, c.2)) w hw, ?_⟩
      funext b
      show y (1, (c.1, c.2)) ((w : B → Y) (b * 1)) = y (1, c) ((w : B → Y) b)
      rw [mul_one]
    rcases hIH _ hQ s1 s2 with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
      have : (w : B → Y) ∈ W.map Z.subtype := ⟨w, hw, rfl⟩
      rw [h] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · right
      refine (Submodule.eq_top_iff').2 fun w => ?_
      have : (w : B → Y) ∈ W.map Z.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', e⟩ := this
      rwa [← Subtype.ext (a1 := w') (a2 := w) e]
  have hint : ∀ p v, fz (ρ p v) = y₂ (p, 1) (fz v) := by
    intro p v
    apply Subtype.ext
    funext b
    rw [hy₂a, hfza, hfza, hfρ]
    have e := (hF (f v) (hWv v)).2.2 (p, 1) b
    rw [e, show ((p, 1) : P × (B × Γ)).2.1 = (1 : B) from rfl, mul_one]
    rfl
  have hS := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indStep P ρ y₂ fz hL hy₂ hfz hint
  let Sp := IndF P.subtype (y₂.comp (MonoidHom.inl P (B × Γ))) ⊤
  let W' : (A → Z) →ₗ[ℂ] (A × B → Y) :=
    { toFun := fun Ψ x => (Ψ x.1 : B → Y) x.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : ∀ Ψ Ψ', W' Ψ = W' Ψ' → Ψ = Ψ' := by
    intro Ψ Ψ' e
    funext a
    apply Subtype.ext
    funext b
    exact congrFun e (a, b)
  have hcur : ∀ φ ∈ IndF (MonoidHom.prodMap P.subtype j) (y3 P y) ⊤, ∃ Ψ ∈ Sp, W' Ψ = φ := by
    intro φ hφ
    have hs : {g : A × B | rightReg ℂ (A × B) Y g φ = φ} ∈ nhds (((1 : A), (1 : B)) : A × B) := indSm hφ
    have hb : ∀ a, (fun b => φ (a, b)) ∈ Z := by
      intro a
      refine indMk (fun h g => ?_) ?_
      · have t := indLaw hφ ((1 : P), h) (a, g)
        have e : (MonoidHom.prodMap P.subtype j) ((1 : P), h) * (a, g) = (a, j h * g) := by simp
        rw [e] at t
        exact t
      · have hc : Continuous fun b : B => ((1 : A), b) := by fun_prop
        refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hs) ?_
        intro b hb
        funext x
        have t := congrFun (show rightReg ℂ (A × B) Y ((1 : A), b) φ = φ from hb) (a, x)
        have t' : φ ((a, x) * ((1 : A), b)) = φ (a, x) := t
        show φ (a, x * b) = φ (a, x)
        simpa using t'
    refine ⟨fun a => ⟨fun b => φ (a, b), hb a⟩, indMk (fun p a => ?_) ?_, rfl⟩
    · apply Subtype.ext
      funext b
      have t := indLaw hφ (p, (1 : H)) (a, b)
      have e : (MonoidHom.prodMap P.subtype j) (p, (1 : H)) * (a, b) = ((p : A) * a, b) := by simp
      rw [e] at t
      show φ ((p : A) * a, b) = y (1, (p, 1)) (φ (a, b * 1))
      rw [mul_one]
      exact t
    · have hc : Continuous fun a : A => (a, (1 : B)) := by fun_prop
      refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hs) ?_
      intro a' ha'
      funext a
      apply Subtype.ext
      funext b
      have t := congrFun (show rightReg ℂ (A × B) Y (a', (1 : B)) φ = φ from ha') (a, b)
      have t' : φ ((a, b) * (a', (1 : B))) = φ (a, b) := t
      show φ (a * a', b) = φ (a, b)
      simpa using t'
  intro Q hQ h1 h2
  have hback : ∀ Ψ, W' Ψ ∈ Q → Ψ ∈ Q.comap W' ⊓ Sp := by
    intro Ψ h
    obtain ⟨Ψ', h', e⟩ := hcur _ (hQ h)
    rw [← hinj _ _ e]
    exact Submodule.mem_inf.2 ⟨by rw [Submodule.mem_comap, e]; exact h, h'⟩
  have st1 : ∀ g, ∀ Ψ ∈ Q.comap W' ⊓ Sp, rightReg ℂ A Z g Ψ ∈ Q.comap W' ⊓ Sp := by
    intro g Ψ hΨ
    refine hback _ ?_
    have t := h1 (g, 1) _ (Submodule.mem_inf.1 hΨ).1
    have e : W' (rightReg ℂ A Z g Ψ) = rightReg ℂ (A × B) Y (g, 1) (W' Ψ) := by
      funext x
      show ((Ψ (x.1 * g) : Z) : B → Y) x.2 = ((Ψ (x * (g, 1)).1 : Z) : B → Y) (x * (g, 1)).2
      simp
    rw [e]
    exact t
  have st2 : ∀ c : B × Γ, ∀ Ψ ∈ Q.comap W' ⊓ Sp, (fun x => y₂ (1, c) (Ψ x)) ∈ Q.comap W' ⊓ Sp := by
    intro c Ψ hΨ
    refine hback _ ?_
    have t1 := h1 ((1 : A), c.1) _ (Submodule.mem_inf.1 hΨ).1
    have t2 := h2 c.2 _ t1
    have e : W' (fun x => y₂ (1, c) (Ψ x)) =
        fun x => y (1, (1, c.2)) (rightReg ℂ (A × B) Y ((1 : A), c.1) (W' Ψ) x) := by
      funext x
      show y (1, (1, c.2)) ((Ψ x.1 : B → Y) (x.2 * c.1)) =
        y (1, (1, c.2)) ((Ψ (x * ((1 : A), c.1)).1 : B → Y) (x * ((1 : A), c.1)).2)
      simp
    rw [e]
    exact t2
  rcases hS (Q.comap W' ⊓ Sp) inf_le_right st1 st2 with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    obtain ⟨Ψ, hΨ, e⟩ := hcur φ (hQ hφ)
    have hm : Ψ ∈ Q.comap W' ⊓ Sp := hback Ψ (by rw [e]; exact hφ)
    rw [h] at hm
    rw [← e, (Submodule.mem_bot ℂ).1 hm, map_zero]
  · right
    refine le_antisymm hQ fun φ hφ => ?_
    obtain ⟨Ψ, hΨ, e⟩ := hcur φ hφ
    have hm : Ψ ∈ Q.comap W' ⊓ Sp := by rw [h]; exact hΨ
    have := (Submodule.mem_inf.1 hm).1
    rw [Submodule.mem_comap, e] at this
    exact this

end Prod

section Fin

private def consG {r : ℕ} (G : Fin (r + 1) → Type) [∀ i, Group (G i)] : (∀ i, G i) ≃* G 0 × ∀ i : Fin r, G i.succ where
  toFun g := (g 0, fun i => g i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv g := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  right_inv x := by simp
  map_mul' _ _ := rfl

/- English proof (translation)
Apply `Prod.ext` to reduce the goal to its premises. Conclude with `Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i).symm p`. Use function extensionality and compare the values at `k show Pi.mulSingle i.succ p k.succ = (Pi.mulSingle i p : ∀ j : Fin r, G j.succ) k`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]`. Rewrite using `[Pi.mulSingle_eq_of_ne (fun e => h (Fin.succ_injective _ e)), Pi.mulSingle_eq_of_ne h]`.
-/
private theorem consSucc {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] (i : Fin r) (p : G i.succ) :
    consG G (Pi.mulSingle i.succ p) = (1, Pi.mulSingle i p) := by
  apply Prod.ext
  · exact Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i).symm p
  · funext k
    show Pi.mulSingle i.succ p k.succ = (Pi.mulSingle i p : ∀ j : Fin r, G j.succ) k
    by_cases h : k = i
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (fun e => h (Fin.succ_injective _ e)), Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
The claim follows from `Prod.ext (Pi.mulSingle_eq_same 0 p) (funext fun k => Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero k) p)`.
-/
private theorem consZero {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] (p : G 0) :
    consG G (Pi.mulSingle 0 p) = (p, 1) :=
  Prod.ext (Pi.mulSingle_eq_same 0 p) (funext fun k => Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero k) p)

/- English proof (translation)
The claim follows from `(continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)`.
-/
private theorem consCont {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] :
    Continuous (consG G) :=
  (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations. Conclude with `continuous_fst`. Conclude with `(continuous_apply k).comp continuous_snd`.
-/
private theorem consCont' {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] :
    Continuous (consG G).symm := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · exact continuous_fst
  · exact (continuous_apply k).comp continuous_snd

/- English proof (translation)
Introduce `N hN`. Rewrite `hN` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hsub⟩` from `hN`. Use `choose U hUo hUt using fun i => h i (t i) (ht i)`. Use `⟨Subgroup.pi Set.univ U, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : ((Subgroup.pi Set.univ U : Subgroup (∀ i, G i)) : Set (∀ i, G i)) = Set.univ.pi fun i => (U i : Set (G i))` using `rfl`. Rewrite using `[e]`. Conclude with `isOpen_set_pi Set.finite_univ fun i _ => hUo i`. Introduce `x hx`. Apply `hsub` to reduce the goal to its premises.

Introduce `i _`. Conclude with `hUt i (hx i (Set.mem_univ i))`.
-/
private theorem smallPi {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (h : ∀ i, ∀ N ∈ nhds (1 : G i), ∃ U : Subgroup (G i), IsOpen (U : Set (G i)) ∧ (U : Set (G i)) ⊆ N) :
    ∀ N ∈ nhds (1 : ∀ i, G i), ∃ U : Subgroup (∀ i, G i), IsOpen (U : Set (∀ i, G i)) ∧ (U : Set (∀ i, G i)) ⊆ N := by
  intro N hN
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  choose U hUo hUt using fun i => h i (t i) (ht i)
  refine ⟨Subgroup.pi Set.univ U, ?_, ?_⟩
  · have e : ((Subgroup.pi Set.univ U : Subgroup (∀ i, G i)) : Set (∀ i, G i)) = Set.univ.pi fun i => (U i : Set (G i)) := rfl
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun i _ => hUo i
  · intro x hx
    apply hsub
    intro i _
    exact hUt i (hx i (Set.mem_univ i))

end Fin

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `G _ _ _ P Γ _ Y _ _ y hy _ _`. Conclude with `simpleBase (piIncl P) y hy`.

Consider the case `succ r ih`. Introduce `G _ _ _ P Γ _ Y _ _ y hy hsm hloc`. Set `eP` to `consG (fun i => P i)`. Set `θ : (∀ i : Fin r, P i.succ) × (P 0 × Γ) →* (∀ i, P i) × Γ` to `{ toFun := fun x => (eP.symm (x.2.1, x.1), x.2.2) map_one' := Prod.ext (map_one eP.symm) rfl map_mul' := fun a b => Prod.ext (map_mul eP.symm (a.2.1, a.1) (b.2.1, b.1)) rfl }`. Set `y' : Representation ℂ ((∀ i : Fin r, P i.succ) × (P 0 × Γ)) Y` to `y.comp θ`.

Establish `hsurj : ∀ x, ∃ z, θ z = x`. Introduce and unpack `⟨p, c⟩`. Use `⟨((eP p).2, ((eP p).1, c)), Prod.ext ?_ rfl⟩` and prove the remaining obligations. Conclude with `eP.symm_apply_apply p`. Take `⟨V, a1, a2, ρ, f, hL, hf, hfr⟩` from `hloc 0`.

Establish `hYn : Nontrivial Y`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, f v ≠ 0 := by`. Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `hf (LinearMap.ext hh)`.

Conclude with `⟨⟨_, _, hv⟩⟩`. Establish `hy' : y'.IsIrreducible`. Use `irrOf y' hYn fun W hW => irrCases y hy W fun x v hv => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hsurj x`. Conclude with `hW z v hv`.

Establish `hsm' : ∀ v, IsOpen {p : ∀ i : Fin r, P i.succ | y' (p, 1) v = v}`. Introduce `v`. Establish `hc : Continuous fun p : (∀ i : Fin r, P i.succ) => eP.symm ((1 : P 0), p)` using `consCont'.comp (by fun_prop)`. Conclude with `(hsm v).preimage hc`. Establish `hloc' : ∀ i : Fin r, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i.succ) V) (f : V →ₗ[ℂ] Y), LocOk (P i.succ) ρ ∧ f ≠ 0 ∧ ∀ p v, f (ρ p v) = y' (Pi.mulSingle i p, 1) (f v)`.

Introduce `i`. Take `⟨V, b1, b2, ρ, f, hL, hf, hfr⟩` from `hloc i.succ`. Use `⟨V, b1, b2, ρ, f, hL, hf, fun p v => ?_⟩` and prove the remaining obligations. Establish `e : eP.symm (1, Pi.mulSingle i p) = Pi.mulSingle i.succ p`. Rewrite using `[MulEquiv.symm_apply_eq]`.

Conclude with `(consSucc (G := fun i => P i) i p).symm`. Rewrite using `[hfr]`. Use `show y (Pi.mulSingle i.succ p, 1) (f v) = y (eP.symm (1, Pi.mulSingle i p), 1) (f v)`. Rewrite using `[e]`. Establish `hIH` using `ih (G := fun i : Fin r => G i.succ) (fun i => P i.succ) y' hy' hsm' hloc'`.

Establish `hB : ∀ N ∈ nhds (1 : ∀ i : Fin r, G i.succ), ∃ U : Subgroup (∀ i : Fin r, G i.succ), IsOpen (U : Set (∀ i : Fin r, G i.succ)) ∧ (U : Set (∀ i : Fin r, G i.succ)) ⊆ N`. Use `smallPi fun i => ?_` and prove the remaining obligations. Take `⟨V, b1, b2, ρ, f, hL, _, _⟩` from `hloc i.succ`. Conclude with `hL.small`. Establish `hemb : Topology.IsEmbedding (piIncl fun i : Fin r => P i.succ)` using `Topology.IsEmbedding.piMap fun _ => Topology.IsEmbedding.subtypeVal`.

Establish `hfρ : ∀ p v, f (ρ p v) = y' (1, (p, 1)) (f v)`. Introduce `p v`. Establish `e : eP.symm (p, 1) = Pi.mulSingle 0 p`. Rewrite using `[MulEquiv.symm_apply_eq]`. Conclude with `(consZero (G := fun i => P i) p).symm`.

Rewrite using `[hfr]`. Use `show y (Pi.mulSingle 0 p, 1) (f v) = y (eP.symm (p, 1), 1) (f v)`. Rewrite using `[e]`. Establish `hfin` using `prodStep (P 0) (piIncl fun i : Fin r => P i.succ) hemb hB y' ρ f hL hf hfρ hsm' hIH`. Establish `hγ : (fun c : Γ => y' (1, (1, c))) = fun c => y (1, c)`.

Use function extensionality and compare the values at `c`. Use `show y (eP.symm (1, 1), c) = y (1, c)`. Rewrite using `[show eP.symm ((1 : P 0), (1 : ∀ i : Fin r, P i.succ)) = 1 from map_one eP.symm]`. Rewrite `hfin` using `[hγ]`. Use `simpleTrans (consG G) consCont consCont' (piIncl P) _ eP (fun h => rfl) _ (y3 (P 0) y') (fun h => ?_) _ hfin` and prove the remaining obligations.

Use `show y (h, 1) = y (eP.symm (eP h), 1)`. Rewrite using `[MulEquiv.symm_apply_apply]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indProdG :
    ∀ (r : ℕ) {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] (P : ∀ i, Subgroup (G i)) {Γ : Type} [Group Γ] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
      (y : Representation ℂ ((∀ i, P i) × Γ) Y), y.IsIrreducible → (∀ v, IsOpen {p : ∀ i, P i | y (p, 1) v = v}) →
      (∀ i, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i) V) (f : V →ₗ[ℂ] Y), LocOk (P i) ρ ∧ f ≠ 0 ∧
        ∀ p v, f (ρ p v) = y (Pi.mulSingle i p, 1) (f v)) →
      SimpleG (IndF (piIncl P) (y.comp (MonoidHom.inl _ Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro r
  induction r with
  | zero =>
    intro G _ _ _ P Γ _ Y _ _ y hy _ _
    exact simpleBase (piIncl P) y hy
  | succ r ih =>
    intro G _ _ _ P Γ _ Y _ _ y hy hsm hloc
    let eP := consG (fun i => P i)
    let θ : (∀ i : Fin r, P i.succ) × (P 0 × Γ) →* (∀ i, P i) × Γ :=
      { toFun := fun x => (eP.symm (x.2.1, x.1), x.2.2)
        map_one' := Prod.ext (map_one eP.symm) rfl
        map_mul' := fun a b => Prod.ext (map_mul eP.symm (a.2.1, a.1) (b.2.1, b.1)) rfl }
    let y' : Representation ℂ ((∀ i : Fin r, P i.succ) × (P 0 × Γ)) Y := y.comp θ
    have hsurj : ∀ x, ∃ z, θ z = x := by
      rintro ⟨p, c⟩
      refine ⟨((eP p).2, ((eP p).1, c)), Prod.ext ?_ rfl⟩
      exact eP.symm_apply_apply p
    obtain ⟨V, a1, a2, ρ, f, hL, hf, hfr⟩ := hloc 0
    have hYn : Nontrivial Y := by
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra hh
        push_neg at hh
        exact hf (LinearMap.ext hh)
      exact ⟨⟨_, _, hv⟩⟩
    have hy' : y'.IsIrreducible := by
      refine irrOf y' hYn fun W hW => irrCases y hy W fun x v hv => ?_
      obtain ⟨z, rfl⟩ := hsurj x
      exact hW z v hv
    have hsm' : ∀ v, IsOpen {p : ∀ i : Fin r, P i.succ | y' (p, 1) v = v} := by
      intro v
      have hc : Continuous fun p : (∀ i : Fin r, P i.succ) => eP.symm ((1 : P 0), p) :=
        consCont'.comp (by fun_prop)
      exact (hsm v).preimage hc
    have hloc' : ∀ i : Fin r, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i.succ) V) (f : V →ₗ[ℂ] Y),
        LocOk (P i.succ) ρ ∧ f ≠ 0 ∧ ∀ p v, f (ρ p v) = y' (Pi.mulSingle i p, 1) (f v) := by
      intro i
      obtain ⟨V, b1, b2, ρ, f, hL, hf, hfr⟩ := hloc i.succ
      refine ⟨V, b1, b2, ρ, f, hL, hf, fun p v => ?_⟩
      have e : eP.symm (1, Pi.mulSingle i p) = Pi.mulSingle i.succ p := by
        rw [MulEquiv.symm_apply_eq]
        exact (consSucc (G := fun i => P i) i p).symm
      rw [hfr]
      show y (Pi.mulSingle i.succ p, 1) (f v) = y (eP.symm (1, Pi.mulSingle i p), 1) (f v)
      rw [e]
    have hIH := ih (G := fun i : Fin r => G i.succ) (fun i => P i.succ) y' hy' hsm' hloc'
    have hB : ∀ N ∈ nhds (1 : ∀ i : Fin r, G i.succ), ∃ U : Subgroup (∀ i : Fin r, G i.succ),
        IsOpen (U : Set (∀ i : Fin r, G i.succ)) ∧ (U : Set (∀ i : Fin r, G i.succ)) ⊆ N := by
      refine smallPi fun i => ?_
      obtain ⟨V, b1, b2, ρ, f, hL, _, _⟩ := hloc i.succ
      exact hL.small
    have hemb : Topology.IsEmbedding (piIncl fun i : Fin r => P i.succ) :=
      Topology.IsEmbedding.piMap fun _ => Topology.IsEmbedding.subtypeVal
    have hfρ : ∀ p v, f (ρ p v) = y' (1, (p, 1)) (f v) := by
      intro p v
      have e : eP.symm (p, 1) = Pi.mulSingle 0 p := by
        rw [MulEquiv.symm_apply_eq]
        exact (consZero (G := fun i => P i) p).symm
      rw [hfr]
      show y (Pi.mulSingle 0 p, 1) (f v) = y (eP.symm (p, 1), 1) (f v)
      rw [e]
    have hfin := prodStep (P 0) (piIncl fun i : Fin r => P i.succ) hemb hB y' ρ f hL hf hfρ hsm' hIH
    have hγ : (fun c : Γ => y' (1, (1, c))) = fun c => y (1, c) := by
      funext c
      show y (eP.symm (1, 1), c) = y (1, c)
      rw [show eP.symm ((1 : P 0), (1 : ∀ i : Fin r, P i.succ)) = 1 from map_one eP.symm]
    rw [hγ] at hfin
    refine simpleTrans (consG G) consCont consCont' (piIncl P) _ eP (fun h => rfl) _ (y3 (P 0) y') (fun h => ?_) _ hfin
    show y (h, 1) = y (eP.symm (eP h), 1)
    rw [MulEquiv.symm_apply_apply]
