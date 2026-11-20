import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSetlift
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGlift
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGco
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.BorelProjectionIsTwoCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ValSubOneMap

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ k _ _ F C₀ hF O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h j`. Introduce `C' _ _ _ p σ' hp hker hσ' hpσ`. Take `⟨a⟩` from `pr_setlift hF O C' R p B hp hker hCont`. Take `⟨D, hD⟩` from `ep_glift O h2 C' R p σ' σ hσ' hpσ B π hGr a`. Establish `hco : ∀ u : ↥(formp σ' (RingHom.ker p) j), (∀ x : F.Γ × F.Γ, (D.co u).1 x ∈ adp (ResidueField O) j) ∧ ∀ (v : F.V) (s : F.Gv v), (D.co u).2 v s ∈ adp (ResidueField O) j` using `fun u => ep_gco O C' R p σ' B π D hD j u u.2`.

Establish `hom` using `pr_omk hF O C' R p B D hker`. Set `Ψ : ↥(formp σ' (RingHom.ker p) j) →ₗ[ResidueField O] ((F.Γ × F.Γ → ↥(adp (ResidueField O) j)) × ((v : F.V) → F.Gv v → ↥(adp (ResidueField O) j)))` to `{ toFun := fun u => (fun x => ⟨(D.co u).1 x, (hco u).1 x⟩, fun v s => ⟨(D.co u).2 v s, (hco u).2 v s⟩) map_add' := by`. Introduce `u w`. Apply the tactic sequence `refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>`. Simplify using `[map_add]`.

Use the proof step `map_smul' := by`. Introduce `c u`. Apply the tactic sequence `refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>`. Simplify using `[map_smul] }`. Establish `hmem : ∀ u, Ψ u ∈ continuousCocycles2 F.loc (h.ad j) ((Box.bar O B).bp j)`.

Introduce `u`. Establish `k1 : Subtype.val ∘ (Ψ u).1 = (fun M : Matrix (Fin 3) (Fin 3) C' => M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.om` using `rfl`. Establish `k2 : ∀ v, Subtype.val ∘ (Ψ u).2 v = (fun M : Matrix (Fin 3) (Fin 3) C' => M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.a v` using `fun v => rfl`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective` and prove the remaining obligations.

Rewrite using `[k1]`. Conclude with `hom.2.2.1.comp _`. Introduce `v`. Use `IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective` and prove the remaining obligations. Rewrite using `[k2 v]`.

Conclude with `(hom.2.2.2 v).comp _`. Introduce `s t r`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `borelProjection_isTwoCocycle hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker s t r`. Introduce `v s t`.

Conclude with `pr_cocv hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker v s t`. Use `⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ Ψ hmem), ?_⟩` and prove the remaining obligations. Introduce `u hu C'' _ _ _ q p'' hcomp hq hy`. Use `pr_obs hF O R ρ B hU hOf hCont hGood C' p D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker ?_ C'' q p'' hcomp hq hy` and prove the remaining obligations. Rewrite `hu` using `[LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Take `⟨β, Y, hβ, h1, h3⟩` from `hu`. Use `⟨fun g => (β g : Matrix (Fin 3) (Fin 3) (ResidueField O)), fun v => (Y v : Matrix (Fin 3) (Fin 3) (ResidueField O)), hβ.comp _, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Conclude with `congrArg (fun f => (f x : Matrix (Fin 3) (Fin 3) (ResidueField O))) h1`. Introduce `v s`.

Conclude with `h3 v s`.
-/
theorem UpperTheory.V.Fr.ep_hasobs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → B.Gr σ π → ∀ h : (B.bar O).Ev π, ∀ j, HasObsG O σ j (coneH2 F.loc (h.ad j) ((B.bar O).bp j)) := by
  intro l _ k _ _ F C₀ hF O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h j
  intro C' _ _ _ p σ' hp hker hσ' hpσ
  obtain ⟨a⟩ := pr_setlift hF O C' R p B hp hker hCont
  obtain ⟨D, hD⟩ := ep_glift O h2 C' R p σ' σ hσ' hpσ B π hGr a
  have hco : ∀ u : ↥(formp σ' (RingHom.ker p) j),
      (∀ x : F.Γ × F.Γ, (D.co u).1 x ∈ adp (ResidueField O) j) ∧
        ∀ (v : F.V) (s : F.Gv v), (D.co u).2 v s ∈ adp (ResidueField O) j :=
    fun u => ep_gco O C' R p σ' B π D hD j u u.2
  have hom := pr_omk hF O C' R p B D hker
  let Ψ : ↥(formp σ' (RingHom.ker p) j) →ₗ[ResidueField O]
      ((F.Γ × F.Γ → ↥(adp (ResidueField O) j)) × ((v : F.V) → F.Gv v → ↥(adp (ResidueField O) j))) :=
    { toFun := fun u => (fun x => ⟨(D.co u).1 x, (hco u).1 x⟩, fun v s => ⟨(D.co u).2 v s, (hco u).2 v s⟩)
      map_add' := by
        intro u w
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_add]
      map_smul' := by
        intro c u
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_smul] }
  have hmem : ∀ u, Ψ u ∈ continuousCocycles2 F.loc (h.ad j) ((Box.bar O B).bp j) := by
    intro u
    have k1 : Subtype.val ∘ (Ψ u).1 = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.om := rfl
    have k2 : ∀ v, Subtype.val ∘ (Ψ u).2 v = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.a v := fun v => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k1]
      exact hom.2.2.1.comp _
    · intro v
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k2 v]
      exact (hom.2.2.2 v).comp _
    · intro s t r
      apply Subtype.ext
      exact borelProjection_isTwoCocycle hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker s t r
    · intro v s t
      exact pr_cocv hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker v s t
  refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ Ψ hmem), ?_⟩
  intro u hu C'' _ _ _ q p'' hcomp hq hy
  refine pr_obs hF O R ρ B hU hOf hCont hGood C' p D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker ?_
    C'' q p'' hcomp hq hy
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
  obtain ⟨β, Y, hβ, h1, h3⟩ := hu
  refine ⟨fun g => (β g : Matrix (Fin 3) (Fin 3) (ResidueField O)),
    fun v => (Y v : Matrix (Fin 3) (Fin 3) (ResidueField O)), hβ.comp _, ?_, ?_⟩
  · funext x
    exact congrArg (fun f => (f x : Matrix (Fin 3) (Fin 3) (ResidueField O))) h1
  · intro v s
    exact h3 v s
