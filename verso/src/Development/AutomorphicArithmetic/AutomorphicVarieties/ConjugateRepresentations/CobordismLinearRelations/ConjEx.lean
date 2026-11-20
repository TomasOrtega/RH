import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private def Cv (_ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance (σ : ℂ ≃+* ℂ) (V : Type) [i : AddCommGroup V] : AddCommGroup (Cv σ V) := i

private noncomputable instance (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Cv σ V) :=
  Module.compHom V σ.symm.toRingHom

private def toCv (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Cv σ V := AddEquiv.refl V

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem smul_toCv (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    c • toCv σ V v = toCv σ V (σ.symm c • v) := rfl

/- English proof (translation)
Rewrite using `[smul_toCv, RingEquiv.symm_apply_apply]`.
-/
private theorem toCv_smul (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    toCv σ V (c • v) = σ c • toCv σ V v := by
  rw [smul_toCv, RingEquiv.symm_apply_apply]

private noncomputable def cvRep (σ : ℂ ≃+* ℂ) {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ G (Cv σ V) where
  toFun g :=
    { toFun := fun v => toCv σ V (ρ g ((toCv σ V).symm v))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => congrArg (toCv σ V) (map_smul (ρ g) (σ.symm c) ((toCv σ V).symm x)) }
  map_one' := LinearMap.ext fun v => by simp
  map_mul' x y := LinearMap.ext fun v => by
    simp only [map_mul]
    rfl

/- English proof (translation)
Take `⟨h0, h1⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff ρ).1 h`. Use `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => ?_⟩` and prove the remaining obligations. Set `W' : Submodule ℂ V` to `{ carrier := {v | toCv σ V v ∈ W} add_mem' := fun {x y} hx hy => W.add_mem hx hy zero_mem' := W.zero_mem smul_mem' := fun c x hx => by`. Express the relevant statement in the definitionally equal form `toCv σ V (c • x) ∈ W`. Rewrite using `[toCv_smul]`.

Conclude with `W.smul_mem _ hx }`. Break down `h1 W' (fun g v hv => hW g _ hv) with e | e` into its components or cases. Conclude with `Or.inl ((Submodule.eq_bot_iff _).2 fun v hv => (Submodule.eq_bot_iff _).1 e ((toCv σ V).symm v) hv)`. Conclude with `Or.inr (Submodule.eq_top_iff'.2 fun v => Submodule.eq_top_iff'.1 e ((toCv σ V).symm v))`.
-/
private theorem cvRep_irr (σ : ℂ ≃+* ℂ) {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : (cvRep σ ρ).IsIrreducible := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => ?_⟩
  let W' : Submodule ℂ V :=
    { carrier := {v | toCv σ V v ∈ W}
      add_mem' := fun {x y} hx hy => W.add_mem hx hy
      zero_mem' := W.zero_mem
      smul_mem' := fun c x hx => by
        change toCv σ V (c • x) ∈ W
        rw [toCv_smul]
        exact W.smul_mem _ hx }
  rcases h1 W' (fun g v hv => hW g _ hv) with e | e
  · exact Or.inl ((Submodule.eq_bot_iff _).2 fun v hv => (Submodule.eq_bot_iff _).1 e ((toCv σ V).symm v) hv)
  · exact Or.inr (Submodule.eq_top_iff'.2 fun v => Submodule.eq_top_iff'.1 e ((toCv σ V).symm v))

/- English proof (translation)
Introduce `E _ _ a σ τ`. Conclude with `⟨SmIrr.mk (Cv σ τ.V) (cvRep σ τ.ρ) τ.5 (cvRep_irr σ τ.ρ τ.irred), toCv σ τ.V, toCv_smul σ, fun _ _ => rfl⟩`.
-/
theorem UpperTheory.V.Cj.conjEx :
    UpperTheory.V.Cj.ConjEx := by
  intro E _ _ a σ τ
  exact ⟨SmIrr.mk (Cv σ τ.V) (cvRep σ τ.ρ) τ.5 (cvRep_irr σ τ.ρ τ.irred), toCv σ τ.V, toCv_smul σ, fun _ _ => rfl⟩
