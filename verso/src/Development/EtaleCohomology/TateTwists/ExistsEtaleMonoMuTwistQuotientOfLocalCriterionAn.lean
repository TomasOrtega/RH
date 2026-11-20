import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotien

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def muK (q : ℕ) (A : CommRingCat.{0}) : Submodule (ULift.{1} (ZMod q)) ((twF q 1).obj A) :=
  Submodule.span _ {x | ∃ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 ∧
    x = (l.map fun ζ => twGenR A ζ).sum}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) = _`. Rewrite using `[Finsupp.mapDomain_single]`. Both sides reduce to the same expression.
-/
theorem muK_gen_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (ζ.map f.hom) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]
  rfl

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨l, hl, rfl⟩`. Use `Submodule.subset_span ⟨l.map (Prim.map f.hom), ?_, ?_⟩` and prove the remaining obligations. Establish `: ((l.map fun ζ => ζ.1).map f.hom).prod = f.hom 1` using `by rw [← map_list_prod, hl]`. Rewrite `this` using `[map_one]`.

Rewrite using `[← this, List.map_map, List.map_map]`. Both sides reduce to the same expression. Rewrite using `[map_list_sum, List.map_map, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `ζ _`. Conclude with `muK_gen_map q f ζ`.
-/
theorem muK_le (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    muK q A ≤ (muK q B).comap ((twF q 1).map f).hom := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨l, hl, rfl⟩
  refine Submodule.subset_span ⟨l.map (Prim.map f.hom), ?_, ?_⟩
  · have : ((l.map fun ζ => ζ.1).map f.hom).prod = f.hom 1 := by rw [← map_list_prod, hl]
    rw [map_one] at this
    rw [← this, List.map_map, List.map_map]
    rfl
  · rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ζ _
    exact muK_gen_map q f ζ

noncomputable def muT (q : ℕ) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ ((twF q 1).obj A ⧸ muK q A)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ ((twF q 1).map f).hom (muK_le q f))
  map_id A := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (𝟙 A)).hom x) = Submodule.Quotient.mk x
    rw [(twF q 1).map_id]; rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (f ≫ g)).hom x) =
      Submodule.Quotient.mk (((twF q 1).map g).hom (((twF q 1).map f).hom x))
    rw [(twF q 1).map_comp]; rfl

noncomputable def muτ (q : ℕ) : twF q 1 ⟶ muT q where
  app A := ModuleCat.ofHom (muK q A).mkQ
  naturality A B f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

/- English proof (translation)
Establish `h : (l.map fun ζ => twGenR A ζ).sum ∈ muK q A` using `Submodule.subset_span ⟨l, hl, rfl⟩`. Use `(Submodule.Quotient.mk_eq_zero (muK q A)).2 h` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ((muτ q).app A).hom (List.map (fun ζ => twGenR A ζ) l).sum`. Rewrite using `[map_list_sum, List.map_map]`.

Both sides reduce to the same expression.
-/
theorem muτ_list (q : ℕ) (A : CommRingCat.{0}) (l : List (Prim q A)) (hl : (l.map fun ζ => ζ.1).prod = 1) :
    (l.map fun ζ => ((muτ q).app A).hom (twGenR A ζ)).sum = 0 := by
  have h : (l.map fun ζ => twGenR A ζ).sum ∈ muK q A := Submodule.subset_span ⟨l, hl, rfl⟩
  have := (Submodule.Quotient.mk_eq_zero (muK q A)).2 h
  refine Eq.trans ?_ this
  change _ = ((muτ q).app A).hom (List.map (fun ζ => twGenR A ζ) l).sum
  rw [map_list_sum, List.map_map]
  rfl

def EtaleSheafifyMonoOfKernelLocallyZeroCriterion : Prop :=
  ∀ (q : ℕ) (P Q : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : P ⟶ Q),
    (∀ (U : Scheme.{0}) (x : P.obj Γ(U, ⊤)), (τ.app _).hom x = 0 → Loc U fun _ g => (P.map g.appTop).hom x = 0) →
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ))

def MuRootRelationSubmoduleEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (x : (twF q 1).obj Γ(U, ⊤)), x ∈ muK q Γ(U, ⊤) →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom x = 0

/- English proof (translation)
Introduce `q P Q τ h`. Establish `hli : Presheaf.IsLocallyInjective Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ τ)`. Use `⟨fun {X} x y hxy => ?_⟩` and prove the remaining obligations. Set `x' : P.obj Γ(X.unop, ⊤)` to `x`. Set `y' : P.obj Γ(X.unop, ⊤)` to `y`.

Establish `hxy' : (τ.app _).hom x' = (τ.app _).hom y'` using `hxy`. Take `⟨S, hS, hSP⟩` from `h X.unop (x' - y') (by rw [map_sub, hxy', sub_self])`. Use `Scheme.etaleTopology.superset_covering ?_ hS` and prove the remaining obligations. Introduce `V g hg`. Establish `h2 : (P.map g.appTop).hom (x' - y') = 0` using `hSP V g hg`.

Rewrite `h2` using `[map_sub, sub_eq_zero]`. Conclude with `h2`. Establish `: Sheaf.IsLocallyInjective ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ))` using `(Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hli`. Conclude with `Sheaf.mono_of_isLocallyInjective _`.
-/
theorem etale_sheafify_mono_of_kernel_locally_zero : EtaleSheafifyMonoOfKernelLocallyZeroCriterion := by
  intro q P Q τ h
  have hli : Presheaf.IsLocallyInjective Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ τ) := by
    refine ⟨fun {X} x y hxy => ?_⟩
    let x' : P.obj Γ(X.unop, ⊤) := x
    let y' : P.obj Γ(X.unop, ⊤) := y
    have hxy' : (τ.app _).hom x' = (τ.app _).hom y' := hxy
    obtain ⟨S, hS, hSP⟩ := h X.unop (x' - y') (by rw [map_sub, hxy', sub_self])
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    have h2 : (P.map g.appTop).hom (x' - y') = 0 := hSP V g hg
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have : Sheaf.IsLocallyInjective ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hli
  exact Sheaf.mono_of_isLocallyInjective _

/- English proof (translation)
Introduce `q _`. Use `⟨muT q, muτ q, h1 q _ _ (muτ q) fun U x hx => h2 q U x ?_, muτ_list q⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.mk_eq_zero (muK q _)).1 hx`.
-/
theorem exists_etale_mono_muTwist_quotient_of_locally_zero (h1 : EtaleSheafifyMonoOfKernelLocallyZeroCriterion) (h2 : MuRootRelationSubmoduleEtaleLocallyZero) :
    ExistsEtaleMonoMuTwistKillingRootRelations := by
  intro q _
  refine ⟨muT q, muτ q, h1 q _ _ (muτ q) fun U x hx => h2 q U x ?_, muτ_list q⟩
  exact (Submodule.Quotient.mk_eq_zero (muK q _)).1 hx

end LateralTheory.EtaleFoundations
