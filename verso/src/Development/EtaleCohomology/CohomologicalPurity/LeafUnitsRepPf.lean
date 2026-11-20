import Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Thom.UnitsRepPf

variable (R : Type) [CommRing R] (m : ℕ)

abbrev P := MvPolynomial (Fin m) R
abbrev f : P R m := ∏ i, MvPolynomial.X i
abbrev R' := Localization.Away (f R m)

def ι : R →+* R' R m := (algebraMap (P R m) (R' R m)).comp MvPolynomial.C

variable {R m}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hunit {B : Type} [CommRing B] (ψ : R' R m →+* B) (i : Fin m) :
    IsUnit (ψ (algebraMap (P R m) (R' R m) (MvPolynomial.X i))) :=
  isUnit_of_dvd_unit (map_dvd ψ (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))))
    ((IsLocalization.Away.algebraMap_isUnit (f R m)).map ψ)

def Φ {B : Type} [CommRing B] (ψ : R' R m →+* B) : (Fin m → Bˣ) × (R →+* B) :=
  (fun i => (hunit ψ i).unit, ψ.comp (ι R m))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem Φ_inj {B : Type} [CommRing B] : Function.Injective (Φ (R := R) (m := m) (B := B)) := by
  intro ψ₁ ψ₂ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply IsLocalization.ringHom_ext (Submonoid.powers (f R m))
  apply MvPolynomial.ringHom_ext
  · intro r
    exact RingHom.congr_fun h2 r
  · intro i
    have := congrArg (fun u => ((u i : Bˣ) : B)) h1
    simpa [Φ] using this

/- English proof (translation)
Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem Φ_surj {B : Type} [CommRing B] : Function.Surjective (Φ (R := R) (m := m) (B := B)) := by
  rintro ⟨u, g⟩
  let e : P R m →+* B := MvPolynomial.eval₂Hom g (fun i => (u i : B))
  have hg : IsUnit (e (f R m)) := ⟨∏ i, u i, by simp [e, map_prod]⟩
  refine ⟨IsLocalization.Away.lift (f R m) hg, ?_⟩
  refine Prod.ext ?_ ?_
  · funext i; apply Units.ext; simp [Φ, IsLocalization.Away.lift_eq, e]
  · ext r; simp [Φ, ι, IsLocalization.Away.lift_eq, e]

def back {X : Scheme.{0}} {A : CommRingCat.{0}} (φ : X ⟶ Spec A) : A ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso A).inv ≫ φ.appTop

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem back_inj {X : Scheme.{0}} {A : CommRingCat.{0}} : Function.Injective (back (X := X) (A := A)) := by
  intro a b h
  exact (ΓSpec.adjunction.homEquiv X (op A)).symm.injective (Opposite.unop_injective h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem back_surj {X : Scheme.{0}} {A : CommRingCat.{0}} : Function.Surjective (back (X := X) (A := A)) := by
  intro φ
  exact ⟨_, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem back_comp {X : Scheme.{0}} {A A' : CommRingCat.{0}} (φ : X ⟶ Spec A') (g : A ⟶ A') :
    back (φ ≫ Spec.map g) = g ≫ back φ := by
  simp only [back, Scheme.Hom.comp_appTop, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem back_nat {X Y : Scheme.{0}} {A : CommRingCat.{0}} (h : Y ⟶ X) (φ : X ⟶ Spec A) :
    back (h ≫ φ) = back φ ≫ h.appTop := by
  simp [back]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem back_ι {X : Scheme.{0}} (φ : X ⟶ Spec (CommRingCat.of (R' R m))) :
    (back (φ ≫ Spec.map (CommRingCat.ofHom (ι R m)))).hom = (back φ).hom.comp (ι R m) := by
  rw [back_comp]; rfl

def τ : yoneda.obj (Spec (CommRingCat.of (R' R m))) ⟶
    FunctorToTypes.prod (Uts m) (yoneda.obj (Spec (CommRingCat.of R))) where
  app X := ↾fun φ => ((Φ (back φ).hom).1, φ ≫ Spec.map (CommRingCat.ofHom (ι R m)))
  naturality X Y h := by
    ext φ
    · funext i
      apply Units.ext
      change ((hunit (back (h.unop ≫ φ)).hom i).unit : Γ(Y.unop, ⊤)) =
        (Units.map ((Scheme.Hom.appTop h.unop).hom : Γ(X.unop, ⊤) →* Γ(Y.unop, ⊤))
          ((hunit (back φ).hom i).unit) : Γ(Y.unop, ⊤))
      simp only [IsUnit.unit_spec, Units.coe_map, back_nat]
      rfl
    · change (h.unop ≫ φ) ≫ Spec.map (CommRingCat.ofHom (ι R m)) =
        h.unop ≫ (φ ≫ Spec.map (CommRingCat.ofHom (ι R m)))
      rw [Category.assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem τ_bij (X : Scheme.{0}ᵒᵖ) : Function.Bijective ((τ (R := R) (m := m)).app X) := by
  constructor
  · intro φ₁ φ₂ h
    have h1 : (Φ (back φ₁).hom).1 = (Φ (back φ₂).hom).1 := by
      have := congrArg Prod.fst h; exact this
    have h2' : φ₁ ≫ Spec.map (CommRingCat.ofHom (ι R m)) = φ₂ ≫ Spec.map (CommRingCat.ofHom (ι R m)) := by
      have := congrArg Prod.snd h; exact this
    have h2 := congrArg (fun p => (back p).hom) h2'
    simp only [back_ι] at h2
    apply back_inj
    apply CommRingCat.hom_ext
    apply Φ_inj
    exact Prod.ext h1 h2
  · rintro ⟨u, χ⟩
    obtain ⟨ψ, hψ⟩ := Φ_surj (R := R) (m := m) (B := Γ(X.unop, ⊤)) (u, (back χ).hom)
    obtain ⟨φ, hφ⟩ := back_surj (CommRingCat.ofHom ψ)
    refine ⟨φ, ?_⟩
    refine Prod.ext ?_ ?_
    · change (Φ (back φ).hom).1 = u
      rw [hφ]; exact congrArg Prod.fst hψ
    · change φ ≫ Spec.map (CommRingCat.ofHom (ι R m)) = χ
      apply back_inj
      apply CommRingCat.hom_ext
      rw [back_ι, hφ]
      exact congrArg Prod.snd hψ

instance (X : Scheme.{0}ᵒᵖ) : IsIso ((τ (R := R) (m := m)).app X) :=
  (isIso_iff_bijective _).mpr (τ_bij X)

instance : IsIso (τ (R := R) (m := m)) := NatIso.isIso_of_isIso_app _

end LateralTheory.CohomologicalPurity.Thom.UnitsRepPf

namespace LateralTheory.CohomologicalPurity.Thom
open UnitsRepPf in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem LeafUnitsRep_of : LeafUnitsRep := by
  intro R _ m
  exact ⟨R' R m, inferInstance, ι R m,
    ⟨FunctorToTypes.binaryProductIso _ _ ≪≫ (asIso (τ (R := R) (m := m))).symm⟩⟩

end LateralTheory.CohomologicalPurity.Thom
