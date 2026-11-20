import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecsMapArrow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}}

/- English proof (translation)
Use `Scheme.Modules.hom_ext _ _ fun W ↦ ?_` and prove the remaining obligations. Use extensionality with `s`. Establish `hcov : W ≤ ⨆ B : {B : X.Opens // P B ∧ B ≤ W}, B.1`. Introduce `x hx`. Take `⟨B, hB, hBW, hxB⟩` from `hP W x hx`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨B, hB, hBW⟩, hxB⟩`. Use `TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X) (fun B : {B : X.Opens // P B ∧ B ≤ W} ↦ B.1) W (fun B ↦ homOfLE B.2.2) hcov _ _ fun B ↦ ?_` and prove the remaining obligations. Establish `nat` using `ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE B.2.2).op) s`. Establish `e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE B.2.2).op)) (φ.app W s) = 0` using `nat.symm.trans (h B.1 B.2.1 _)`. Use `e1.trans ?_` and prove the remaining obligations.

Rewrite using `[Scheme.Modules.Hom.zero_app]`. Simplify using the standard rewrite rules.
-/
theorem hom_eq_zero_of_basis {M N : X.Modules} (φ : M ⟶ N) (P : X.Opens → Prop)
    (hP : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ B, P B ∧ B ≤ W ∧ x ∈ B)
    (h : ∀ B, P B → ∀ s : Γ(M, B), φ.app B s = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  have hcov : W ≤ ⨆ B : {B : X.Opens // P B ∧ B ≤ W}, B.1 := by
    intro x hx
    obtain ⟨B, hB, hBW, hxB⟩ := hP W x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨B, hB, hBW⟩, hxB⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun B : {B : X.Opens // P B ∧ B ≤ W} ↦ B.1) W
    (fun B ↦ homOfLE B.2.2) hcov _ _ fun B ↦ ?_
  have nat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE B.2.2).op) s
  have e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE B.2.2).op)) (φ.app W s) = 0 :=
    nat.symm.trans (h B.1 B.2.1 _)
  refine e1.trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

/- English proof (translation)
Establish `h0 : S.arrow ≫ cokernel.π T.arrow = 0`. Use `hom_eq_zero_of_basis _ (fun B ↦ ∃ U ∈ t, ∃ f : Γ(X, (U : X.Opens)), B = X.basicOpen f) ?_ ?_` and prove the remaining obligations. Introduce `W x hx`. Take `⟨U, hU, hxU⟩` from `ht x`. Take `⟨f, hfW, hxf⟩` from `U.2.exists_basicOpen_le (V := W) ⟨x, hx⟩ hxU`.

Conclude with `⟨X.basicOpen f, ⟨U, hU, f, rfl⟩, hfW, hxf⟩`. Introduce and unpack `B ⟨U, hU, f, rfl⟩ s`. Take `⟨y, hy⟩` from `h U hU f ⟨s, rfl⟩`. Establish `hz : (T.arrow ≫ cokernel.π T.arrow).app (X.basicOpen f) y = 0`. Rewrite using `[cokernel.condition]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(cokernel.π T.arrow).app _ (S.arrow.app _ s) = 0`. Rewrite using `[← hy]`. Conclude with `hz`. Use `Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) ?_` and prove the remaining obligations.

Conclude with `Abelian.monoLift_comp _ _ _`.
-/
theorem le_of_secs_basicOpen {E : X.Modules} (S T : Subobject E) (t : Set X.affineOpens)
    (ht : ∀ x : X, ∃ U ∈ t, x ∈ (U : X.Opens))
    (h : ∀ U ∈ t, ∀ f : Γ(X, (U : X.Opens)), secs S (X.basicOpen f) ⊆ secs T (X.basicOpen f)) :
    S ≤ T := by
  have h0 : S.arrow ≫ cokernel.π T.arrow = 0 := by
    refine hom_eq_zero_of_basis _
      (fun B ↦ ∃ U ∈ t, ∃ f : Γ(X, (U : X.Opens)), B = X.basicOpen f) ?_ ?_
    · intro W x hx
      obtain ⟨U, hU, hxU⟩ := ht x
      obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le (V := W) ⟨x, hx⟩ hxU
      exact ⟨X.basicOpen f, ⟨U, hU, f, rfl⟩, hfW, hxf⟩
    · rintro B ⟨U, hU, f, rfl⟩ s
      obtain ⟨y, hy⟩ := h U hU f ⟨s, rfl⟩
      have hz : (T.arrow ≫ cokernel.π T.arrow).app (X.basicOpen f) y = 0 := by
        rw [cokernel.condition]; rfl
      change (cokernel.π T.arrow).app _ (S.arrow.app _ s) = 0
      rw [← hy]
      exact hz
  refine Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) ?_
  exact Abelian.monoLift_comp _ _ _

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `resO h (resO le_top _) = resO le_top _`. Rewrite using `[resO_resO]`.
-/
lemma toFunctions_res {U V : X.Opens} (h : V ≤ U) (a : A) :
    resO h (toFunctions (A := A) U a) = toFunctions (A := A) V a := by
  change resO h (resO le_top _) = resO le_top _
  rw [resO_resO]

/- English proof (translation)
Rewrite using `[Ideal.map_map]`. Use `congr 1`. Conclude with `RingHom.ext (toFunctions_res h)`.
-/
lemma map_toFunctions_res {U V : X.Opens} (h : V ≤ U) (J : Ideal A) :
    Ideal.map (resO h) (Ideal.map (toFunctions (A := A) U) J) = Ideal.map (toFunctions (A := A) V) J := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (toFunctions_res h)

/- English proof (translation)
Use `Submodule.smul_induction_on hm ?_ ?_` and prove the remaining obligations. Introduce `a ha z _`. Rewrite using `[resF_smul]`. Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Rewrite using `[← map_toFunctions_res h]`.

Conclude with `Ideal.mem_map_of_mem _ ha`. Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
lemma resF_mem_pow (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (n : ℕ) (m : Γ(F, U))
    (hm : m ∈ (Ideal.map (toFunctions (A := A) U) (I ^ n) • ⊤ : Submodule Γ(X, U) Γ(F, U))) :
    resF F h m ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha z _
    rw [resF_smul]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← map_toFunctions_res h]
    exact Ideal.mem_map_of_mem _ ha
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}} {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

/- English proof (translation)
Take `⟨e₁, z₁, hz₁, hr₁⟩` from `h₁`. Take `⟨e₂, z₂, hz₂, hr₂⟩` from `h₂`. Use `⟨e₁ + e₂, f ^ e₂ • z₁ + f ^ e₁ • z₂, add_mem (P.smul_mem _ hz₁) (P.smul_mem _ hz₂), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, resF_smul, resF_smul, hr₁, hr₂, smul_smul, smul_smul, smul_add, map_pow, map_pow, pow_add, mul_comm (resO (X.basicOpen_le f) f ^ e₂)]`.
-/
lemma sat_add (F : X.Modules) {V : X.Opens} (f : Γ(X, V)) (P : Submodule Γ(X, V) Γ(F, V))
    (y₁ y₂ : Γ(F, X.basicOpen f))
    (h₁ : ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • y₁)
    (h₂ : ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • y₂) :
    ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • (y₁ + y₂) := by
  obtain ⟨e₁, z₁, hz₁, hr₁⟩ := h₁
  obtain ⟨e₂, z₂, hz₂, hr₂⟩ := h₂
  refine ⟨e₁ + e₂, f ^ e₂ • z₁ + f ^ e₁ • z₂, add_mem (P.smul_mem _ hz₁) (P.smul_mem _ hz₂), ?_⟩
  rw [map_add, resF_smul, resF_smul, hr₁, hr₂, smul_smul, smul_smul, smul_add, map_pow, map_pow,
    pow_add, mul_comm (resO (X.basicOpen_le f) f ^ e₂)]

/- English proof (translation)
Use `set P : Submodule Γ(X, V) Γ(F, V) := Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ with hPdef`. Establish `key : ∀ a ∈ Ideal.map (toFunctions (A` using `A) (X.basicOpen f)) (I ^ n), ∀ z : Γ(F, X.basicOpen f), ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧ resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • (a • z) := by`. Introduce `a ha`. Rewrite `ha` using `[← map_toFunctions_res (X.basicOpen_le f)]`. Express the relevant statement in the definitionally equal form `a ∈ Ideal.span _ at ha`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨b, hb, rfl⟩` from `ha`. Introduce `z`. Take `⟨e, z', hz'⟩` from `qcoh_exists_res_eq F hV f z`.

Use `⟨e, b • z', Submodule.smul_mem_smul hb Submodule.mem_top, ?_⟩` and prove the remaining obligations. Rewrite using `[resF_smul, hz', smul_comm]`. Consider the case `zero`. Introduce `z`. Conclude with `⟨0, 0, P.zero_mem, by simp⟩`.

Consider the case `add a₁ a₂ _ _ h₁ h₂`. Introduce `z`. Rewrite using `[add_smul]`. Conclude with `sat_add F f P _ _ (h₁ z) (h₂ z)`. Consider the case `smul s a _ h`.

Introduce `z`. Rewrite using `[smul_eq_mul, mul_smul, smul_comm s a]`. Conclude with `h (s • z)`. Use `Submodule.smul_induction_on hy (fun a ha z _ ↦ key a ha z) ?_` and prove the remaining obligations. Introduce `y₁ y₂ h₁ h₂`.

Conclude with `sat_add F f P _ _ h₁ h₂`.
-/
lemma exists_res_eq_of_mem_pow (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (f : Γ(X, V)) (n : ℕ) (y : Γ(F, X.basicOpen f))
    (hy : y ∈ (Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ n) • ⊤ :
      Submodule Γ(X, X.basicOpen f) Γ(F, X.basicOpen f))) :
    ∃ (e : ℕ) (y' : Γ(F, V)),
      y' ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • y := by
  set P : Submodule Γ(X, V) Γ(F, V) := Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ with hPdef
  have key : ∀ a ∈ Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ n),
      ∀ z : Γ(F, X.basicOpen f), ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
        resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • (a • z) := by
    intro a ha
    rw [← map_toFunctions_res (X.basicOpen_le f)] at ha
    change a ∈ Ideal.span _ at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨b, hb, rfl⟩ := ha
      intro z
      obtain ⟨e, z', hz'⟩ := qcoh_exists_res_eq F hV f z
      refine ⟨e, b • z', Submodule.smul_mem_smul hb Submodule.mem_top, ?_⟩
      rw [resF_smul, hz', smul_comm]
    | zero =>
      intro z
      exact ⟨0, 0, P.zero_mem, by simp⟩
    | add a₁ a₂ _ _ h₁ h₂ =>
      intro z
      rw [add_smul]
      exact sat_add F f P _ _ (h₁ z) (h₂ z)
    | smul s a _ h =>
      intro z
      rw [smul_eq_mul, mul_smul, smul_comm s a]
      exact h (s • z)
  refine Submodule.smul_induction_on hy (fun a ha z _ ↦ key a ha z) ?_
  intro y₁ y₂ h₁ h₂
  exact sat_add F f P _ _ h₁ h₂

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}} {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

/- English proof (translation)
The claim follows from `X.toRingedSpace.isUnit_res_basicOpen f`.
-/
lemma isUnit_resO_basicOpen {V : X.Opens} (f : Γ(X, V)) : IsUnit (resO (X.basicOpen_le f) f) :=
  X.toRingedSpace.isUnit_res_basicOpen f

/- English proof (translation)
Use `set u := resO (X.basicOpen_le f) f with hu`. Take `⟨e₁, y', hy', hr₁⟩` from `exists_res_eq_of_mem_pow I E hV f (n + k) _ hx`. Take `⟨e₂, d', hd'⟩` from `qcoh_exists_res_eq (D : X.Modules) hV f x`. Establish `h0 : resF E (X.basicOpen_le f) (f ^ e₁ • D.arrow.app V d' - f ^ e₂ • y') = 0`. Rewrite using `[map_sub, resF_smul, resF_smul, resF_app, hd', Scheme.Modules.Hom.app_smul, hr₁, map_pow, map_pow, ← hu, smul_smul, smul_smul, mul_comm, sub_self]`.

Take `⟨e₃, he₃⟩` from `qcoh_exists_pow_smul_eq_zero E hV f _ h0`. Rewrite `he₃` using `[smul_sub, sub_eq_zero]`. Establish `hmem : D.arrow.app V (f ^ e₃ • f ^ e₁ • d') ∈ (Ideal.map (toFunctions (A` using `A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) := by`. Rewrite using `[Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, he₃]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy')`.

Establish `h2` using `resF_mem_pow I (D : X.Modules) (X.basicOpen_le f) n _ (hk n _ hmem)`. Rewrite `h2` using `[resF_smul, resF_smul, hd', map_pow, map_pow, ← hu]`. Establish `hU : IsUnit (u ^ e₃ * u ^ e₁ * u ^ e₂)` using `(((isUnit_resO_basicOpen f).pow e₃).mul ((isUnit_resO_basicOpen f).pow e₁)).mul ((isUnit_resO_basicOpen f).pow e₂)`. Rewrite `h2` using `[smul_smul, smul_smul]`. Conclude with `(Submodule.smul_mem_iff_of_isUnit _ hU).mp h2`.
-/
theorem local_step {E : X.Modules} [E.IsQuasicoherent] (D : Subobject E)
    [(D : X.Modules).IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) (k : ℕ)
    (hk : ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V)))
    (f : Γ(X, V)) (n : ℕ) (x : Γ((D : X.Modules), X.basicOpen f))
    (hx : D.arrow.app _ x ∈ (Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ (n + k)) • ⊤ :
      Submodule Γ(X, X.basicOpen f) Γ(E, X.basicOpen f))) :
    x ∈ (Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ n) • ⊤ :
      Submodule Γ(X, X.basicOpen f) Γ((D : X.Modules), X.basicOpen f)) := by
  set u := resO (X.basicOpen_le f) f with hu
  obtain ⟨e₁, y', hy', hr₁⟩ := exists_res_eq_of_mem_pow I E hV f (n + k) _ hx
  obtain ⟨e₂, d', hd'⟩ := qcoh_exists_res_eq (D : X.Modules) hV f x
  have h0 : resF E (X.basicOpen_le f) (f ^ e₁ • D.arrow.app V d' - f ^ e₂ • y') = 0 := by
    rw [map_sub, resF_smul, resF_smul, resF_app, hd', Scheme.Modules.Hom.app_smul, hr₁, map_pow,
      map_pow, ← hu, smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨e₃, he₃⟩ := qcoh_exists_pow_smul_eq_zero E hV f _ h0
  rw [smul_sub, sub_eq_zero] at he₃
  have hmem : D.arrow.app V (f ^ e₃ • f ^ e₁ • d') ∈
      (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, he₃]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy')
  have h2 := resF_mem_pow I (D : X.Modules) (X.basicOpen_le f) n _ (hk n _ hmem)
  rw [resF_smul, resF_smul, hd', map_pow, map_pow, ← hu] at h2
  have hU : IsUnit (u ^ e₃ * u ^ e₁ * u ^ e₂) :=
    (((isUnit_resO_basicOpen f).pow e₃).mul ((isUnit_resO_basicOpen f).pow e₁)).mul
      ((isUnit_resO_basicOpen f).pow e₂)
  rw [smul_smul, smul_smul] at h2
  exact (Submodule.smul_mem_iff_of_isUnit _ hU).mp h2

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}} {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

/- English proof (translation)
Set `φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V)` to `{ toFun := D.arrow.app V map_add' := map_add _ map_smul' := Scheme.Modules.Hom.app_smul D.arrow }`. Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul (Ideal.map (toFunctions (A := A) V) I) (LinearMap.range φ)`. Use `⟨k, fun n x hx ↦ ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[Ideal.map_pow]`. Establish `h1 : φ x ∈ (Ideal.map (toFunctions (A` using `A) V) I) ^ (n + k) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ⊓ LinearMap.range φ := ⟨hx, ⟨x, rfl⟩⟩`.

Rewrite `h1` using `[hk (n + k) (by omega), Nat.add_sub_cancel]`. Establish `h2 : (Ideal.map (toFunctions (A` using `A) V) I) ^ n • ((Ideal.map (toFunctions (A := A) V) I) ^ k • (⊤ : Submodule Γ(X, V) Γ(E, V)) ⊓ LinearMap.range φ) ≤ ((Ideal.map (toFunctions (A := A) V) I) ^ n • (⊤ : Submodule Γ(X, V) Γ((D : X.Modules), V))).map φ := by`. Rewrite using `[Submodule.map_smul'', Submodule.map_top]`. Conclude with `Submodule.smul_mono le_rfl inf_le_right`. Take `⟨y, hy, hyx⟩` from `h2 h1`.

Rewrite `hy` using `[injective_app_of_mono D.arrow V hyx]`. Then use the resulting hypothesis.
-/
theorem exists_const_of_finite {E : X.Modules} (D : Subobject E) (V : X.Opens)
    [IsNoetherianRing Γ(X, V)] [Module.Finite Γ(X, V) Γ(E, V)] :
    ∃ k : ℕ, ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V)) := by
  let φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V) :=
    { toFun := D.arrow.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul D.arrow }
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.map (toFunctions (A := A) V) I)
    (LinearMap.range φ)
  refine ⟨k, fun n x hx ↦ ?_⟩
  rw [Ideal.map_pow] at hx ⊢
  have h1 : φ x ∈ (Ideal.map (toFunctions (A := A) V) I) ^ (n + k) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ⊓
      LinearMap.range φ := ⟨hx, ⟨x, rfl⟩⟩
  rw [hk (n + k) (by omega), Nat.add_sub_cancel] at h1
  have h2 : (Ideal.map (toFunctions (A := A) V) I) ^ n •
      ((Ideal.map (toFunctions (A := A) V) I) ^ k • (⊤ : Submodule Γ(X, V) Γ(E, V)) ⊓ LinearMap.range φ) ≤
      ((Ideal.map (toFunctions (A := A) V) I) ^ n • (⊤ : Submodule Γ(X, V) Γ((D : X.Modules), V))).map φ := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨y, hy, hyx⟩ := h2 h1
  rwa [injective_app_of_mono D.arrow V hyx] at hy

/- English proof (translation)
Introduce `n x hx`. Use `hk n x (Submodule.smul_mono_left (Ideal.map_mono (Ideal.pow_le_pow_right ?_)) hx)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
lemma const_mono {E : X.Modules} (D : Subobject E) (V : X.Opens) {k k' : ℕ} (hkk : k ≤ k')
    (hk : ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V))) :
    ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k')) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V)) := by
  intro n x hx
  refine hk n x (Submodule.smul_mono_left (Ideal.map_mono (Ideal.pow_le_pow_right ?_)) hx)
  omega

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE

open GlobalTheory.CompanionTheory.GE.ArtinRees in

/- English proof (translation)
Use `haveI : E.IsQuasicoherent := hE.1`. Establish `hc : ∀ U : X.affineOpens, ∃ k : ℕ, ∀ (n : ℕ) (x : Γ((D : X.Modules), (U : X.Opens))), D.arrow.app (U : X.Opens) x ∈ (Ideal.map (toFunctions (A` using `A) (U : X.Opens)) (I ^ (n + k)) • ⊤ : Submodule Γ(X, (U : X.Opens)) Γ(E, (U : X.Opens))) → x ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ n) • ⊤ : Submodule Γ(X, (U : X.Opens)) Γ((D : X.Modules), (U : X.Opens))) := fun U ↦ by haveI := hE.2 (U : X.Opens) U.2 haveI := IsL …`. Conclude with `exists_const_of_finite I D (U : X.Opens)`. Use `choose c hc using hc`. Establish `hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X)`.

Introduce `x _`. Take `⟨U, ⟨V, hV, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Conclude with `Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ (U : X.Opens).isOpen) hcov`. Use `⟨t.sup c, fun n ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[Subobject.inf_eq_map_pullback]`. Use `leOfHom ((Subobject.map D.arrow).map (homOfLE ?_))` and prove the remaining obligations. Use `le_of_secs_basicOpen _ _ (↑t : Set X.affineOpens) ?_ ?_` and prove the remaining obligations. Introduce `x`. Take `⟨U, hU, hxU⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`.

Conclude with `⟨U, hU, hxU⟩`. Introduce `U hU f y hy`. Rewrite `hy` using `[secs_pullback_arrow, secs_powSub I E inferInstance _ _ (U.2.basicOpen f)]`. Rewrite using `[secs_powSub I (D : X.Modules) hD _ _ (U.2.basicOpen f)]`. Use `haveI := hD`.

Conclude with `local_step I D U.2 (t.sup c) (const_mono I D (U : X.Opens) (Finset.le_sup (f := c) hU) (hc U)) f n y hy`.
-/
theorem artinRees_uniform {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}
    (hE : IsCoherent E) (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) :
    ∃ k : ℕ, ∀ n : ℕ, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) := by
  haveI : E.IsQuasicoherent := hE.1
  have hc : ∀ U : X.affineOpens, ∃ k : ℕ, ∀ (n : ℕ) (x : Γ((D : X.Modules), (U : X.Opens))),
      D.arrow.app (U : X.Opens) x ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ (n + k)) • ⊤ :
        Submodule Γ(X, (U : X.Opens)) Γ(E, (U : X.Opens))) →
      x ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ n) • ⊤ :
        Submodule Γ(X, (U : X.Opens)) Γ((D : X.Modules), (U : X.Opens))) := fun U ↦ by
    haveI := hE.2 (U : X.Opens) U.2
    haveI := IsLocallyNoetherian.component_noetherian U
    exact exists_const_of_finite I D (U : X.Opens)
  choose c hc using hc
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := by
    intro x _
    obtain ⟨U, ⟨V, hV, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ (U : X.Opens).isOpen) hcov
  refine ⟨t.sup c, fun n ↦ ?_⟩
  rw [Subobject.inf_eq_map_pullback]
  refine leOfHom ((Subobject.map D.arrow).map (homOfLE ?_))
  refine le_of_secs_basicOpen _ _ (↑t : Set X.affineOpens) ?_ ?_
  · intro x
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨U, hU, hxU⟩
  · intro U hU f y hy
    rw [secs_pullback_arrow, secs_powSub I E inferInstance _ _ (U.2.basicOpen f)] at hy
    rw [secs_powSub I (D : X.Modules) hD _ _ (U.2.basicOpen f)]
    haveI := hD
    exact local_step I D U.2 (t.sup c)
      (const_mono I D (U : X.Opens) (Finset.le_sup (f := c) hU) (hc U)) f n y hy

end GlobalTheory.CompanionTheory.GE
