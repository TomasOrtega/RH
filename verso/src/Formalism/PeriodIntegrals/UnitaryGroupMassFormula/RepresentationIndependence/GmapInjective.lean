import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeMainT

noncomputable section

namespace PI.RepsIndep.Tr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components.
-/
theorem mem_gmap {γ : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ Formalism.HermitianLatticesTheory.gmap γ L ↔ γ.symm x ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ap_mem_gmap {γ : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} {x : S.V} :
    γ x ∈ Formalism.HermitianLatticesTheory.gmap γ L ↔ x ∈ L := by
  rw [mem_gmap, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smul_symm (γ : S.V ≃ₗ[E] S.V) (s : 𝓞 E) (x : S.V) : γ.symm (s • x) = s • γ.symm x := by
  rw [← algebraMap_smul E s x, map_smul, algebraMap_smul]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem gmap_symm_gmap (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ.symm (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm, ap_mem_gmap]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem gmap_inf (γ : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap γ A ⊓ Formalism.HermitianLatticesTheory.gmap γ B := by
  ext x
  simp only [mem_gmap, Submodule.mem_inf]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem gmap_sup (γ : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap γ A ⊔ Formalism.HermitianLatticesTheory.gmap γ B := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_sup]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gmap_span (γ : S.V ≃ₗ[E] S.V) (s : Set S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (Submodule.span (𝓞 E) s) = Submodule.span (𝓞 E) (γ '' s) := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_span]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem coe_gmap (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = γ '' (L : Set S.V) := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem gmap_toO (γ : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (toO S U) = toO S (U.map (γ : S.V →ₗ[E] S.V)) := by
  ext x
  rw [mem_gmap]
  simp only [toO, Submodule.restrictScalars_mem]
  rw [Submodule.mem_map_equiv]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gmap_smul (γ : S.V ≃ₗ[E] S.V) (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (I • L) = I • Formalism.HermitianLatticesTheory.gmap γ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  exact Submodule.map_smul'' _ _ _

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gmap_locS (γ : S.V ≃ₗ[E] S.V) (M : Submonoid (𝓞 E)) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.locS M L) = Formalism.HermitianLatticesTheory.locS M (Formalism.HermitianLatticesTheory.gmap γ L) := by
  ext x
  rw [mem_gmap]
  show (∃ s ∈ M, s • γ.symm x ∈ L) ↔ ∃ s ∈ M, s • x ∈ Formalism.HermitianLatticesTheory.gmap γ L
  simp only [mem_gmap, smul_symm]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gmap_locP (γ : S.V ≃ₗ[E] S.V) (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.localization₂ p L) = Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.gmap γ L) :=
  gmap_locS γ p.primeCompl L

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem spanE_gmap (γ : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    spanE S (Formalism.HermitianLatticesTheory.gmap γ M) = (spanE S M).map (γ : S.V →ₗ[E] S.V) := by
  rw [spanE, spanE, coe_gmap, Submodule.map_span]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iso_ap {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) :
    S.hT (γ x) (γ y) = S.hT x y :=
  hγ x y

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iso_symm {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) : γ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT :=
  (Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hγ

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem orth_map {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V) :
    orth S (U.map (γ : S.V →ₗ[E] S.V)) = (orth S U).map (γ : S.V →ₗ[E] S.V) := by
  ext v
  rw [Submodule.mem_map_equiv, mem_orth, mem_orth]
  constructor
  · intro h x hx
    have := h (γ x) (Submodule.mem_map_of_mem hx)
    rw [← iso_ap hγ x (γ.symm v), LinearEquiv.apply_symm_apply]
    simpa using this
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have := h x hx
    rw [← iso_ap hγ x (γ.symm v), LinearEquiv.apply_symm_apply] at this
    simpa using this

variable {r : ℕ}

def mapF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) : FlagG S r T where
  e := fun a => γ (F.e a)
  z := γ F.z
  e_indep := F.e_indep.map' (γ : S.V →ₗ[E] S.V) γ.ker
  e_iso a b := by rw [iso_ap hγ]; exact F.e_iso a b
  z_orth a := by rw [iso_ap hγ]; exact F.z_orth a
  z_norm := by rw [iso_ap hγ]; exact F.z_norm

def mapL {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) : LFlag S r T :=
  ⟨mapF γ hγ F.fl, γ F.zt⟩

/- English proof (translation)
Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Simplify by unfolding definitions. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem flag_ext {T : E} {F G : FlagG S r T} (he : F.e = G.e) (hz : F.z = G.z) : F = G := by
  cases F
  cases G
  dsimp only at he hz
  subst he hz
  rfl

/- English proof (translation)
Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Simplify by unfolding definitions. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem lflag_ext {T : E} {F G : LFlag S r T} (h : F.fl = G.fl) (hz : F.zt = G.zt) : F = G := by
  cases F
  cases G
  dsimp only at h hz
  subst h hz
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem mapL_symm {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    mapL γ.symm (iso_symm hγ) (mapL γ hγ F) = F := by
  apply lflag_ext
  · apply flag_ext
    · funext a
      simp [mapL, mapF]
    · simp [mapL, mapF]
  · simp [mapL]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem mapL_symm' {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ' : γ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : LFlag S r T) : mapL γ hγ (mapL γ.symm hγ' F) = F := by
  apply lflag_ext
  · apply flag_ext
    · funext a
      simp [mapL, mapF]
    · simp [mapL, mapF]
  · simp [mapL]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem fvec_mapF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (i : Fin (r + 1)) :
    (mapF γ hγ F).fvec i = γ (F.fvec i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [FlagG.fvec, mapF]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frame_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (i : Fin (r + 1)) :
    frame (mapL γ hγ F) i = γ (frame F i) :=
  fvec_mapF hγ F.fl i

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem Xa_mapF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) :
    (mapF γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.Xa, FlagG.Xa, Submodule.map_span, Set.image_image]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem X_mapF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) :
    (mapF γ hγ F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.X, FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Zhat_mapF {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T)
    (F' : FlagG S r T') : Zhat (mapF γ hγ F) (mapF γ hγ F') = Zhat F F' := by
  ext a b
  show brS S ((mapF γ hγ F').fvec b) ((mapF γ hγ F).fvec a) = brS S (F'.fvec b) (F.fvec a)
  rw [fvec_mapF, fvec_mapF]
  exact iso_ap hγ _ _

end PI.RepsIndep.Tr
