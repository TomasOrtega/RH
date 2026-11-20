import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteAbelianWeightDecomposition
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeisenbergWeightDim

variable {F : Type} [Field F] {A : Type} [CommGroup A] {E : Type} [AddCommGroup E] [Module F E]

/- English proof (translation)
The claim follows from `Units.ext (smul_left_injective F hw h)`.
-/
theorem units_eq_of_smul_eq {x y : Fˣ} {w : E} (hw : w ≠ 0) (h : (x : F) • w = (y : F) • w) :
    x = y :=
  Units.ext (smul_left_injective F hw h)

variable [Nontrivial E] {e : A → A → Fˣ} {Φ : A → (E ≃ₗ[F] E)}

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : E)`. Establish `hw : Φ a (Φ b v) ≠ 0` using `by simpa using hv`. Apply `units_eq_of_smul_eq hw` to reduce the goal to its premises. Rewrite using `[Units.val_mul, mul_smul, ← hc b a v, ← hc a b v, Units.val_one, one_smul]`.
-/
theorem comm_swap (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a b : A) :
    e a b * e b a = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hw : Φ a (Φ b v) ≠ 0 := by simpa using hv
  apply units_eq_of_smul_eq hw
  rw [Units.val_mul, mul_smul, ← hc b a v, ← hc a b v, Units.val_one, one_smul]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : E)`. Establish `hw : Φ b (Φ (a * a') v) ≠ 0` using `by simpa using hv`. Apply `units_eq_of_smul_eq hw` to reduce the goal to its premises. Take `⟨c, h⟩` from `hm a a'`. Rewrite using `[← hc, h, h, hc a' b, map_smul, hc a b, map_smul, Units.val_mul]`.

Simplify using `only [smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm_mul_left (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a a' b : A) :
    e (a * a') b = e a b * e a' b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hw : Φ b (Φ (a * a') v) ≠ 0 := by simpa using hv
  apply units_eq_of_smul_eq hw
  obtain ⟨c, h⟩ := hm a a'
  rw [← hc, h, h, hc a' b, map_smul, hc a b, map_smul, Units.val_mul]
  simp only [smul_smul]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[eq_inv_of_mul_eq_one_left (comm_swap hc a (b * b')), eq_inv_of_mul_eq_one_left (comm_swap hc a b), eq_inv_of_mul_eq_one_left (comm_swap hc a b'), comm_mul_left hm hc, mul_inv]`.
-/
theorem comm_mul_right (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a b b' : A) :
    e a (b * b') = e a b * e a b' := by
  rw [eq_inv_of_mul_eq_one_left (comm_swap hc a (b * b')),
    eq_inv_of_mul_eq_one_left (comm_swap hc a b), eq_inv_of_mul_eq_one_left (comm_swap hc a b'),
    comm_mul_left hm hc, mul_inv]

/- English proof (translation)
Set `P : A →* (A →* Fˣ)` to `MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => e b a) (fun b b' => comm_mul_left hm hc b b' a)) (fun a a' => by`. Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `b`. Conclude with `comm_mul_right hm hc b a a')`. Establish `hinj : Function.Injective P`.

Rewrite using `[injective_iff_map_eq_one]`. Introduce `a ha`. Apply `hn` to reduce the goal to its premises. Introduce `b`. Establish `h1 : e b a = 1` using `DFunLike.congr_fun ha b`.

Establish `h2` using `comm_swap hc a b`. Rewrite `h2` using `[h1, _root_.mul_one]`. Then use the resulting hypothesis. Use `haveI : Finite (A →* Fˣ) := Finite.of_equiv A (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A F).some.toEquiv.symm`. Establish `hbij : Function.Bijective P` using `hinj.bijective_of_nat_card_le (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A F).le`. Take `⟨ψ, hψ⟩` from `MonoidHom.domRestrict_surjective F T χ`.

Take `⟨a, ha⟩` from `hbij.2 ψ`. Use `⟨a, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← hψ, ← ha]`. Both sides reduce to the same expression.
-/
theorem exists_comm_eq [Finite A] [HasEnoughRootsOfUnity F (Monoid.exponent A)]
    (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v))
    (hn : ∀ a, (∀ b, e a b = 1) → a = 1) (T : Subgroup A) (χ : T →* Fˣ) :
    ∃ a, ∀ t : T, e t a = χ t := by
  let P : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => e b a) (fun b b' => comm_mul_left hm hc b b' a))
      (fun a a' => by
        apply MonoidHom.ext
        intro b
        exact comm_mul_right hm hc b a a')
  have hinj : Function.Injective P := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply hn
    intro b
    have h1 : e b a = 1 := DFunLike.congr_fun ha b
    have h2 := comm_swap hc a b
    rwa [h1, _root_.mul_one] at h2
  haveI : Finite (A →* Fˣ) :=
    Finite.of_equiv A (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A F).some.toEquiv.symm
  have hbij : Function.Bijective P :=
    hinj.bijective_of_nat_card_le (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A F).le
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective F T χ
  obtain ⟨a, ha⟩ := hbij.2 ψ
  refine ⟨a, fun t => ?_⟩
  rw [← hψ, ← ha]
  rfl

end GlobalTheory.HeisenbergWeightDim

namespace GlobalTheory

open HeisenbergWeightDim in

/- English proof (translation)
Introduce `F _ _ A _ _ E _ _ _ e Φ hA hdim hm hc hn T lam hlam Wt hWt`. Establish `hpos : 0 < Nat.card A` using `Nat.card_pos`. Use `haveI : Nontrivial E := by`. Apply `Module.nontrivial_of_finrank_pos (R := F)` to reduce the goal to its premises. Break down `Nat.eq_zero_or_pos (Module.finrank F E) with h | h` into its components or cases.

Rewrite `hdim` using `[h]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Use `haveI : NeZero ((Nat.card A : ℕ) : F) := ⟨hA⟩`. Use `haveI : NeZero (Nat.card A) := ⟨hpos.ne'⟩`.

Use `haveI h0 : HasEnoughRootsOfUnity F (Nat.card A) := inferInstance`. Use `haveI hAe : HasEnoughRootsOfUnity F (Monoid.exponent A) := h0.of_dvd F Group.exponent_dvd_nat_card`. Use `haveI : HasEnoughRootsOfUnity F (Monoid.exponent T) := hAe.of_dvd F (Monoid.exponent_submonoid_dvd T.toSubmonoid)`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot F (Nat.card A)`. Set `ρ : Representation F T E` to `{ toFun := fun t => (lam t : E →ₗ[F] E) map_one' := by ext v; simp map_mul' := by intro s t; ext v; simp }`.

Take `⟨hfin, hint, -⟩` from `finiteAbelian_weightDecomposition F (Nat.card A) ζ hpos (IsUnit.mk0 _ hA) hζ T (fun t => Subtype.ext (by simp)) E ρ`. Establish `hW : (fun c : T →* Fˣ => ⨅ t, LinearMap.ker (ρ t - (c t : F) • LinearMap.id)) = Wt`. Use function extensionality and compare the values at `c`. Use extensionality with `v`. Rewrite using `[hWt, FiniteAbelianWeights.mem_weightSpace_iff]`.

Both sides reduce to the same expression. Rewrite `hint` using `[hW]`. Use `⟨hint.submodule_iSup_eq_top, ?_⟩` and prove the remaining obligations. Establish `hle : ∀ χ ψ, Module.finrank F (Wt χ) ≤ Module.finrank F (Wt ψ)`. Introduce `χ ψ`.

Take `⟨a, ha⟩` from `exists_comm_eq hm hc hn T (ψ * χ⁻¹)`. Establish `hmap : (Wt χ).map (Φ a : E →ₗ[F] E) ≤ Wt ψ`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite using `[hWt]`. Introduce `t`.

Take `⟨c, h⟩` from `hlam t`. Establish `h1` using `(hWt χ v).1 hv t`. Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[h, hc, smul_comm, ← map_smul, ← h, h1, map_smul, smul_smul, ha, ← Units.val_mul]`. Simplify using the standard rewrite rules.

Conclude with `(LinearEquiv.finrank_map_eq (Φ a) (Wt χ)).symm.le.trans (Submodule.finrank_mono hmap)`. Introduce `χ`. Use `haveI := Fintype.ofFinite (T →* Fˣ)`. Establish `h1 : Module.finrank F E = ∑ ψ, Module.finrank F (Wt ψ)`. Rewrite using `[← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Wt) hint).finrank_eq, Module.finrank_directSum]`.

Rewrite using `[h1, Finset.sum_congr rfl (fun ψ _ => le_antisymm (hle ψ χ) (hle χ ψ)), Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T F, smul_eq_mul, mul_comm]`.
-/
theorem heisenberg_weightSpace_finrank :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → (⨆ χ, Wt χ = ⊤) ∧ ∀ χ, Module.finrank F (Wt χ) * Nat.card T = Module.finrank F E := by
  intro F _ _ A _ _ E _ _ _ e Φ hA hdim hm hc hn T lam hlam Wt hWt
  classical
  have hpos : 0 < Nat.card A := Nat.card_pos
  haveI : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim
      omega
    · exact h
  haveI : NeZero ((Nat.card A : ℕ) : F) := ⟨hA⟩
  haveI : NeZero (Nat.card A) := ⟨hpos.ne'⟩
  haveI h0 : HasEnoughRootsOfUnity F (Nat.card A) := inferInstance
  haveI hAe : HasEnoughRootsOfUnity F (Monoid.exponent A) :=
    h0.of_dvd F Group.exponent_dvd_nat_card
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent T) :=
    hAe.of_dvd F (Monoid.exponent_submonoid_dvd T.toSubmonoid)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (Nat.card A)
  let ρ : Representation F T E :=
    { toFun := fun t => (lam t : E →ₗ[F] E)
      map_one' := by ext v; simp
      map_mul' := by intro s t; ext v; simp }
  obtain ⟨hfin, hint, -⟩ := finiteAbelian_weightDecomposition F (Nat.card A) ζ hpos
    (IsUnit.mk0 _ hA) hζ T (fun t => Subtype.ext (by simp)) E ρ
  have hW : (fun c : T →* Fˣ => ⨅ t, LinearMap.ker (ρ t - (c t : F) • LinearMap.id)) = Wt := by
    funext c
    ext v
    rw [hWt, FiniteAbelianWeights.mem_weightSpace_iff]
    rfl
  rw [hW] at hint
  refine ⟨hint.submodule_iSup_eq_top, ?_⟩
  have hle : ∀ χ ψ, Module.finrank F (Wt χ) ≤ Module.finrank F (Wt ψ) := by
    intro χ ψ
    obtain ⟨a, ha⟩ := exists_comm_eq hm hc hn T (ψ * χ⁻¹)
    have hmap : (Wt χ).map (Φ a : E →ₗ[F] E) ≤ Wt ψ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hWt]
      intro t
      obtain ⟨c, h⟩ := hlam t
      have h1 := (hWt χ v).1 hv t
      simp only [LinearEquiv.coe_coe]
      rw [h, hc, smul_comm, ← map_smul, ← h, h1, map_smul, smul_smul, ha, ← Units.val_mul]
      simp
    exact (LinearEquiv.finrank_map_eq (Φ a) (Wt χ)).symm.le.trans (Submodule.finrank_mono hmap)
  intro χ
  haveI := Fintype.ofFinite (T →* Fˣ)
  have h1 : Module.finrank F E = ∑ ψ, Module.finrank F (Wt ψ) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Wt) hint).finrank_eq,
      Module.finrank_directSum]
  rw [h1, Finset.sum_congr rfl (fun ψ _ => le_antisymm (hle ψ χ) (hle χ ψ)), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T F, smul_eq_mul, mul_comm]

end GlobalTheory
