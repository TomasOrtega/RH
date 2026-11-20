import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.ClopenIdealSheaf

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Use `Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)` and prove the remaining obligations. Rewrite using `[hcomm]`.

Conclude with `Ideal.mem_map_of_mem _ ha`. Introduce `s hs`. Take `⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩` from `(IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)`. Take `⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩` from `IsLocalization.surj (.powers f) s`. Simplify using `only at hxs hb`.

Establish `h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hb, map_mul]`. Use `_ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by`. Rewrite using `[hcomm, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]`. Take `⟨⟨_, m, rfl⟩, hm⟩` from `(IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1`. Simplify using `only at hm`. Rewrite using `[IsLocalization.mem_map_algebraMap_iff (.powers f)]`.

Use `⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Establish `e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n)`. Rewrite using `[map_mul, map_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.mem_comap, e, hm]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)`. Simplify using `only`. Rewrite using `[map_mul, pow_add, map_mul, ← hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_comap_localization {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
    rw [hcomm]
    exact Ideal.mem_map_of_mem _ ha
  · intro s hs
    obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (.powers f) s
    simp only at hxs hb
    have h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k) := by
      calc algebraMap A T (ρ b * ρ f ^ n)
          = τ (algebraMap R S b) * algebraMap A T (ρ f ^ n) := by rw [map_mul, hcomm]
        _ = τ s * τ (algebraMap R S (f ^ k)) * algebraMap A T (ρ f ^ n) := by
          rw [← hb, map_mul]
        _ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by
          rw [hcomm, map_pow]; ring
        _ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1
    simp only at hm
    rw [IsLocalization.mem_map_algebraMap_iff (.powers f)]
    refine ⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩
    · have e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n) := by
        rw [map_mul, map_pow, pow_add]; ring
      rw [Ideal.mem_comap, e, hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)
    · simp only
      rw [map_mul, pow_add, map_mul, ← hb]
      ring

/- English proof (translation)
Substitute `hB` using the available equality. Rewrite using `[← hI]`. Use `haveI := U.2.isLocalization_basicOpen f`. Use `haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)`. Use `map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _ (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _` and prove the remaining obligations.

Introduce `a`. Express the relevant statement in the definitionally equal form `(Z.presheaf.map (homOfLE hBD).op).hom ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) = (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom ((Z.presheaf.map (homOfLE hVU).op).hom a)`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem map_comap_eq {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by
  subst hB
  rw [← hI]
  haveI := U.2.isLocalization_basicOpen f
  haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)
  refine map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _
    (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _
  intro a
  change (Z.presheaf.map (homOfLE hBD).op).hom
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) =
    (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom
      ((Z.presheaf.map (homOfLE hVU).op).hom a)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

end GlobalTheory.ClopenIdealSheaf

namespace GlobalTheory.ClopenIdealSheaf

/- English proof (translation)
Introduce `Z W hW F hF`. Set `W' : Z.Opens` to `⟨W, hW.isOpen⟩`. Set `Wc : Z.Opens` to `⟨Wᶜ, hW.isClosed.isOpen_compl⟩`. Establish `hAff : ∀ U : Z.affineOpens, IsAffineOpen ((U : Z.Opens) ⊓ W')`. Introduce `U`.

Take `⟨e, -, he, -⟩` from `GlobalTheory.IsNormalScheme.exists_isIdempotentElem_basicOpen_eq (X := Z) (U := (U : Z.Opens)) (V := (U : Z.Opens) ⊓ W') (W := (U : Z.Opens) ⊓ Wc) (by`. Rewrite using `[← inf_sup_left]`. Establish `: W' ⊔ Wc = ⊤`. Use extensionality with `x`. Simplify using `[W', Wc, em]`.

Rewrite using `[this, inf_top_eq])`. Use the proof step `(by`. Use `Disjoint.mono inf_le_right inf_le_right ?_` and prove the remaining obligations. Rewrite using `[disjoint_iff]`. Use extensionality with `x`.

Simplify using `[W', Wc])`. Rewrite using `[← he]`. Conclude with `U.2.basicOpen e`. Set `V : Z.affineOpens → Z.affineOpens` to `fun U => ⟨(U : Z.Opens) ⊓ W', hAff U⟩`. Establish `hVU : ∀ U, (V U : Z.Opens) ≤ U` using `fun U => inf_le_left`.

Establish `hVW : ∀ U, ((V U : Z.Opens) : Set Z) ⊆ W` using `fun U => Set.inter_subset_right`. Set `I : ∀ U : Z.affineOpens, Ideal Γ(Z, U)` to `fun U => (F (V U)).comap (Z.presheaf.map (homOfLE (hVU U)).op).hom`. Use `⟨{ ideal := I, map_ideal_basicOpen := ?_ }, ?_, ?_⟩` and prove the remaining obligations. Introduce `U f`. Establish `hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = V (Z.affineBasicOpen f)`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Z.basicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = Z.basicOpen f ⊓ W'`. Rewrite using `[Scheme.basicOpen_res]`. Use `Z.basicOpen_le f` as an intermediate fact. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `le_inf inf_le_right (inf_le_left.trans inf_le_right)`. Conclude with `le_inf (le_inf (inf_le_left.trans this) inf_le_right) inf_le_left`. Conclude with `map_comap_eq F (hVU U) f hB (hVU _) (hF (V U) _ (hVW U))`. Introduce `U hU`. Establish `key : ∀ (A B : Z.affineOpens), A = B → ∀ hle : (B : Z.Opens) ≤ A, (F B).comap (Z.presheaf.map (homOfLE hle).op).hom = F A`.

Introduce and unpack `A B rfl hle`. Establish `: homOfLE hle = 𝟙 _` using `rfl`. Rewrite using `[this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]`. Conclude with `Ideal.comap_id _`. Conclude with `key U (V U) (Subtype.ext (inf_eq_left.mpr (show (U : Z.Opens) ≤ W' from hU)).symm) (hVU U)`.

Introduce `x hx`. Assume the negation of the conclusion as `hxW`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open hxW hW.isClosed.isOpen_compl`. Use `replace hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx`. Establish `hbot : ((V ⟨U, hU⟩ : Z.affineOpens) : Z.Opens) = ⊥`.

Use extensionality with `y`. Simplify using `only [V, W', TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk, Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun h => hUW h.1 h.2`. Use `haveI : Subsingleton Γ(Z, (V ⟨U, hU⟩ : Z.Opens)) := CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)`. Establish `htop : F (V ⟨U, hU⟩) = ⊤`.

Rewrite using `[Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Z, (V ⟨U, hU⟩ : Z.Opens))) 0]`. Conclude with `zero_mem _`. Establish `hI : I ⟨U, hU⟩ = ⊤`. Simplify using `only [I, htop, Ideal.comap_top]`. Express the relevant statement in the definitionally equal form `x ∈ Z.zeroLocus (U := U) (I ⟨U, hU⟩ : Set Γ(Z, U)) at hx`.

Rewrite `hx` using `[hI, Scheme.mem_zeroLocus_iff]`. Conclude with `hx 1 (Submodule.mem_top) (by rw [Scheme.basicOpen_one]; exact hxU)`.
-/
theorem exists_idealSheafData_of_isClopen : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W →
    ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  intro Z W hW F hF
  let W' : Z.Opens := ⟨W, hW.isOpen⟩
  let Wc : Z.Opens := ⟨Wᶜ, hW.isClosed.isOpen_compl⟩
  have hAff : ∀ U : Z.affineOpens, IsAffineOpen ((U : Z.Opens) ⊓ W') := by
    intro U
    obtain ⟨e, -, he, -⟩ := GlobalTheory.IsNormalScheme.exists_isIdempotentElem_basicOpen_eq (X := Z)
      (U := (U : Z.Opens)) (V := (U : Z.Opens) ⊓ W') (W := (U : Z.Opens) ⊓ Wc)
      (by
        rw [← inf_sup_left]
        have : W' ⊔ Wc = ⊤ := by
          ext x; simp [W', Wc, em]
        rw [this, inf_top_eq])
      (by
        refine Disjoint.mono inf_le_right inf_le_right ?_
        rw [disjoint_iff]; ext x; simp [W', Wc])
    rw [← he]; exact U.2.basicOpen e
  let V : Z.affineOpens → Z.affineOpens := fun U => ⟨(U : Z.Opens) ⊓ W', hAff U⟩
  have hVU : ∀ U, (V U : Z.Opens) ≤ U := fun U => inf_le_left
  have hVW : ∀ U, ((V U : Z.Opens) : Set Z) ⊆ W := fun U => Set.inter_subset_right
  let I : ∀ U : Z.affineOpens, Ideal Γ(Z, U) := fun U =>
    (F (V U)).comap (Z.presheaf.map (homOfLE (hVU U)).op).hom
  refine ⟨{ ideal := I, map_ideal_basicOpen := ?_ }, ?_, ?_⟩
  · intro U f
    have hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) =
        V (Z.affineBasicOpen f) := by
      apply Subtype.ext
      change Z.basicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = Z.basicOpen f ⊓ W'
      rw [Scheme.basicOpen_res]
      have := Z.basicOpen_le f
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
      · exact le_inf (le_inf (inf_le_left.trans this) inf_le_right) inf_le_left
    exact map_comap_eq F (hVU U) f hB (hVU _) (hF (V U) _ (hVW U))
  · intro U hU
    have key : ∀ (A B : Z.affineOpens), A = B → ∀ hle : (B : Z.Opens) ≤ A,
        (F B).comap (Z.presheaf.map (homOfLE hle).op).hom = F A := by
      rintro A B rfl hle
      have : homOfLE hle = 𝟙 _ := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]
      exact Ideal.comap_id _
    exact key U (V U) (Subtype.ext (inf_eq_left.mpr (show (U : Z.Opens) ≤ W' from hU)).symm) (hVU U)
  · intro x hx
    by_contra hxW
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open hxW hW.isClosed.isOpen_compl
    replace hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    have hbot : ((V ⟨U, hU⟩ : Z.affineOpens) : Z.Opens) = ⊥ := by
      ext y
      simp only [V, W', TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk,
        Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun h => hUW h.1 h.2
    haveI : Subsingleton Γ(Z, (V ⟨U, hU⟩ : Z.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    have htop : F (V ⟨U, hU⟩) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Z, (V ⟨U, hU⟩ : Z.Opens))) 0]
      exact zero_mem _
    have hI : I ⟨U, hU⟩ = ⊤ := by
      simp only [I, htop, Ideal.comap_top]
    change x ∈ Z.zeroLocus (U := U) (I ⟨U, hU⟩ : Set Γ(Z, U)) at hx
    rw [hI, Scheme.mem_zeroLocus_iff] at hx
    exact hx 1 (Submodule.mem_top) (by rw [Scheme.basicOpen_one]; exact hxU)

end GlobalTheory.ClopenIdealSheaf
