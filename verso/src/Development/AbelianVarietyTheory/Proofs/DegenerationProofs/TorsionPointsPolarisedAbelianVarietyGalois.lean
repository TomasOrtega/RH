import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValuesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionGalois

/- English proof (translation)
Establish `hp : ∀ (g : Monoid.End M) (x : M), g x = x → ∀ k : ℕ, (g ^ k) x = x`. Introduce `g x hx k`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ]`.

Use `show (g ^ k) (g x) = x`. Rewrite using `[hx, ih]`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`. Rewrite `hx` using `[pow_zero, pow_one]`.

Rewrite using `[hx, map_one]`. Consider the case `succ n ih`. Introduce `x hx`. Use `set g := f ^ l ^ n with hg`. Establish `h1 : g (x ^ l) = x ^ l` using `ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)`.

Establish `hd : (g x * x⁻¹) ^ l = 1` using `by rw [mul_pow, ← map_pow, h1, inv_pow, mul_inv_cancel]`. Establish `hgd : g (g x * x⁻¹) = g x * x⁻¹` using `hp f _ (h _ hd) _`. Establish `hk : ∀ k : ℕ, (g ^ k) x = x * (g x * x⁻¹) ^ k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ihk`. Rewrite using `[pow_succ']`. Use `show g ((g ^ k) x) = _`. Rewrite using `[ihk, map_mul, map_pow, hgd, pow_succ', ← _root_.mul_assoc, mul_comm (g x) x⁻¹, mul_inv_cancel_left]`.

Rewrite using `[pow_succ, pow_mul, ← hg, hk, hd, _root_.mul_one]`.
-/
theorem pow_fix {M : Type} [CommGroup M] (l : ℕ) (f : Monoid.End M) (h : ∀ x : M, x ^ l = 1 → f x = x) (n : ℕ) :
    ∀ x : M, x ^ l ^ n = 1 → (f ^ l ^ n) x = x := by
  have hp : ∀ (g : Monoid.End M) (x : M), g x = x → ∀ k : ℕ, (g ^ k) x = x := by
    intro g x hx k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ]; show (g ^ k) (g x) = x; rw [hx, ih]
  induction n with
  | zero => intro x hx; rw [pow_zero, pow_one] at hx; rw [hx, map_one]
  | succ n ih =>
    intro x hx
    set g := f ^ l ^ n with hg
    have h1 : g (x ^ l) = x ^ l := ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)
    have hd : (g x * x⁻¹) ^ l = 1 := by rw [mul_pow, ← map_pow, h1, inv_pow, mul_inv_cancel]
    have hgd : g (g x * x⁻¹) = g x * x⁻¹ := hp f _ (h _ hd) _
    have hk : ∀ k : ℕ, (g ^ k) x = x * (g x * x⁻¹) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ']
        show g ((g ^ k) x) = _
        rw [ihk, map_mul, map_pow, hgd, pow_succ', ← _root_.mul_assoc, mul_comm (g x) x⁻¹, mul_inv_cancel_left]
    rw [pow_succ, pow_mul, ← hg, hk, hd, _root_.mul_one]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

noncomputable def tw (τ : Ω ≃ₐ[K] Ω) : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    show spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K Ω) = spMap (algebraMap K Ω)
    rw [← spMap_comp']
    congr 1
    ext c
    exact τ.commutes c)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show spMap (RingHom.id Ω) = 𝟙 _`. Conclude with `Spec.map_id _`.
-/
theorem tw_one : tw (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap (RingHom.id Ω) = 𝟙 _
  exact Spec.map_id _

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `spMap_comp' σ.toRingEquiv.toRingHom τ.toRingEquiv.toRingHom`.
-/
theorem tw_mul (τ σ : Ω ≃ₐ[K] Ω) : tw (τ * σ) = tw τ ≫ tw σ := by
  apply Over.OverMorphism.ext
  exact spMap_comp' σ.toRingEquiv.toRingHom τ.toRingEquiv.toRingHom

/- English proof (translation)
Use `P.isAb.comm` as an intermediate fact. Set `f : Monoid.End (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)` to `MonoidHom.mk' (fun x => tw τ ≫ x) (fun a b => MonObj.comp_mul _ _ _)`. Establish `hf : ∀ (k : ℕ) x, (f ^ k) x = tw (τ ^ k) ≫ x`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro x`. Rewrite using `[pow_zero, pow_zero, tw_one, Category.id_comp]`. Both sides reduce to the same expression. Consider the case `succ k ih`. Introduce `x`.

Rewrite using `[pow_succ, pow_succ, tw_mul, Category.assoc, ← ih]`. Both sides reduce to the same expression. Rewrite using `[← hf]`. Conclude with `pow_fix l f h n x hx`.
-/
theorem tw_pow_fix (P : Out.PolAV (Sp K)) (l : ℕ) (τ : Ω ≃ₐ[K] Ω)
    (h : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 → tw τ ≫ x = x) (n : ℕ)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) (hx : x ^ l ^ n = 1) : tw (τ ^ l ^ n) ≫ x = x := by
  have := P.isAb.comm
  let f : Monoid.End (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) :=
    MonoidHom.mk' (fun x => tw τ ≫ x) (fun a b => MonObj.comp_mul _ _ _)
  have hf : ∀ (k : ℕ) x, (f ^ k) x = tw (τ ^ k) ≫ x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero, tw_one, Category.id_comp]; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, tw_mul, Category.assoc, ← ih]; rfl
  rw [← hf]
  exact pow_fix l f h n x hx

/- English proof (translation)
Establish `hpr` using `P.isAb.proper`. Establish `key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1}, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ (∀ τ : Ω ≃ₐ[K] Ω, τ ∈ L.fixingSubgroup ↔ tw τ ≫ x.1 = x.1) ∧ ∀ L' : IntermediateField K Ω, L ≤ L' → ∃ y : Sp L' ⟶ P.A.left, spMap (algebraMap L' Ω) ≫ …`. Introduce `x`. Take `⟨E, h1, h2, h3⟩` from `GlobalTheory.T.exists_field_of_definition_of_point P.A.left Ω x.1.left`. Take `⟨L, hL, rfl⟩` from `h3 K P.A.hom inferInstance (Over.w x.1) inferInstance`.

Use `⟨L, hL, fun τ => ?_, fun L' hL' => (h2 L' (algebraMap L' Ω)).1 fun c hc => ⟨⟨c, hL' hc⟩, rfl⟩⟩` and prove the remaining obligations. Establish `e : spMap (RingHom.id Ω) ≫ x.1.left = x.1.left`. Establish `e₀ : spMap (RingHom.id Ω) = 𝟙 _` using `Spec.map_id _`. Rewrite using `[e₀]`. Conclude with `Category.id_comp _`.

Use `h1 τ.toRingEquiv.toRingHom (RingHom.id Ω)` as an intermediate fact. Rewrite `this` using `[e]`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Conclude with `⟨fun hh => Over.OverMorphism.ext (this.2 hh), fun hh => this.1 (congrArg CommaMorphism.left hh)⟩`. Use `choose F hF1 hF2 hF3 using key`.

Establish `hmem : ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ (⨆ x, F x).fixingSubgroup ↔ ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l ^ n = 1 → tw τ ≫ x = x`. Introduce `τ`. Rewrite using `[← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]`. Simplify using `only [IntermediateField.le_iff_le, Subgroup.zpowers_le, hF2]`. Conclude with `⟨fun hh x hx => hh ⟨x, hx⟩, fun hh x => hh x.1 x.2⟩`.

Establish `hn : (⨆ x, F x).fixingSubgroup.Normal` using `⟨fun τ hτ σ => by`. Rewrite `hτ`, the goal using `[hmem]`. Introduce `x hx`. Establish `hx' : (tw σ⁻¹ ≫ x) ^ l ^ n = 1` using `by rw [← MonObj.comp_pow, hx, MonObj.comp_one]`. Rewrite using `[tw_mul, tw_mul, Category.assoc, Category.assoc, hτ _ hx', ← Category.assoc, ← tw_mul, mul_inv_cancel, tw_one, Category.id_comp]⟩`.

Establish `hg : IsGalois K (⨆ x, F x : IntermediateField K Ω)` using `(InfiniteGalois.normal_iff_isGalois _).1 hn`. Use `⟨⨆ x, F x, IntermediateField.finiteDimensional_iSup_of_finite, hg.to_normal, fun g => ?_, fun x hx => hF3 ⟨x, hx⟩ _ (le_iSup F _)⟩` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := (⨆ x, F x : IntermediateField K Ω)) Ω g`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hmem]`.

Conclude with `tw_pow_fix P l τ (h τ) n`.
-/
theorem exists_field [CharZero K] [IsAlgClosure K Ω] (P : Out.PolAV (Sp K)) (l n : ℕ)
    (hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1})
    (h : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 → tw τ ≫ x = x) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧
      ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 →
        ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left := by
  have hpr := P.isAb.proper
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1},
      ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
        (∀ τ : Ω ≃ₐ[K] Ω, τ ∈ L.fixingSubgroup ↔ tw τ ≫ x.1 = x.1) ∧
        ∀ L' : IntermediateField K Ω, L ≤ L' → ∃ y : Sp L' ⟶ P.A.left, spMap (algebraMap L' Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, h1, h2, h3⟩ := GlobalTheory.T.exists_field_of_definition_of_point P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    refine ⟨L, hL, fun τ => ?_, fun L' hL' => (h2 L' (algebraMap L' Ω)).1 fun c hc => ⟨⟨c, hL' hc⟩, rfl⟩⟩
    have e : spMap (RingHom.id Ω) ≫ x.1.left = x.1.left := by
      have e₀ : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
      rw [e₀]; exact Category.id_comp _
    have := h1 τ.toRingEquiv.toRingHom (RingHom.id Ω)
    rw [e] at this
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun hh => Over.OverMorphism.ext (this.2 hh), fun hh => this.1 (congrArg CommaMorphism.left hh)⟩
  choose F hF1 hF2 hF3 using key
  have hmem : ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ (⨆ x, F x).fixingSubgroup ↔
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l ^ n = 1 → tw τ ≫ x = x := by
    intro τ
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
    simp only [IntermediateField.le_iff_le, Subgroup.zpowers_le, hF2]
    exact ⟨fun hh x hx => hh ⟨x, hx⟩, fun hh x => hh x.1 x.2⟩
  have hn : (⨆ x, F x).fixingSubgroup.Normal := ⟨fun τ hτ σ => by
    rw [hmem] at hτ ⊢
    intro x hx
    have hx' : (tw σ⁻¹ ≫ x) ^ l ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    rw [tw_mul, tw_mul, Category.assoc, Category.assoc, hτ _ hx', ← Category.assoc, ← tw_mul, mul_inv_cancel,
      tw_one, Category.id_comp]⟩
  have hg : IsGalois K (⨆ x, F x : IntermediateField K Ω) := (InfiniteGalois.normal_iff_isGalois _).1 hn
  refine ⟨⨆ x, F x, IntermediateField.finiteDimensional_iSup_of_finite, hg.to_normal, fun g => ?_,
    fun x hx => hF3 ⟨x, hx⟩ _ (le_iSup F _)⟩
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := (⨆ x, F x : IntermediateField K Ω)) Ω g
  refine ⟨n, ?_⟩
  rw [← map_pow, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hmem]
  exact tw_pow_fix P l τ (h τ) n

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (x y : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), ∃ v : Ωˣ, x ^ k = 1 → y ^ k = 1 → ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ v = u`. Introduce `k x y`. Distinguish the cases in `hh : x ^ k = 1 ∧ y ^ k = 1`. Take `⟨c, hc, hu⟩` from `(hL.weil _ P k _).1 x y hh.1 hh.2`. Set `E` to `Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv`.

Use `⟨E c, fun _ _ u => ⟨fun H => ?_, fun H => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hu _ H]`. Conclude with `E.apply_symm_apply u`. Substitute `H` using the available equality. Establish `: Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (E c) = c` using `E.symm_apply_apply c`.

Rewrite using `[this]`. Conclude with `hc`. Conclude with `⟨1, fun a b => (hh ⟨a, b⟩).elim⟩`. Use `choose e he using key`. Conclude with `⟨e, he⟩`.
-/
theorem exists_pairing (hL : Out.Laws) (P : Out.PolAV (Sp K)) :
    ∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ,
      ∀ (k : ℕ) x y, x ^ k = 1 → y ^ k = 1 → ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ e k x y = u := by
  classical
  have key : ∀ (k : ℕ) (x y : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), ∃ v : Ωˣ, x ^ k = 1 → y ^ k = 1 →
      ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ v = u := by
    intro k x y
    by_cases hh : x ^ k = 1 ∧ y ^ k = 1
    · obtain ⟨c, hc, hu⟩ := (hL.weil _ P k _).1 x y hh.1 hh.2
      let E := Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv
      refine ⟨E c, fun _ _ u => ⟨fun H => ?_, fun H => ?_⟩⟩
      · rw [← hu _ H]
        exact E.apply_symm_apply u
      · subst H
        have : Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (E c) = c :=
          E.symm_apply_apply c
        rw [this]; exact hc
    · exact ⟨1, fun a b => (hh ⟨a, b⟩).elim⟩
  choose e he using key
  exact ⟨e, he⟩

end GlobalTheory.TorsionGalois

open GlobalTheory.TorsionGalois in

/- English proof (translation)
Introduce `K _ _ P Ω _ _ _ l hl`. Establish `hL` using `GlobalTheory.T.abelianScheme_laws_unconditional.1`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective`. Establish `hne : ∀ n, ((l ^ n : ℕ) : Ω) ≠ 0` using `fun n => Nat.cast_ne_zero.2 (pow_ne_zero n hl.ne_zero)`.

Establish `hcard : ∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))` using `fun n => by`. Rewrite using `[pow_mul]`. Conclude with `(hL.mulN _ P (l ^ n) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero n hl.ne_zero))).2.2.2.2 Ω _ (hne n)`. Use `⟨hcard, ?_, fun h n => exists_field P l n (Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)) fun τ x hx => Over.OverMorphism.ext (h τ x hx)⟩` and prove the remaining obligations. Use `P.isAb.comm` as an intermediate fact.

Take `⟨e, he⟩` from `exists_pairing (Ω := Ω) hL P`. Establish `hmul : ∀ (k : ℕ) x x' y, x ^ k = 1 → x' ^ k = 1 → y ^ k = 1 → e k (x * x') y = e k x y * e k x' y`. Introduce `k x x' y hx hx' hy`. Rewrite using `[← he k _ _ (by rw [mul_pow, hx, hx', _root_.mul_one]) hy, map_mul]`. Conclude with `(hL.weil _ P k _).2.1 x x' y _ _ ((he k _ _ hx hy _).2 rfl) ((he k _ _ hx' hy _).2 rfl)`.

Use `⟨fun n => e (l ^ n), ⟨fun n x x' y hx hx' hy => ⟨hmul _ _ _ _ hx hx' hy, ?_⟩, fun n x y hx hy => ?_, fun n x hx h => ?_⟩, fun τ n x y x' y' hx hy hx' hy' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← he _ _ _ hy hx, map_inv]`. Conclude with `GlobalTheory.CommPairing.weilIs_symm P.isLB ((he _ _ _ hx hy _).2 rfl)`. Establish `hxl : (x ^ l) ^ l ^ n = 1` using `by rw [← pow_mul, ← pow_succ']; exact hx`. Establish `hu : IsUnit ((l ^ n * l : ℕ) : Γ((Over.mk (spMap (algebraMap K Ω))).left, ⊤))`.

Use `(IsUnit.mk0 _ (hne (n + 1))).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast, pow_succ]`. Conclude with `this`. Establish `H` using `((hL.weil _ P (l ^ n) _).2.2.2 l x y _ hu (by rw [← pow_succ]; exact hx) hy).2 ((he _ _ _ hxl hy _).2 rfl)`. Rewrite `H` using `[← Nat.cast_mul, ← pow_succ]`.

Conclude with `(he _ _ _ hx (by rw [pow_succ, pow_mul, hy, one_pow]) _).1 H`. Use `GlobalTheory.ThetaRep.eq_one_of_weilIs hL P _ (hne n) x hx fun y hy => ?_` and prove the remaining obligations. Establish `H` using `(he _ _ _ hx hy _).2 (h y hy)`. Rewrite `H` using `[map_one]`. Then use the resulting hypothesis. Establish `h1 : e (l ^ n) 1 y = 1`.

Use `hmul (l ^ n) 1 1 y (one_pow _) (one_pow _) hy` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_mul.1 this`. Establish `hp : ∀ m : ℕ, e (l ^ n) (x ^ m) y = e (l ^ n) x y ^ m`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero x, pow_zero, h1]`. Consider the case `succ m ih`. Rewrite using `[pow_succ x, hmul _ _ _ _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) hx hy, ih, pow_succ]`. Use `show (e (l ^ n) x y : Ω) ^ l ^ n = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, ← hp, hx, h1, Units.val_one]`. Take `rfl : x' = tw τ ≫ x` from `Over.OverMorphism.ext hx'`. Take `rfl : y' = tw τ ≫ y` from `Over.OverMorphism.ext hy'`. Establish `H` using `GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (tw τ) ((he _ _ _ hx hy _).2 rfl)`. Establish `E : Units.map (tw τ).left.appTop.hom.toMonoidHom (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (e (l ^ n) x y)) = Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (Units.map τ.toRingEquiv.toRingHom.toMonoidHom (e (l ^ n) x y))` using `Units.ext (congrArg (fun q => q.hom (e (l ^ n) x y).val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ.toRingEquiv.toRingHom))).symm`.

Rewrite `H` using `[E]`. Conclude with `congrArg Units.val ((he _ _ _ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) _).1 H)`.
-/
theorem GlobalTheory.torsion_points_galois_module : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ), l.Prime → (∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))) ∧ (∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ ∀ (τ : Ω ≃ₐ[K] Ω) n (x y x' y' : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l ^ n = 1 → y ^ l ^ n = 1 → x'.left = spMap τ.toRingEquiv.toRingHom ≫ x.left → y'.left = spMap τ.toRingEquiv.toRingHom ≫ y.left → (e n x y : Ω) ^ l ^ n = 1 ∧ (e n x' y' : Ω) = τ (e n x y)) ∧ ((∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ n, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧ ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 → ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left) := by
  intro K _ _ P Ω _ _ _ l hl
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hne : ∀ n, ((l ^ n : ℕ) : Ω) ≠ 0 := fun n => Nat.cast_ne_zero.2 (pow_ne_zero n hl.ne_zero)
  have hcard : ∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} =
      l ^ (n * (2 * P.g)) := fun n => by
    rw [pow_mul]
    exact (hL.mulN _ P (l ^ n) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero n hl.ne_zero))).2.2.2.2 Ω _ (hne n)
  refine ⟨hcard, ?_, fun h n => exists_field P l n
    (Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero))
    fun τ x hx => Over.OverMorphism.ext (h τ x hx)⟩
  have := P.isAb.comm
  obtain ⟨e, he⟩ := exists_pairing (Ω := Ω) hL P
  have hmul : ∀ (k : ℕ) x x' y, x ^ k = 1 → x' ^ k = 1 → y ^ k = 1 → e k (x * x') y = e k x y * e k x' y := by
    intro k x x' y hx hx' hy
    rw [← he k _ _ (by rw [mul_pow, hx, hx', _root_.mul_one]) hy, map_mul]
    exact (hL.weil _ P k _).2.1 x x' y _ _ ((he k _ _ hx hy _).2 rfl) ((he k _ _ hx' hy _).2 rfl)
  refine ⟨fun n => e (l ^ n), ⟨fun n x x' y hx hx' hy => ⟨hmul _ _ _ _ hx hx' hy, ?_⟩, fun n x y hx hy => ?_,
    fun n x hx h => ?_⟩, fun τ n x y x' y' hx hy hx' hy' => ⟨?_, ?_⟩⟩
  · rw [← he _ _ _ hy hx, map_inv]
    exact GlobalTheory.CommPairing.weilIs_symm P.isLB ((he _ _ _ hx hy _).2 rfl)
  · have hxl : (x ^ l) ^ l ^ n = 1 := by rw [← pow_mul, ← pow_succ']; exact hx
    have hu : IsUnit ((l ^ n * l : ℕ) : Γ((Over.mk (spMap (algebraMap K Ω))).left, ⊤)) := by
      have := (IsUnit.mk0 _ (hne (n + 1))).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
      rw [map_natCast, pow_succ] at this
      exact this
    have H := ((hL.weil _ P (l ^ n) _).2.2.2 l x y _ hu (by rw [← pow_succ]; exact hx) hy).2
      ((he _ _ _ hxl hy _).2 rfl)
    rw [← Nat.cast_mul, ← pow_succ] at H
    exact (he _ _ _ hx (by rw [pow_succ, pow_mul, hy, one_pow]) _).1 H
  · refine GlobalTheory.ThetaRep.eq_one_of_weilIs hL P _ (hne n) x hx fun y hy => ?_
    have H := (he _ _ _ hx hy _).2 (h y hy)
    rwa [map_one] at H
  · have h1 : e (l ^ n) 1 y = 1 := by
      have := hmul (l ^ n) 1 1 y (one_pow _) (one_pow _) hy
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have hp : ∀ m : ℕ, e (l ^ n) (x ^ m) y = e (l ^ n) x y ^ m := by
      intro m
      induction m with
      | zero => rw [pow_zero x, pow_zero, h1]
      | succ m ih =>
        rw [pow_succ x, hmul _ _ _ _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) hx hy, ih, pow_succ]
    show (e (l ^ n) x y : Ω) ^ l ^ n = 1
    rw [← Units.val_pow_eq_pow_val, ← hp, hx, h1, Units.val_one]
  · obtain rfl : x' = tw τ ≫ x := Over.OverMorphism.ext hx'
    obtain rfl : y' = tw τ ≫ y := Over.OverMorphism.ext hy'
    have H := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (tw τ) ((he _ _ _ hx hy _).2 rfl)
    have E : Units.map (tw τ).left.appTop.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (e (l ^ n) x y)) =
        Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
          (Units.map τ.toRingEquiv.toRingHom.toMonoidHom (e (l ^ n) x y)) :=
      Units.ext (congrArg (fun q => q.hom (e (l ^ n) x y).val)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ.toRingEquiv.toRingHom))).symm
    rw [E] at H
    exact congrArg Units.val ((he _ _ _ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) _).1 H)
