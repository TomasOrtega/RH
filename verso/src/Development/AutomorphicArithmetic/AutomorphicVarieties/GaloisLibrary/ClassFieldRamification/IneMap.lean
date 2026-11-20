import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `k K H _ _ _ _ _ _ _ _ _ _ _ _ w`. Use `haveI : IsGalois K H := IsGalois.tower_top_of_isGalois k K H`. Establish `comm : ∀ (σ : Gal(H/k)) (x : 𝓞 K), algebraMap (𝓞 K) (𝓞 H) (resTo k K H σ • x) = σ • algebraMap (𝓞 K) (𝓞 H) x`. Introduce `σ x`. Apply `FaithfulSMul.algebraMap_injective (𝓞 H) H` to reduce the goal to its premises.

Establish `e1 : algebraMap (𝓞 H) H (σ • algebraMap (𝓞 K) (𝓞 H) x) = σ • algebraMap (𝓞 H) H (algebraMap (𝓞 K) (𝓞 H) x)` using `algebraMap.smul' _ _ _`. Establish `e2 : algebraMap (𝓞 K) K (resTo k K H σ • x) = resTo k K H σ • algebraMap (𝓞 K) K x` using `algebraMap.smul' _ _ _`. Rewrite using `[e1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K H, IsScalarTower.algebraMap_apply (𝓞 K) K H, e2]`. Conclude with `AlgEquiv.restrictNormal_commutes σ K _`. Establish `comm2 : ∀ (τ : Gal(H/K)) (y : 𝓞 H), (τ.restrictScalars k) • y = τ • y`.

Introduce `τ y`. Apply `FaithfulSMul.algebraMap_injective (𝓞 H) H` to reduce the goal to its premises. Establish `e1 : algebraMap (𝓞 H) H ((τ.restrictScalars k) • y) = (τ.restrictScalars k) • algebraMap (𝓞 H) H y` using `algebraMap.smul' _ _ _`. Establish `e2 : algebraMap (𝓞 H) H (τ • y) = τ • algebraMap (𝓞 H) H y` using `algebraMap.smul' _ _ _`. Rewrite using `[e1, e2]`.

Both sides reduce to the same expression. Use `set P := w.asIdeal with hP`. Use `set Q := P.under (𝓞 K) with hQ`. Use `set p := P.under (𝓞 k) with hp`. Use `haveI : Nonempty (Q.primesOver (𝓞 H)) := ⟨⟨P, inferInstance, inferInstance⟩⟩`.

Establish `hle : (P.inertia Gal(H/k)).map (resTo k K H) ≤ Q.inertia Gal(K/k)`. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Introduce `x`. Establish `h1` using `hσ (algebraMap (𝓞 K) (𝓞 H) x)`. Use `show _ ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) P`.

Rewrite using `[Ideal.mem_comap, map_sub, comm]`. Conclude with `h1`. Apply `Subgroup.eq_of_le_of_card_ge hle` to reduce the goal to its premises. Establish `cG : Nat.card (P.inertia Gal(H/k)) = p.ramificationIdxIn (𝓞 H)` using `Ideal.card_inertia_eq_ramificationIdxIn p P`. Establish `cK : Nat.card (Q.inertia Gal(K/k)) = p.ramificationIdxIn (𝓞 K)` using `Ideal.card_inertia_eq_ramificationIdxIn p Q`.

Establish `cH : Nat.card (P.inertia Gal(H/K)) = Q.ramificationIdxIn (𝓞 H)` using `Ideal.card_inertia_eq_ramificationIdxIn Q P`. Establish `hmul : p.ramificationIdxIn (𝓞 K) * Q.ramificationIdxIn (𝓞 H) = p.ramificationIdxIn (𝓞 H)` using `Ideal.ramificationIdxIn_mul_ramificationIdxIn Q Gal(K/k) (𝓞 H) Gal(H/k) Gal(H/K)`. Set `f : (P.inertia Gal(H/k)) →* Gal(K/k)` to `(resTo k K H).comp (Subgroup.subtype _)`. Establish `hrange : f.range = (P.inertia Gal(H/k)).map (resTo k K H)`. Rewrite using `[MonoidHom.range_comp, Subgroup.range_subtype]`.

Set `g : (P.inertia Gal(H/K)) →* (P.inertia Gal(H/k))` to `{ toFun := fun τ => ⟨(τ.1.restrictScalars k), fun y => by`. Rewrite using `[comm2]`. Conclude with `τ.2 y⟩`. Use the proof step `map_one' := rfl`. Use the proof step `map_mul' := fun _ _ => rfl }`.

Establish `hker : f.ker ≤ g.range`. Introduce `σ hσ`. Establish `hfix : ∀ c : K, σ.1 (algebraMap K H c) = algebraMap K H c`. Introduce `c`. Establish `h2 : resTo k K H σ.1 = 1` using `hσ`.

Rewrite using `[← AlgEquiv.restrictNormal_commutes σ.1 K c]`. Establish `h3 : σ.1.restrictNormal K = 1` using `h2`. Rewrite using `[h3]`. Both sides reduce to the same expression. Set `τ : Gal(H/K)` to `AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) hfix`.

Establish `hτ : τ ∈ P.inertia Gal(H/K)`. Introduce `y`. Establish `h4` using `σ.2 y`. Rewrite `*` using `[← comm2]`. Conclude with `h4`.

Conclude with `⟨⟨τ, hτ⟩, by`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `z`. Use the proof step `rfl⟩`. Establish `hcardker : Nat.card f.ker ≤ Nat.card (P.inertia Gal(H/K))` using `(Subgroup.card_le_of_le hker).trans (Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective)`.

Establish `hpos : 0 < Nat.card f.ker` using `Nat.card_pos`. Establish `key` using `f.ker.card_mul_index`. Rewrite `key` using `[Subgroup.index_ker, hrange, cG, ← hmul]`. Rewrite using `[cK]`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `hQpos : 0 < Q.ramificationIdxIn (𝓞 H)`. Rewrite using `[← cH]`. Conclude with `Nat.card_pos`. Rewrite `hcardker` using `[cH]`.

Use polynomial arithmetic with `[Nat.mul_le_mul hcardker (le_of_lt hlt)]`.
-/
theorem UpperTheory.V.CF.ineMap :
    ∀ (k K H : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field H] [NumberField H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H] [IsGalois k K] [IsGalois k H] (w : HeightOneSpectrum (𝓞 H)), (w.asIdeal.inertia Gal(H/k)).map (resTo k K H) = (w.asIdeal.under (𝓞 K)).inertia Gal(K/k) := by
  intro k K H _ _ _ _ _ _ _ _ _ _ _ _ w
  haveI : IsGalois K H := IsGalois.tower_top_of_isGalois k K H
  have comm : ∀ (σ : Gal(H/k)) (x : 𝓞 K),
      algebraMap (𝓞 K) (𝓞 H) (resTo k K H σ • x) = σ • algebraMap (𝓞 K) (𝓞 H) x := by
    intro σ x
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H (σ • algebraMap (𝓞 K) (𝓞 H) x) =
        σ • algebraMap (𝓞 H) H (algebraMap (𝓞 K) (𝓞 H) x) := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 K) K (resTo k K H σ • x) = resTo k K H σ • algebraMap (𝓞 K) K x :=
      algebraMap.smul' _ _ _
    rw [e1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K H, IsScalarTower.algebraMap_apply (𝓞 K) K H, e2]
    exact AlgEquiv.restrictNormal_commutes σ K _
  have comm2 : ∀ (τ : Gal(H/K)) (y : 𝓞 H), (τ.restrictScalars k) • y = τ • y := by
    intro τ y
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H ((τ.restrictScalars k) • y) =
        (τ.restrictScalars k) • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 H) H (τ • y) = τ • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    rw [e1, e2]
    rfl
  set P := w.asIdeal with hP
  set Q := P.under (𝓞 K) with hQ
  set p := P.under (𝓞 k) with hp
  haveI : Nonempty (Q.primesOver (𝓞 H)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have hle : (P.inertia Gal(H/k)).map (resTo k K H) ≤ Q.inertia Gal(K/k) := by
    rintro _ ⟨σ, hσ, rfl⟩
    intro x
    have h1 := hσ (algebraMap (𝓞 K) (𝓞 H) x)
    show _ ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) P
    rw [Ideal.mem_comap, map_sub, comm]
    exact h1
  apply Subgroup.eq_of_le_of_card_ge hle
  have cG : Nat.card (P.inertia Gal(H/k)) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn p P
  have cK : Nat.card (Q.inertia Gal(K/k)) = p.ramificationIdxIn (𝓞 K) :=
    Ideal.card_inertia_eq_ramificationIdxIn p Q
  have cH : Nat.card (P.inertia Gal(H/K)) = Q.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn Q P
  have hmul : p.ramificationIdxIn (𝓞 K) * Q.ramificationIdxIn (𝓞 H) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn Q Gal(K/k) (𝓞 H) Gal(H/k) Gal(H/K)
  let f : (P.inertia Gal(H/k)) →* Gal(K/k) := (resTo k K H).comp (Subgroup.subtype _)
  have hrange : f.range = (P.inertia Gal(H/k)).map (resTo k K H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let g : (P.inertia Gal(H/K)) →* (P.inertia Gal(H/k)) :=
    { toFun := fun τ => ⟨(τ.1.restrictScalars k), fun y => by
        rw [comm2]
        exact τ.2 y⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : f.ker ≤ g.range := by
    intro σ hσ
    have hfix : ∀ c : K, σ.1 (algebraMap K H c) = algebraMap K H c := by
      intro c
      have h2 : resTo k K H σ.1 = 1 := hσ
      rw [← AlgEquiv.restrictNormal_commutes σ.1 K c]
      have h3 : σ.1.restrictNormal K = 1 := h2
      rw [h3]
      rfl
    let τ : Gal(H/K) := AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) hfix
    have hτ : τ ∈ P.inertia Gal(H/K) := by
      intro y
      have h4 := σ.2 y
      rw [← comm2] at *
      exact h4
    exact ⟨⟨τ, hτ⟩, by
      apply Subtype.ext
      ext z
      rfl⟩
  have hcardker : Nat.card f.ker ≤ Nat.card (P.inertia Gal(H/K)) :=
    (Subgroup.card_le_of_le hker).trans
      (Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have key := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, cG, ← hmul] at key
  rw [cK]
  by_contra hlt
  push_neg at hlt
  have hQpos : 0 < Q.ramificationIdxIn (𝓞 H) := by
    rw [← cH]
    exact Nat.card_pos
  rw [cH] at hcardker
  nlinarith [Nat.mul_le_mul hcardker (le_of_lt hlt)]
