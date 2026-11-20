import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharmatrixBlockDiagonal
open WittVector Ideal Matrix GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.IotaDet

/- English proof (translation)
Establish `e : w = (w - v) + v` using `by simp`. Rewrite using `[e, f.map_add_univ, Finset.sum_eq_single ∅]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Take `⟨k, hk⟩` from `Finset.nonempty_iff_ne_empty.2 hs`.

Distinguish the cases in `hkS : k ∈ S`. Conclude with `f.map_coord_zero k (by simp [Finset.piecewise, hk, h1 k hkS])`. Apply `f.map_linearDependent` to reduce the goal to its premises. Introduce `hli`. Establish `hm : ∀ i : ↥(insert k S), s.piecewise (w - v) v i ∈ U`.

Introduce and unpack `⟨i, hi⟩`. Distinguish the cases in `his : i ∈ s`. Simplify `h3 i` using `[Finset.piecewise, his]`. Establish `: i ∈ S` using `(Finset.mem_insert.1 hi).resolve_left (fun e => his (e ▸ hk))`. Simplify `h2 i this` using `[Finset.piecewise, his]`.

Establish `hli' : LinearIndependent C (fun i : ↥(insert k S) => (⟨_, hm i⟩ : U))` using `LinearIndependent.of_comp U.subtype (hli.comp _ Subtype.val_injective)`. Use `hli'.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_coe, Finset.card_insert_of_notMem hkS]`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem alt_change {C W X : Type} [Field C] [AddCommGroup W] [Module C W] [AddCommGroup X]
    [Module C X] {N : ℕ} (f : W [⋀^Fin N]→ₗ[C] X) (U : Submodule C W) [FiniteDimensional C U]
    (S : Finset (Fin N)) (hS : Module.finrank C U ≤ S.card) (v w : Fin N → W)
    (h1 : ∀ i ∈ S, w i = v i) (h2 : ∀ i ∈ S, v i ∈ U) (h3 : ∀ i, w i - v i ∈ U) : f w = f v := by
  classical
  have e : w = (w - v) + v := by simp
  rw [e, f.map_add_univ, Finset.sum_eq_single ∅]
  · simp
  · intro s _ hs
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hs
    by_cases hkS : k ∈ S
    · exact f.map_coord_zero k (by simp [Finset.piecewise, hk, h1 k hkS])
    · apply f.map_linearDependent
      intro hli
      have hm : ∀ i : ↥(insert k S), s.piecewise (w - v) v i ∈ U := by
        rintro ⟨i, hi⟩
        by_cases his : i ∈ s
        · simpa [Finset.piecewise, his] using h3 i
        · have : i ∈ S := (Finset.mem_insert.1 hi).resolve_left (fun e => his (e ▸ hk))
          simpa [Finset.piecewise, his] using h2 i this
      have hli' : LinearIndependent C (fun i : ↥(insert k S) => (⟨_, hm i⟩ : U)) :=
        LinearIndependent.of_comp U.subtype (hli.comp _ Subtype.val_injective)
      have := hli'.fintype_card_le_finrank
      rw [Fintype.card_coe, Finset.card_insert_of_notMem hkS] at this
      omega
  · simp

/- English proof (translation)
Take `⟨K', hK⟩` from `K.exists_isCompl`. Establish `hd` using `Submodule.finrank_add_eq_of_isCompl hK`. Rewrite `hd` using `[hN]`. Substitute `hd` using the available equality. Use `⟨(((Module.finBasis C K).prod (Module.finBasis C K')).map (Submodule.prodEquivOfIsCompl K K' hK)).reindex finSumFinEquiv, fun i hi => ?_⟩` and prove the remaining obligations.

Establish `: i = Fin.castAdd _ ⟨i, hi⟩` using `Fin.ext rfl`. Rewrite using `[this, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Module.Basis.map_apply]`. Simplify using `[Module.Basis.prod_apply]`.
-/
theorem exists_adapted_basis {C V : Type} [Field C] [AddCommGroup V] [Module C V]
    [FiniteDimensional C V] (K : Submodule C V) {N : ℕ} (hN : Module.finrank C V = N) :
    ∃ x : Module.Basis (Fin N) C V, ∀ i : Fin N, (i : ℕ) < Module.finrank C K → x i ∈ K := by
  obtain ⟨K', hK⟩ := K.exists_isCompl
  have hd := Submodule.finrank_add_eq_of_isCompl hK
  rw [hN] at hd
  subst hd
  refine ⟨(((Module.finBasis C K).prod (Module.finBasis C K')).map
    (Submodule.prodEquivOfIsCompl K K' hK)).reindex finSumFinEquiv, fun i hi => ?_⟩
  have : i = Fin.castAdd _ ⟨i, hi⟩ := Fin.ext rfl
  rw [this, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Module.Basis.map_apply]
  simp [Module.Basis.prod_apply]

/- English proof (translation)
Introduce `C _ V W _ _ _ _ _ _ N hV α β h1 h2 a ha`. Take `⟨σ, hσ⟩` from `β.rangeRestrict.exists_rightInverse_of_surjective β.range_rangeRestrict`. Take `⟨π, hπ⟩` from `(LinearMap.range β).subtype.exists_leftInverse_of_injective (LinearMap.range β).ker_subtype`. Establish `hσ' : ∀ z, β (σ z) = z` using `fun z => congrArg Subtype.val (LinearMap.congr_fun hσ z)`. Establish `hπ' : ∀ z ∈ LinearMap.range β, (π z : V) = z` using `fun z hz => congrArg Subtype.val (LinearMap.congr_fun hπ ⟨z, hz⟩)`.

Establish `hβα : ∀ x, β (α x) = 0` using `fun x => by`. Rewrite using `[← LinearMap.mem_ker, h2]`. Conclude with `⟨x, rfl⟩`. Establish `hαβ : ∀ z ∈ LinearMap.range β, α z = 0` using `fun z hz => by`. Rewrite using `[← LinearMap.mem_ker, h1]`.

Conclude with `hz`. Set `φ : V →ₗ[C] W` to `σ ∘ₗ π + α`. Establish `hφ : ∀ x, φ x = σ (π x) + α x` using `fun x => rfl`. Establish `d1` using `α.finrank_range_add_finrank_ker`. Establish `d2` using `β.finrank_range_add_finrank_ker`.

Rewrite `d1` using `[h1, ← h2, ← ha, hV]`. Rewrite `d2` using `[← ha]`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Establish `e` using `congrArg β hx`. Rewrite `e` using `[hφ, map_add, hσ', hβα, add_zero, map_zero]`. Establish `e' : π x = 0` using `Subtype.ext e`. Rewrite `hx` using `[hφ, e', map_zero, zero_add, ← LinearMap.mem_ker, h1]`. Rewrite using `[← hπ' x hx, e]`.

Set `Φ : V ≃ₗ[C] W` to `φ.linearEquivOfInjective hinj (by omega)`. Establish `hbij : Function.Bijective (exteriorPower.map N φ)`. Establish `e1 : Φ.symm.toLinearMap ∘ₗ φ = LinearMap.id`. Use extensionality with `x`. Conclude with `Φ.symm_apply_apply x`.

Establish `e2 : φ ∘ₗ Φ.symm.toLinearMap = LinearMap.id`. Use extensionality with `x`. Conclude with `Φ.apply_symm_apply x`. Use `Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map N Φ.symm.toLinearMap, fun z => ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.comp_apply, ← exteriorPower.map_comp, e1, exteriorPower.map_id, LinearMap.id_apply]`.

Rewrite using `[← LinearMap.comp_apply, ← exteriorPower.map_comp, e2, exteriorPower.map_id, LinearMap.id_apply]`. Establish `c1 : (Finset.univ.filter fun i : Fin N => (i : ℕ) < a).card = a`. Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers. Establish `c2 : (Finset.univ.filter fun i : Fin N => ¬ (i : ℕ) < a).card = N - a`.

Use `Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin N => (i : ℕ) < a)` as an intermediate fact. Rewrite `this` using `[c1, Finset.card_univ, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∀ (x : Fin N → V) (y : Fin N → W), (∀ i : Fin N, (i : ℕ) < a → x i = β (y i)) → (∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)) → exteriorPower.map N φ (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y`. Introduce `x y hx hy`.

Rewrite using `[exteriorPower.map_apply_ιMulti]`. Set `u : Fin N → W` to `fun i => if (i : ℕ) < a then σ (π (x i)) else y i`. Use `trans exteriorPower.ιMulti C N u`. Use `alt_change _ (LinearMap.range σ) (Finset.univ.filter fun i : Fin N => (i : ℕ) < a) ?_ _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[c1, ha]`.

Conclude with `LinearMap.finrank_range_le σ`. Introduce `i hi`. Establish `hi` using `(Finset.mem_filter.1 hi).2`. Simplify using `only [Function.comp_apply, u, if_pos hi, hφ]`. Rewrite using `[hαβ _ ⟨_, (hx i hi).symm⟩, add_zero]`.

Introduce `i hi`. Establish `hi` using `(Finset.mem_filter.1 hi).2`. Simplify using `only [u, if_pos hi]`. Conclude with `⟨_, rfl⟩`. Introduce `i`.

Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `only [Function.comp_apply, u, if_pos hi, hφ]`. Rewrite using `[hαβ _ ⟨_, (hx i hi).symm⟩, add_zero, sub_self]`. Conclude with `zero_mem _`. Simplify using `only [Function.comp_apply, u, if_neg hi, hφ]`.

Rewrite using `[hy i (not_lt.1 hi), add_sub_cancel_right]`. Conclude with `⟨_, rfl⟩`. Use `symm`. Use `alt_change _ (LinearMap.ker β) (Finset.univ.filter fun i : Fin N => ¬ (i : ℕ) < a) ?_ _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[c2]`.

Use linear arithmetic over natural numbers and integers. Introduce `i hi`. Establish `hi` using `(Finset.mem_filter.1 hi).2`. Simplify using `only [u, if_neg hi]`. Introduce `i hi`.

Establish `hi` using `(Finset.mem_filter.1 hi).2`. Simplify using `only [u, if_neg hi]`. Rewrite using `[hy i (not_lt.1 hi)]`. Conclude with `hβα _`. Introduce `i`.

Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `only [u, if_pos hi]`. Rewrite using `[LinearMap.mem_ker, map_sub, hσ', hπ' _ ⟨_, (hx i hi).symm⟩, ← hx i hi, sub_self]`. Simplify using `only [u, if_neg hi, sub_self]`. Conclude with `zero_mem _`.

Establish `huniq : ∀ ι : ⋀[C]^N V →ₗ[C] ⋀[C]^N W, (∀ (x : Fin N → V) (y : Fin N → W), (∀ i : Fin N, (i : ℕ) < a → x i = β (y i)) → (∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)) → ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y) → ι = exteriorPower.map N φ`. Introduce `ι hι`. Take `⟨x, hx⟩` from `exists_adapted_basis (LinearMap.range β) hV`. Set `y : Fin N → W` to `fun i => if (i : ℕ) < a then σ (π (x i)) else α (x i)`. Establish `a1 : ∀ i : Fin N, (i : ℕ) < a → x i = β (y i)` using `fun i hi => by`.

Simplify using `only [y, if_pos hi]`. Rewrite using `[hσ', hπ' _ (hx i (ha ▸ hi))]`. Establish `a2 : ∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)` using `fun i hi => by`. Simplify using `only [y, if_neg (not_lt.2 hi)]`. Establish `e` using `(hι x y a1 a2).trans (hex x y a1 a2).symm`.

Apply `exteriorPower.linearMap_ext` to reduce the goal to its premises. Use `x.ext_alternating fun s hs => ?_` and prove the remaining obligations. Set `s' : Equiv.Perm (Fin N)` to `Equiv.ofBijective s (Finite.injective_iff_bijective.1 hs)`. Establish `e' : (fun j => x (s j)) = x ∘ s'` using `rfl`. Rewrite using `[e', AlternatingMap.map_perm, AlternatingMap.map_perm]`.

Conclude with `congrArg _ e`. Conclude with `⟨⟨_, hex, huniq⟩, fun ι hι => huniq ι hι ▸ hbij⟩`.
-/
theorem exists_unique_wedge_map : ∀ (C : Type) [Field C] (V W : Type) [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W]
    [FiniteDimensional C V] [FiniteDimensional C W] (N : ℕ), Module.finrank C V = N →
    ∀ (α : V →ₗ[C] W) (β : W →ₗ[C] V), LinearMap.ker α = LinearMap.range β →
    LinearMap.ker β = LinearMap.range α → ∀ (a : ℕ), a = Module.finrank C (LinearMap.range β) →
    (∃! ι : ⋀[C]^N V →ₗ[C] ⋀[C]^N W, ∀ (x : Fin N → V) (y : Fin N → W),
        (∀ i : Fin N, (i : ℕ) < a → x i = β (y i)) → (∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)) →
        ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y) ∧
    ∀ ι : ⋀[C]^N V →ₗ[C] ⋀[C]^N W, (∀ (x : Fin N → V) (y : Fin N → W),
        (∀ i : Fin N, (i : ℕ) < a → x i = β (y i)) → (∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)) →
        ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y) → Function.Bijective ι := by
  intro C _ V W _ _ _ _ _ _ N hV α β h1 h2 a ha
  classical
  obtain ⟨σ, hσ⟩ := β.rangeRestrict.exists_rightInverse_of_surjective β.range_rangeRestrict
  obtain ⟨π, hπ⟩ := (LinearMap.range β).subtype.exists_leftInverse_of_injective
    (LinearMap.range β).ker_subtype
  have hσ' : ∀ z, β (σ z) = z := fun z => congrArg Subtype.val (LinearMap.congr_fun hσ z)
  have hπ' : ∀ z ∈ LinearMap.range β, (π z : V) = z := fun z hz =>
    congrArg Subtype.val (LinearMap.congr_fun hπ ⟨z, hz⟩)
  have hβα : ∀ x, β (α x) = 0 := fun x => by
    rw [← LinearMap.mem_ker, h2]; exact ⟨x, rfl⟩
  have hαβ : ∀ z ∈ LinearMap.range β, α z = 0 := fun z hz => by
    rw [← LinearMap.mem_ker, h1]; exact hz
  let φ : V →ₗ[C] W := σ ∘ₗ π + α
  have hφ : ∀ x, φ x = σ (π x) + α x := fun x => rfl
  have d1 := α.finrank_range_add_finrank_ker
  have d2 := β.finrank_range_add_finrank_ker
  rw [h1, ← h2, ← ha, hV] at d1
  rw [← ha] at d2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have e := congrArg β hx
    rw [hφ, map_add, hσ', hβα, add_zero, map_zero] at e
    have e' : π x = 0 := Subtype.ext e
    rw [hφ, e', map_zero, zero_add, ← LinearMap.mem_ker, h1] at hx
    rw [← hπ' x hx, e]
  let Φ : V ≃ₗ[C] W := φ.linearEquivOfInjective hinj (by omega)
  have hbij : Function.Bijective (exteriorPower.map N φ) := by
    have e1 : Φ.symm.toLinearMap ∘ₗ φ = LinearMap.id := by
      ext x; exact Φ.symm_apply_apply x
    have e2 : φ ∘ₗ Φ.symm.toLinearMap = LinearMap.id := by
      ext x; exact Φ.apply_symm_apply x
    refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map N Φ.symm.toLinearMap, fun z => ?_,
      fun z => ?_⟩
    · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, e1, exteriorPower.map_id, LinearMap.id_apply]
    · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, e2, exteriorPower.map_id, LinearMap.id_apply]
  have c1 : (Finset.univ.filter fun i : Fin N => (i : ℕ) < a).card = a := by
    rw [Fin.card_filter_val_lt]; omega
  have c2 : (Finset.univ.filter fun i : Fin N => ¬ (i : ℕ) < a).card = N - a := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin N => (i : ℕ) < a)
    rw [c1, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hex : ∀ (x : Fin N → V) (y : Fin N → W),
      (∀ i : Fin N, (i : ℕ) < a → x i = β (y i)) → (∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)) →
      exteriorPower.map N φ (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y := by
    intro x y hx hy
    rw [exteriorPower.map_apply_ιMulti]
    let u : Fin N → W := fun i => if (i : ℕ) < a then σ (π (x i)) else y i
    trans exteriorPower.ιMulti C N u
    · refine alt_change _ (LinearMap.range σ) (Finset.univ.filter fun i : Fin N => (i : ℕ) < a)
        ?_ _ _ ?_ ?_ ?_
      · rw [c1, ha]; exact LinearMap.finrank_range_le σ
      · intro i hi
        have hi := (Finset.mem_filter.1 hi).2
        simp only [Function.comp_apply, u, if_pos hi, hφ]
        rw [hαβ _ ⟨_, (hx i hi).symm⟩, add_zero]
      · intro i hi
        have hi := (Finset.mem_filter.1 hi).2
        simp only [u, if_pos hi]
        exact ⟨_, rfl⟩
      · intro i
        by_cases hi : (i : ℕ) < a
        · simp only [Function.comp_apply, u, if_pos hi, hφ]
          rw [hαβ _ ⟨_, (hx i hi).symm⟩, add_zero, sub_self]
          exact zero_mem _
        · simp only [Function.comp_apply, u, if_neg hi, hφ]
          rw [hy i (not_lt.1 hi), add_sub_cancel_right]
          exact ⟨_, rfl⟩
    · symm
      refine alt_change _ (LinearMap.ker β) (Finset.univ.filter fun i : Fin N => ¬ (i : ℕ) < a)
        ?_ _ _ ?_ ?_ ?_
      · rw [c2]; omega
      · intro i hi
        have hi := (Finset.mem_filter.1 hi).2
        simp only [u, if_neg hi]
      · intro i hi
        have hi := (Finset.mem_filter.1 hi).2
        simp only [u, if_neg hi]
        rw [hy i (not_lt.1 hi)]
        exact hβα _
      · intro i
        by_cases hi : (i : ℕ) < a
        · simp only [u, if_pos hi]
          rw [LinearMap.mem_ker, map_sub, hσ', hπ' _ ⟨_, (hx i hi).symm⟩, ← hx i hi, sub_self]
        · simp only [u, if_neg hi, sub_self]
          exact zero_mem _
  have huniq : ∀ ι : ⋀[C]^N V →ₗ[C] ⋀[C]^N W, (∀ (x : Fin N → V) (y : Fin N → W),
      (∀ i : Fin N, (i : ℕ) < a → x i = β (y i)) → (∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i)) →
      ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y) → ι = exteriorPower.map N φ := by
    intro ι hι
    obtain ⟨x, hx⟩ := exists_adapted_basis (LinearMap.range β) hV
    let y : Fin N → W := fun i => if (i : ℕ) < a then σ (π (x i)) else α (x i)
    have a1 : ∀ i : Fin N, (i : ℕ) < a → x i = β (y i) := fun i hi => by
      simp only [y, if_pos hi]
      rw [hσ', hπ' _ (hx i (ha ▸ hi))]
    have a2 : ∀ i : Fin N, a ≤ (i : ℕ) → y i = α (x i) := fun i hi => by
      simp only [y, if_neg (not_lt.2 hi)]
    have e := (hι x y a1 a2).trans (hex x y a1 a2).symm
    apply exteriorPower.linearMap_ext
    refine x.ext_alternating fun s hs => ?_
    let s' : Equiv.Perm (Fin N) := Equiv.ofBijective s (Finite.injective_iff_bijective.1 hs)
    have e' : (fun j => x (s j)) = x ∘ s' := rfl
    rw [e', AlternatingMap.map_perm, AlternatingMap.map_perm]
    exact congrArg _ e
  exact ⟨⟨_, hex, huniq⟩, fun ι hι => huniq ι hι ▸ hbij⟩

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε h Λ _ _ D τ`. Use `haveI : IsFractionRing O C := hv.isFractionRing`. Establish `hinj : Function.Injective (algebraMap O C)` using `IsFractionRing.injective O C`. Set `j : (Fin h → O) →ₗ[O] (Fin h → C)` to `(Algebra.linearMap O C).compLeft (Fin h)`. Establish `hj : Function.Injective j` using `fun x y e => funext fun i => hinj (congrFun e i)`.

Establish `mv : ∀ (X : Matrix (Fin h) (Fin h) O) (z : Fin h → O), j (Matrix.toLin' X z) = Matrix.toLin' (X.map (algebraMap O C)) (j z)`. Introduce `X z`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (algebraMap O C) X z i`. Establish `mb : ∀ z, j (D.bb z) = bC C D (j z)` using `fun z => mv _ z`.

Establish `mT : ∀ z, z ∈ D.Tsub τ ↔ j z ∈ eig C (actT D) τ`. Introduce `z`. Simplify using `only [Datum.Tsub, eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Use `forall_congr' fun b => ?_` and prove the remaining obligations. Rewrite using `[← mv, algebraMap_smul, ← map_smul, hj.eq_iff]`.

Both sides reduce to the same expression. Use `set U := LinearMap.range (bC C D) ⊓ eig C (actT D) τ with hU`. Establish `hm : ∀ z : ↥(D.Lie ⊓ D.Tsub τ), j z ∈ U`. Introduce and unpack `⟨_, ⟨z, rfl⟩, hz⟩`. Conclude with `⟨⟨_, (mb z).symm⟩, (mT _).1 hz⟩`.

Set `g : ↥(D.Lie ⊓ D.Tsub τ) →ₗ[O] U` to `{ toFun := fun z => ⟨j z, hm z⟩ map_add' := fun x y => Subtype.ext (map_add j _ _) map_smul' := fun c x => Subtype.ext (map_smul j _ _) }`. Use `haveI : IsLocalizedModule (nonZeroDivisors O) g := { map_units := fun s => by`. Rewrite using `[Module.End.isUnit_iff]`. Establish `hs : algebraMap O C s ≠ 0` using `(IsLocalization.map_units C s).ne_zero`. Establish `e : ⇑(algebraMap O (Module.End O U) s) = fun z : U => algebraMap O C s • z`.

Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `(MulAction.bijective (Units.mk0 _ hs))`. Use `surj := by`.

Introduce and unpack `⟨_, ⟨w, rfl⟩, hw⟩`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w`. Use `choose z hz using hc`. Establish `e : j z = (c : O) • w` using `funext hz`. Establish `e2 : j (D.bb z) = (c : O) • bC C D w`.

Rewrite using `[mb, e, ← algebraMap_smul C, map_smul, algebraMap_smul]`. Use `⟨⟨⟨D.bb z, ⟨z, rfl⟩, (mT _).2 ?_⟩, c⟩, Subtype.ext e2.symm⟩` and prove the remaining obligations. Rewrite using `[e2, ← algebraMap_smul C]`. Conclude with `Submodule.smul_mem _ _ hw`. Use `exists_of_eq := fun e => ⟨1, by`.

Rewrite using `[Subtype.ext (hj (congrArg Subtype.val e))]⟩ }`. Rewrite using `[Datum.lieRank, ← IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl, IsFractionRing.finrank_right_eq O C]`.
-/
theorem lieRank_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p) (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (D : GlobalTheory.Sandwich.Datum ε h Λ)
      (τ : Λ →+* O),
      D.lieRank τ = Module.finrank C ↥(LinearMap.range (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D) ⊓
        GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.eig C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε h Λ _ _ D τ
  haveI : IsFractionRing O C := hv.isFractionRing
  have hinj : Function.Injective (algebraMap O C) := IsFractionRing.injective O C
  let j : (Fin h → O) →ₗ[O] (Fin h → C) := (Algebra.linearMap O C).compLeft (Fin h)
  have hj : Function.Injective j := fun x y e => funext fun i => hinj (congrFun e i)
  have mv : ∀ (X : Matrix (Fin h) (Fin h) O) (z : Fin h → O),
      j (Matrix.toLin' X z) = Matrix.toLin' (X.map (algebraMap O C)) (j z) := by
    intro X z; funext i
    exact RingHom.map_mulVec (algebraMap O C) X z i
  have mb : ∀ z, j (D.bb z) = bC C D (j z) := fun z => mv _ z
  have mT : ∀ z, z ∈ D.Tsub τ ↔ j z ∈ eig C (actT D) τ := by
    intro z
    simp only [Datum.Tsub, eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    refine forall_congr' fun b => ?_
    rw [← mv, algebraMap_smul, ← map_smul, hj.eq_iff]
    rfl
  set U := LinearMap.range (bC C D) ⊓ eig C (actT D) τ with hU
  have hm : ∀ z : ↥(D.Lie ⊓ D.Tsub τ), j z ∈ U := by
    rintro ⟨_, ⟨z, rfl⟩, hz⟩
    exact ⟨⟨_, (mb z).symm⟩, (mT _).1 hz⟩
  let g : ↥(D.Lie ⊓ D.Tsub τ) →ₗ[O] U :=
    { toFun := fun z => ⟨j z, hm z⟩
      map_add' := fun x y => Subtype.ext (map_add j _ _)
      map_smul' := fun c x => Subtype.ext (map_smul j _ _) }
  haveI : IsLocalizedModule (nonZeroDivisors O) g :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have hs : algebraMap O C s ≠ 0 := (IsLocalization.map_units C s).ne_zero
        have e : ⇑(algebraMap O (Module.End O U) s) = fun z : U => algebraMap O C s • z := by
          funext z; simp
        rw [e]
        exact (MulAction.bijective (Units.mk0 _ hs))
      surj := by
        rintro ⟨_, ⟨w, rfl⟩, hw⟩
        obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
        choose z hz using hc
        have e : j z = (c : O) • w := funext hz
        have e2 : j (D.bb z) = (c : O) • bC C D w := by
          rw [mb, e, ← algebraMap_smul C, map_smul, algebraMap_smul]
        refine ⟨⟨⟨D.bb z, ⟨z, rfl⟩, (mT _).2 ?_⟩, c⟩, Subtype.ext e2.symm⟩
        rw [e2, ← algebraMap_smul C]
        exact Submodule.smul_mem _ _ hw
      exists_of_eq := fun e => ⟨1, by
        rw [Subtype.ext (hj (congrArg Subtype.val e))]⟩ }
  rw [Datum.lieRank, ← IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl,
    IsFractionRing.finrank_right_eq O C]

/- English proof (translation)
Introduce `p _ Λ _ _ _ _ _ _ a hdeg N h hh ρ`. Establish `hint : IsIntegral ℤ_[p] a` using `IsIntegral.of_finite _ a`. Establish `h1 : LinearMap.charpoly (LinearMap.mulLeft ℤ_[p] a) = minpoly ℤ_[p] a`. Use `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) (minpoly.isIntegrallyClosed_dvd hint ?_) (by rw [LinearMap.charpoly_natDegree, hdeg])` and prove the remaining obligations. Establish `e` using `LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℤ_[p] a)`.

Establish `e2` using `Polynomial.aeval_algHom_apply (Algebra.lmul ℤ_[p] Λ) a (LinearMap.charpoly (LinearMap.mulLeft ℤ_[p] a))`. Establish `e3 : Algebra.lmul ℤ_[p] Λ a = LinearMap.mulLeft ℤ_[p] a` using `rfl`. Rewrite `e2` using `[e3, e]`. Conclude with `Algebra.lmul_injective (by rw [← e2, map_zero])`. Set `r : Λ →ₐ[ℤ_[p]] Module.End ℤ_[p] (Fin h → ℤ_[p])` to `Matrix.toLinAlgEquiv'.toAlgHom.comp ρ`.

Use `letI : Module Λ (Fin h → ℤ_[p]) := Module.compHom _ r.toRingHom`. Establish `hs : ∀ (b : Λ) (x : Fin h → ℤ_[p]), b • x = r b x` using `fun _ _ => rfl`. Use `haveI : IsScalarTower ℤ_[p] Λ (Fin h → ℤ_[p]) := ⟨fun c b x => by`. Rewrite using `[hs, hs, map_smul, LinearMap.smul_apply]⟩`. Use `haveI : Module.Finite Λ (Fin h → ℤ_[p]) := Module.Finite.of_restrictScalars_finite ℤ_[p] _ _`.

Use `haveI : Module.IsTorsionFree Λ (Fin h → ℤ_[p]) := by`. Use `Module.IsTorsionFree.of_smul_eq_zero fun b x hbx => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = 0`. Conclude with `Or.inl hb`. Take `⟨c, hc, d, hd⟩` from `(IsIntegral.of_finite ℤ_[p] b).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hb)`.

Establish `: c • x = 0`. Rewrite using `[← algebraMap_smul Λ, hd, mul_comm, mul_smul, hbx, smul_zero]`. Conclude with `Or.inr ((smul_eq_zero.1 this).resolve_left hc)`. Establish `hN : Module.finrank Λ (Fin h → ℤ_[p]) = N`. Establish `e` using `Module.finrank_mul_finrank ℤ_[p] Λ (Fin h → ℤ_[p])`.

Rewrite `e` using `[Module.finrank_fin_fun]`. Conclude with `Nat.eq_of_mul_eq_mul_left Module.finrank_pos (e.trans hh)`. Establish `e` using `GlobalTheory.FibreCharpoly.charpoly_lsmul_eq_pow ℤ_[p] Λ (Fin h → ℤ_[p]) (Module.finBasisOfFinrankEq Λ _ hN) a`. Rewrite `e` using `[h1]`. Rewrite using `[← e, ← Matrix.charpoly_toLin']`.

Both sides reduce to the same expression.
-/
theorem charpoly_action_eq_pow : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (a : Λ),
    (minpoly ℤ_[p] a).natDegree = Module.finrank ℤ_[p] Λ →
    ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
    ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]), (ρ a).charpoly = minpoly ℤ_[p] a ^ N := by
  intro p _ Λ _ _ _ _ _ _ a hdeg N h hh ρ
  have hint : IsIntegral ℤ_[p] a := IsIntegral.of_finite _ a
  have h1 : LinearMap.charpoly (LinearMap.mulLeft ℤ_[p] a) = minpoly ℤ_[p] a := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (LinearMap.charpoly_monic _) (minpoly.isIntegrallyClosed_dvd hint ?_)
      (by rw [LinearMap.charpoly_natDegree, hdeg])
    have e := LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℤ_[p] a)
    have e2 := Polynomial.aeval_algHom_apply (Algebra.lmul ℤ_[p] Λ) a
      (LinearMap.charpoly (LinearMap.mulLeft ℤ_[p] a))
    have e3 : Algebra.lmul ℤ_[p] Λ a = LinearMap.mulLeft ℤ_[p] a := rfl
    rw [e3, e] at e2
    exact Algebra.lmul_injective (by rw [← e2, map_zero])
  let r : Λ →ₐ[ℤ_[p]] Module.End ℤ_[p] (Fin h → ℤ_[p]) := Matrix.toLinAlgEquiv'.toAlgHom.comp ρ
  letI : Module Λ (Fin h → ℤ_[p]) := Module.compHom _ r.toRingHom
  have hs : ∀ (b : Λ) (x : Fin h → ℤ_[p]), b • x = r b x := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[p] Λ (Fin h → ℤ_[p]) := ⟨fun c b x => by
    rw [hs, hs, map_smul, LinearMap.smul_apply]⟩
  haveI : Module.Finite Λ (Fin h → ℤ_[p]) := Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  haveI : Module.IsTorsionFree Λ (Fin h → ℤ_[p]) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun b x hbx => ?_
    by_cases hb : b = 0
    · exact Or.inl hb
    obtain ⟨c, hc, d, hd⟩ := (IsIntegral.of_finite ℤ_[p] b).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hb)
    have : c • x = 0 := by
      rw [← algebraMap_smul Λ, hd, mul_comm, mul_smul, hbx, smul_zero]
    exact Or.inr ((smul_eq_zero.1 this).resolve_left hc)
  have hN : Module.finrank Λ (Fin h → ℤ_[p]) = N := by
    have e := Module.finrank_mul_finrank ℤ_[p] Λ (Fin h → ℤ_[p])
    rw [Module.finrank_fin_fun] at e
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos (e.trans hh)
  have e := GlobalTheory.FibreCharpoly.charpoly_lsmul_eq_pow ℤ_[p] Λ (Fin h → ℤ_[p])
    (Module.finBasisOfFinrankEq Λ _ hN) a
  rw [h1] at e
  rw [← e, ← Matrix.charpoly_toLin']
  rfl

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in

/- English proof (translation)
Introduce `p _ Λ _ _ _ _ _ _`. Take `⟨α, hα⟩` from `Field.exists_primitive_element (FractionRing ℤ_[p]) (FractionRing Λ)`. Establish `halg : IsAlgebraic ℤ_[p] α` using `(IsFractionRing.isAlgebraic_iff ℤ_[p] (FractionRing ℤ_[p]) _).2 (IsAlgebraic.of_finite _ α)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral (R := Λ) (hint.tower_top (A := Λ))`.

Establish `hy' : algebraMap ℤ_[p] (FractionRing ℤ_[p]) y ≠ 0` using `by simpa using hy`. Establish `htop : IntermediateField.adjoin (FractionRing ℤ_[p]) {algebraMap Λ (FractionRing Λ) a} = ⊤`. Rewrite using `[eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]`. Establish `: α = (algebraMap ℤ_[p] (FractionRing ℤ_[p]) y)⁻¹ • algebraMap Λ (FractionRing Λ) a`. Rewrite using `[ha, ← algebraMap_smul (FractionRing ℤ_[p]) y α, smul_smul, inv_mul_cancel₀ hy', one_smul]`.

Rewrite using `[this]`. Conclude with `IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self _ _)`. Use `⟨a, fun b => ?_, ?_⟩` and prove the remaining obligations. Establish `hb : algebraMap Λ (FractionRing Λ) b ∈ Algebra.adjoin (FractionRing ℤ_[p]) {algebraMap Λ (FractionRing Λ) a}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite _ _), htop]`.

Discharge the goal by the elementary cases of `trivial`. Rewrite `hb` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨q, hq⟩` from `hb`. Take `⟨m, hm, hmq⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ_[p]) q`. Use `⟨m, nonZeroDivisors.ne_zero hm, IsLocalization.integerNormalization (nonZeroDivisors ℤ_[p]) q, ?_⟩` and prove the remaining obligations.

Apply `IsFractionRing.injective Λ (FractionRing Λ)` to reduce the goal to its premises. Rewrite using `[← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap (FractionRing ℤ_[p]), hmq, ← algebraMap_smul (FractionRing ℤ_[p]) m q, map_smul (Polynomial.aeval _), algebraMap_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]`. Conclude with `congrArg _ hq.symm`. Establish `e` using `(Field.primitive_element_iff_minpoly_natDegree_eq _ _).1 htop`. Rewrite `e` using `[minpoly.isIntegrallyClosed_eq_field_fractions (FractionRing ℤ_[p]) (FractionRing Λ) (IsIntegral.of_finite ℤ_[p] a), (minpoly.monic (IsIntegral.of_finite ℤ_[p] a)).natDegree_map]`.

Rewrite using `[e, IsFractionRing.finrank_eq ℤ_[p] (FractionRing ℤ_[p]) Λ (FractionRing Λ)]`.
-/
theorem exists_generator : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    ∃ a : Λ, (∀ b : Λ, ∃ m : ℤ_[p], m ≠ 0 ∧ ∃ Q : Polynomial ℤ_[p], m • b = Polynomial.aeval a Q) ∧
      (minpoly ℤ_[p] a).natDegree = Module.finrank ℤ_[p] Λ := by
  intro p _ Λ _ _ _ _ _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (FractionRing ℤ_[p]) (FractionRing Λ)
  have halg : IsAlgebraic ℤ_[p] α :=
    (IsFractionRing.isAlgebraic_iff ℤ_[p] (FractionRing ℤ_[p]) _).2 (IsAlgebraic.of_finite _ α)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := Λ) (hint.tower_top (A := Λ))
  have hy' : algebraMap ℤ_[p] (FractionRing ℤ_[p]) y ≠ 0 := by simpa using hy
  have htop : IntermediateField.adjoin (FractionRing ℤ_[p]) {algebraMap Λ (FractionRing Λ) a} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have : α = (algebraMap ℤ_[p] (FractionRing ℤ_[p]) y)⁻¹ • algebraMap Λ (FractionRing Λ) a := by
      rw [ha, ← algebraMap_smul (FractionRing ℤ_[p]) y α, smul_smul, inv_mul_cancel₀ hy', one_smul]
    rw [this]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self _ _)
  refine ⟨a, fun b => ?_, ?_⟩
  · have hb : algebraMap Λ (FractionRing Λ) b ∈
        Algebra.adjoin (FractionRing ℤ_[p]) {algebraMap Λ (FractionRing Λ) a} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite _ _), htop]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨q, hq⟩ := hb
    obtain ⟨m, hm, hmq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ_[p]) q
    refine ⟨m, nonZeroDivisors.ne_zero hm, IsLocalization.integerNormalization (nonZeroDivisors ℤ_[p]) q, ?_⟩
    apply IsFractionRing.injective Λ (FractionRing Λ)
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap (FractionRing ℤ_[p]), hmq,
      ← algebraMap_smul (FractionRing ℤ_[p]) m q, map_smul (Polynomial.aeval _), algebraMap_smul,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
    exact congrArg _ hq.symm
  · have e := (Field.primitive_element_iff_minpoly_natDegree_eq _ _).1 htop
    rw [minpoly.isIntegrallyClosed_eq_field_fractions (FractionRing ℤ_[p]) (FractionRing Λ)
      (IsIntegral.of_finite ℤ_[p] a), (minpoly.monic (IsIntegral.of_finite ℤ_[p] a)).natDegree_map] at e
    rw [e, IsFractionRing.finrank_eq ℤ_[p] (FractionRing ℤ_[p]) Λ (FractionRing Λ)]

/- English proof (translation)
Introduce `p _ O _ _ _ f`. Use extensionality with `x`. Rewrite using `[← sub_eq_zero]`. Apply `IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance` to reduce the goal to its premises. Introduce `n`.

Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)`. Establish `hx : x = u * (p : ℤ_[p]) ^ n + (x.appr n : ℤ_[p])` using `by rw [hu]; ring`. Rewrite using `[SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton']`. Use `⟨f u - padicToO p O u, ?_⟩` and prove the remaining obligations. Establish `e : ∀ g : ℤ_[p] →+* O, g x = g u * (p : O) ^ n + (x.appr n : O)` using `fun g => by conv_lhs => rw [hx]`.

Simplify using the standard rewrite rules. Rewrite using `[e f, e (padicToO p O)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ringHom_padicInt_eq : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (f : ℤ_[p] →+* O), f = GlobalTheory.Sandwich.padicToO p O := by
  intro p _ O _ _ _ f
  ext x
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance
  intro n
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = u * (p : ℤ_[p]) ^ n + (x.appr n : ℤ_[p]) := by rw [hu]; ring
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton']
  refine ⟨f u - padicToO p O u, ?_⟩
  have e : ∀ g : ℤ_[p] →+* O, g x = g u * (p : O) ^ n + (x.appr n : O) := fun g => by
    conv_lhs => rw [hx]
    simp
  rw [e f, e (padicToO p O)]; ring

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε h Λ _ _ D`. Take `⟨hdom, -, -, -, hν, hξ, -⟩` from `GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε`. Establish `hμ : mu ε ≠ 0`. Rewrite using `[← xi_mul_nu]`. Use `mul_ne_zero hξ ?_` and prove the remaining obligations.

Introduce `h0`. Apply `hν` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Establish `hG : ∀ a, D.G * D.ρM a = (D.ρT a).map (ofPadic p O) * D.G`. Introduce `a`.

Apply `HodgeTateBound.right_cancel hμ D.G_mul_F` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, ← D.F_act, ← Matrix.mul_assoc, D.G_mul_F, Matrix.mul_assoc, D.G_mul_F]`. Simplify using the standard rewrite rules. Establish `eT : ∀ a, (actT D a).map (algebraMap O C) = ((D.ρT a).map (ofPadic p O)).map ((algebraMap O C).comp (fontaineTheta O p))` using `fun a => rfl`. Establish `eH : ∀ a, (actH D a).map (algebraMap O C) = (D.ρM a).map ((algebraMap O C).comp (fontaineTheta O p))` using `fun a => rfl`.

Establish `sT : ∀ c : ℤ_[p], (D.ρT (algebraMap ℤ_[p] Λ c)).map (ofPadic p O) = ofPadic p O c • 1`. Introduce `c`. Rewrite using `[AlgHom.commutes]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.algebraMap_matrix_apply]`.

Establish `sc : ∀ c : ℤ_[p], (ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))).map (fontaineTheta O p) = padicToO p O c • 1`. Introduce `c`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, padicToO]`. Use `⟨fun a => ?_, fun a => ?_, fun c => ?_, fun c => ?_⟩` and prove the remaining obligations.

Rewrite using `[eT, eH]`. Unfold `bC redC`. Rewrite using `[← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, hG]`. Rewrite using `[eT, eH]`. Unfold `alC redC`.

Rewrite using `[← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, D.F_act]`. Rewrite using `[← sc, ← sT]`. Both sides reduce to the same expression. Establish `: D.ρM (algebraMap ℤ_[p] Λ c) = ofPadic p O c • 1`. Apply `HodgeTateBound.right_cancel hμ D.G_mul_F` to reduce the goal to its premises.

Rewrite using `[← D.F_act, sT]`. Simplify using the standard rewrite rules. Rewrite using `[← sc, ← this]`. Both sides reduce to the same expression.
-/
theorem datum_equivariant : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (D : GlobalTheory.Sandwich.Datum ε h Λ),
      (∀ a : Λ, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D ∘ₗ
          Matrix.toLin' ((GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D a).map (algebraMap O C)) =
        Matrix.toLin' ((GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D a).map (algebraMap O C)) ∘ₗ GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D) ∧
      (∀ a : Λ, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D ∘ₗ
          Matrix.toLin' ((GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D a).map (algebraMap O C)) =
        Matrix.toLin' ((GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D a).map (algebraMap O C)) ∘ₗ GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D) ∧
      (∀ c : ℤ_[p], GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D (algebraMap ℤ_[p] Λ c) =
        GlobalTheory.Sandwich.padicToO p O c • (1 : Matrix (Fin h) (Fin h) O)) ∧
      (∀ c : ℤ_[p], GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D (algebraMap ℤ_[p] Λ c) =
        GlobalTheory.Sandwich.padicToO p O c • (1 : Matrix (Fin h) (Fin h) O)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε h Λ _ _ D
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hμ : mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    refine mul_ne_zero hξ ?_
    intro h0; apply hν; rw [h0, map_zero]
  have hG : ∀ a, D.G * D.ρM a = (D.ρT a).map (ofPadic p O) * D.G := by
    intro a
    apply HodgeTateBound.right_cancel hμ D.G_mul_F
    rw [Matrix.mul_assoc, ← D.F_act, ← Matrix.mul_assoc, D.G_mul_F, Matrix.mul_assoc, D.G_mul_F]
    simp
  have eT : ∀ a, (actT D a).map (algebraMap O C) =
      ((D.ρT a).map (ofPadic p O)).map ((algebraMap O C).comp (fontaineTheta O p)) := fun a => rfl
  have eH : ∀ a, (actH D a).map (algebraMap O C) =
      (D.ρM a).map ((algebraMap O C).comp (fontaineTheta O p)) := fun a => rfl
  have sT : ∀ c : ℤ_[p], (D.ρT (algebraMap ℤ_[p] Λ c)).map (ofPadic p O) = ofPadic p O c • 1 := by
    intro c
    rw [AlgHom.commutes]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.algebraMap_matrix_apply]
  have sc : ∀ c : ℤ_[p], (ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))).map
      (fontaineTheta O p) = padicToO p O c • 1 := by
    intro c
    ext i j
    by_cases hij : i = j <;> simp [hij, padicToO]
  refine ⟨fun a => ?_, fun a => ?_, fun c => ?_, fun c => ?_⟩
  · rw [eT, eH]; unfold bC redC
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, hG]
  · rw [eT, eH]; unfold alC redC
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, D.F_act]
  · rw [← sc, ← sT]; rfl
  · have : D.ρM (algebraMap ℤ_[p] Λ c) = ofPadic p O c • 1 := by
      apply HodgeTateBound.right_cancel hμ D.G_mul_F
      rw [← D.F_act, sT]; simp
    rw [← sc, ← this]; rfl

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O C)` using `IsFractionRing.injective O C`. Use `haveI : Nontrivial O := (algebraMap O C).domain_nontrivial`. Establish `hθξ : θ ξ = 0`. Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `Ideal.mem_span_singleton_self _`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) f`. Use `choose g hg using hc`. Establish `hc0 : algebraMap O C c ≠ 0` using `fun h0 => nonZeroDivisors.coe_ne_zero c (hinj (by rw [h0, map_zero]))`.

Establish `hgf : (algebraMap O C) ∘ g = algebraMap O C c • f`. Use function extensionality and compare the values at `i`. Simplify using `[hg i, Algebra.smul_def]`. Establish `mv : ∀ (X : Matrix (Fin h) (Fin h) A) (z : Fin h → O), (algebraMap O C) ∘ (Matrix.toLin' (X.map θ) z) = Matrix.toLin' (X.map ((algebraMap O C).comp θ)) ((algebraMap O C) ∘ z)`. Introduce `X z`.

Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, RingHom.map_mulVec, Matrix.map_map]`. Both sides reduce to the same expression. Establish `hg0 : g ∈ LinearMap.ker (Matrix.toLin' (G.map θ))`. Rewrite `hf`, the goal using `[LinearMap.mem_ker]`.

Use function extensionality and compare the values at `i`. Apply `hinj` to reduce the goal to its premises. Use `congrFun (mv G g) i` as an intermediate fact. Rewrite `this` using `[hgf, map_smul, hf]`. Simplify using `using this`.

Take `⟨z, hz⟩` from `HodgeTateBound.smul_mem_range θ hs hker hξ hμ hFG g hg0`. Establish `hν0 : algebraMap O C (θ ν) ≠ 0` using `fun h0 => hν (hinj (by rw [h0, map_zero]))`. Use `⟨(algebraMap O C (θ ν) * algebraMap O C c)⁻¹ • ((algebraMap O C) ∘ z), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← mv, hz]`. Establish `: (algebraMap O C) ∘ (θ ν • g) = algebraMap O C (θ ν) • ((algebraMap O C) ∘ g)`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[this, hgf, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hν0 hc0), one_smul]`. Conclude with `HodgeTateBound.range_le_ker _ (by rw [← hμ]; simp [hθξ]) hGF`.
-/
theorem ker_eq_range_of {A O C : Type} [CommRing A] [IsDomain A] [CommRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] {h : ℕ} (θ : A →+* O) (hs : Function.Surjective θ) {ξ ν μ : A}
    (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ξ ≠ 0) (hν : θ ν ≠ 0) (hμ : ξ * ν = μ)
    {F G : Matrix (Fin h) (Fin h) A} (hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A))
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    LinearMap.ker (Matrix.toLin' (G.map ((algebraMap O C).comp θ))) =
      LinearMap.range (Matrix.toLin' (F.map ((algebraMap O C).comp θ))) := by
  have hinj : Function.Injective (algebraMap O C) := IsFractionRing.injective O C
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  have hθξ : θ ξ = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  apply le_antisymm
  · intro f hf
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) f
    choose g hg using hc
    have hc0 : algebraMap O C c ≠ 0 := fun h0 =>
      nonZeroDivisors.coe_ne_zero c (hinj (by rw [h0, map_zero]))
    have hgf : (algebraMap O C) ∘ g = algebraMap O C c • f := by
      funext i; simp [hg i, Algebra.smul_def]
    have mv : ∀ (X : Matrix (Fin h) (Fin h) A) (z : Fin h → O),
        (algebraMap O C) ∘ (Matrix.toLin' (X.map θ) z) =
          Matrix.toLin' (X.map ((algebraMap O C).comp θ)) ((algebraMap O C) ∘ z) := by
      intro X z; funext i
      rw [Function.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, RingHom.map_mulVec,
        Matrix.map_map]
      rfl
    have hg0 : g ∈ LinearMap.ker (Matrix.toLin' (G.map θ)) := by
      rw [LinearMap.mem_ker] at hf ⊢
      funext i
      apply hinj
      have := congrFun (mv G g) i
      rw [hgf, map_smul, hf] at this
      simpa using this
    obtain ⟨z, hz⟩ := HodgeTateBound.smul_mem_range θ hs hker hξ hμ hFG g hg0
    have hν0 : algebraMap O C (θ ν) ≠ 0 := fun h0 => hν (hinj (by rw [h0, map_zero]))
    refine ⟨(algebraMap O C (θ ν) * algebraMap O C c)⁻¹ • ((algebraMap O C) ∘ z), ?_⟩
    rw [map_smul, ← mv, hz]
    have : (algebraMap O C) ∘ (θ ν • g) = algebraMap O C (θ ν) • ((algebraMap O C) ∘ g) := by
      funext i; simp
    rw [this, hgf, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hν0 hc0), one_smul]
  · exact HodgeTateBound.range_le_ker _ (by rw [← hμ]; simp [hθξ]) hGF

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε h Λ _ _ D`. Take `⟨hdom, -, hker, hs, hν, hξ, -⟩` from `GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε`. Establish `hμ : mu ε ≠ 0`. Rewrite using `[← xi_mul_nu]`. Use `mul_ne_zero hξ ?_` and prove the remaining obligations.

Introduce `h0`. Apply `hν` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Use `haveI : IsFractionRing O C := hv.isFractionRing`. Establish `hFG` using `HodgeTateBound.mul_swap hμ D.G_mul_F`.

Conclude with `⟨ker_eq_range_of _ hs hker hξ hν (xi_mul_nu ε) hFG D.G_mul_F, ker_eq_range_of _ hs hker hξ hν (xi_mul_nu ε) D.G_mul_F hFG⟩`.
-/
theorem hodgeTate_exact : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (D : GlobalTheory.Sandwich.Datum ε h Λ),
      LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D) = LinearMap.range (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D) ∧
      LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D) = LinearMap.range (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε h Λ _ _ D
  obtain ⟨hdom, -, hker, hs, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hμ : mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    refine mul_ne_zero hξ ?_
    intro h0; apply hν; rw [h0, map_zero]
  haveI : IsFractionRing O C := hv.isFractionRing
  have hFG := HodgeTateBound.mul_swap hμ D.G_mul_F
  exact ⟨ker_eq_range_of _ hs hker hξ hν (xi_mul_nu ε) hFG D.G_mul_F,
    ker_eq_range_of _ hs hker hξ hν (xi_mul_nu ε) D.G_mul_F hFG⟩

/- English proof (translation)
Establish `hp : ∀ n : ℕ, Matrix.toLin' (M ^ n) u = c ^ n • u`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, Matrix.toLin'_mul_apply, hu, map_smul, ih, smul_smul, pow_succ']`.

Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add q r hq hr => rw [map_add, map_add, LinearMap.add_apply, hq, hr, map_add, add_smul]`. Consider the case `monomial n r`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← algebraMap_smul C r (M ^ n), map_smul, LinearMap.smul_apply, hp, smul_smul]`.
-/
theorem aeval_eigen {R C : Type} [CommRing R] [Field C] [Algebra R C] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) C) (c : C) (u : Fin h → C) (hu : Matrix.toLin' M u = c • u)
    (Q : Polynomial R) : Matrix.toLin' (Polynomial.aeval M Q) u = Polynomial.aeval c Q • u := by
  have hp : ∀ n : ℕ, Matrix.toLin' (M ^ n) u = c ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Matrix.toLin'_mul_apply, hu, map_smul, ih, smul_smul, pow_succ']
  induction Q using Polynomial.induction_on' with
  | add q r hq hr => rw [map_add, map_add, LinearMap.add_apply, hq, hr, map_add, add_smul]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← algebraMap_smul C r (M ^ n), map_smul, LinearMap.smul_apply, hp, smul_smul]

/- English proof (translation)
Take `⟨m, hm, Q, hQ⟩` from `ha b`. Establish `hm' : algebraMap R C m ≠ 0` using `fun h0 => hm (hinj (by rw [h0, map_zero]))`. Establish `e` using `aeval_eigen (ρ a) (t a) u hu Q`. Rewrite `e` using `[Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, ← hQ, map_smul ρ, map_smul t, ← algebraMap_smul C m (ρ b), map_smul, LinearMap.smul_apply, Algebra.smul_def m (t b), ← smul_smul]`. Conclude with `smul_right_injective _ hm' e`.
-/
theorem eigen_all {R C Λ : Type} [CommRing R] [Field C] [Algebra R C] [CommRing Λ] [Algebra R Λ]
    {h : ℕ} (hinj : Function.Injective (algebraMap R C)) (a : Λ)
    (ha : ∀ b : Λ, ∃ m : R, m ≠ 0 ∧ ∃ Q : Polynomial R, m • b = Polynomial.aeval a Q)
    (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) C) (t : Λ →ₐ[R] C) (u : Fin h → C)
    (hu : Matrix.toLin' (ρ a) u = t a • u) (b : Λ) : Matrix.toLin' (ρ b) u = t b • u := by
  obtain ⟨m, hm, Q, hQ⟩ := ha b
  have hm' : algebraMap R C m ≠ 0 := fun h0 => hm (hinj (by rw [h0, map_zero]))
  have e := aeval_eigen (ρ a) (t a) u hu Q
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, ← hQ, map_smul ρ,
    map_smul t, ← algebraMap_smul C m (ρ b), map_smul, LinearMap.smul_apply, Algebra.smul_def m (t b),
    ← smul_smul] at e
  exact smul_right_injective _ hm' e

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `m hm`. Assume the negation of the conclusion as `h0`. Rewrite `hm` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`. Use `mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map j).ne_zero (pow_ne_zero _ ?_) hm` and prove the remaining obligations.

Conclude with `(Fact.out : p.Prime).ne_zero` after adjusting the coercions.
-/
theorem padic_injective {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [CharZero C] (j : ℤ_[p] →+* C) :
    Function.Injective j := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  refine mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map j).ne_zero (pow_ne_zero _ ?_) hm
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/- English proof (translation)
Establish `hint : IsIntegral ℤ_[p] a` using `IsIntegral.of_finite _ a`. Establish `h1 : Irreducible ((minpoly ℤ_[p] a).map (algebraMap ℤ_[p] ℚ_[p]))` using `((minpoly.monic hint).irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).1 (minpoly.irreducible hint)`. Establish `h2` using `h1.separable.map (f := IsFractionRing.lift (K := ℚ_[p]) (padic_injective j))`. Rewrite `h2` using `[Polynomial.map_map]`. Establish `e : (IsFractionRing.lift (K` using `ℚ_[p]) (padic_injective j)).comp (algebraMap ℤ_[p] ℚ_[p]) = j := by`.

Use extensionality with `x`. Conclude with `IsFractionRing.lift_algebraMap (padic_injective j) x`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem minpoly_separable {p : ℕ} [Fact p.Prime] {C Λ : Type} [Field C] [CharZero C] [CommRing Λ]
    [IsDomain Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (j : ℤ_[p] →+* C) (a : Λ) :
    ((minpoly ℤ_[p] a).map j).Separable := by
  have hint : IsIntegral ℤ_[p] a := IsIntegral.of_finite _ a
  have h1 : Irreducible ((minpoly ℤ_[p] a).map (algebraMap ℤ_[p] ℚ_[p])) :=
    ((minpoly.monic hint).irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).1
      (minpoly.irreducible hint)
  have h2 := h1.separable.map (f := IsFractionRing.lift (K := ℚ_[p]) (padic_injective j))
  rw [Polynomial.map_map] at h2
  have e : (IsFractionRing.lift (K := ℚ_[p]) (padic_injective j)).comp (algebraMap ℤ_[p] ℚ_[p]) = j := by
    ext x
    exact IsFractionRing.lift_algebraMap (padic_injective j) x
  rwa [e] at h2

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ τ hτ`. Take `⟨a, ha, hdeg⟩` from `exists_generator p Λ`. Use `letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (padicToO p O)).toAlgebra`. Set `t : Λ →ₐ[ℤ_[p]] C` to `{ (algebraMap O C).comp τ with commutes' := fun c => congrArg (algebraMap O C) (hτ c) }`. Establish `hsep` using `minpoly_separable (algebraMap ℤ_[p] C) a`.

Use `set f := (minpoly ℤ_[p] a).map (algebraMap ℤ_[p] C) with hf`. Establish `hroot : f.IsRoot (t a)`. Rewrite using `[Polynomial.IsRoot, hf, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Take `⟨g, hg⟩` from `Polynomial.dvd_iff_isRoot.2 hroot`. Establish `hg0 : g.eval (t a) ≠ 0`.

Introduce `h0`. Take `⟨g', hg'⟩` from `Polynomial.dvd_iff_isRoot.2 h0`. Conclude with `Polynomial.not_isUnit_X_sub_C _ (hsep.squarefree _ ⟨g', by rw [hg, hg', mul_assoc]⟩)`. Use `⟨a, Polynomial.C (g.eval (t a))⁻¹ * g, fun h ρ h1 hmul hadd hsc u => ?_⟩` and prove the remaining obligations. Establish `h0 : ρ 0 = 0` using `by simpa using hadd 0 0`.

Set `R : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) C` to `{ toFun := fun b => (ρ b).map (algebraMap O C) map_one' := by simp [h1] map_mul' := fun x y => by simp [hmul, Matrix.map_mul] map_zero' := by simp [h0] map_add' := fun x y => by simp [hadd, Matrix.map_add] commutes' := fun c => by`. Rewrite using `[hsc]`. Use extensionality with `i k`. Apply the tactic sequence `by_cases hik : i = k <;> simp [hik, Matrix.algebraMap_matrix_apply]`. Use `rfl }`.

Establish `memE : ∀ w : Fin h → C, w ∈ eig C ρ τ ↔ ∀ b, Matrix.toLin' (R b) w = t b • w`. Introduce `w`. Simplify using `only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Matrix.toLin' (Polynomial.aeval (R a) _) u ∈ _ ∧ (_ → Matrix.toLin' (Polynomial.aeval (R a) _) u = u)`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[memE]`. Apply `eigen_all (padic_injective _) a ha R t` to reduce the goal to its premises. Establish `hz : Polynomial.aeval (R a) f = 0`. Rewrite using `[hf, Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`.

Establish `e : R a * Polynomial.aeval (R a) (Polynomial.C (g.eval (t a))⁻¹ * g) = t a • Polynomial.aeval (R a) (Polynomial.C (g.eval (t a))⁻¹ * g)`. Rewrite `hz` using `[hg, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def]`. Rewrite using `[map_mul, Polynomial.aeval_C, ← Algebra.smul_def, mul_smul_comm, hz, smul_comm]`. Rewrite using `[← Matrix.toLin'_mul_apply, e, map_smul, LinearMap.smul_apply]`. Introduce `hu`.

Rewrite using `[aeval_eigen _ _ u ((memE u).1 hu a)]`. Simplify using `[inv_mul_cancel₀ hg0]`.
-/
theorem exists_projector : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (τ : Λ →+* O),
      (∀ c : ℤ_[p], τ (algebraMap ℤ_[p] Λ c) = GlobalTheory.Sandwich.padicToO p O c) →
      ∃ (a : Λ) (P : Polynomial C), ∀ (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O),
        (ρ 1 = 1) → (∀ x y, ρ (x * y) = ρ x * ρ y) → (∀ x y, ρ (x + y) = ρ x + ρ y) →
        (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = GlobalTheory.Sandwich.padicToO p O c • (1 : Matrix (Fin h) (Fin h) O)) →
        ∀ u : Fin h → C,
          Matrix.toLin' (Polynomial.aeval ((ρ a).map (algebraMap O C)) P) u ∈ GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.eig C ρ τ ∧
          (u ∈ GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.eig C ρ τ → Matrix.toLin' (Polynomial.aeval ((ρ a).map (algebraMap O C)) P) u = u) := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ τ hτ
  obtain ⟨a, ha, hdeg⟩ := exists_generator p Λ
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (padicToO p O)).toAlgebra
  let t : Λ →ₐ[ℤ_[p]] C := { (algebraMap O C).comp τ with
    commutes' := fun c => congrArg (algebraMap O C) (hτ c) }
  have hsep := minpoly_separable (algebraMap ℤ_[p] C) a
  set f := (minpoly ℤ_[p] a).map (algebraMap ℤ_[p] C) with hf
  have hroot : f.IsRoot (t a) := by
    rw [Polynomial.IsRoot, hf, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply,
      minpoly.aeval, map_zero]
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.2 hroot
  have hg0 : g.eval (t a) ≠ 0 := by
    intro h0
    obtain ⟨g', hg'⟩ := Polynomial.dvd_iff_isRoot.2 h0
    exact Polynomial.not_isUnit_X_sub_C _ (hsep.squarefree _ ⟨g', by rw [hg, hg', mul_assoc]⟩)
  refine ⟨a, Polynomial.C (g.eval (t a))⁻¹ * g, fun h ρ h1 hmul hadd hsc u => ?_⟩
  have h0 : ρ 0 = 0 := by simpa using hadd 0 0
  let R : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) C :=
    { toFun := fun b => (ρ b).map (algebraMap O C)
      map_one' := by simp [h1]
      map_mul' := fun x y => by simp [hmul, Matrix.map_mul]
      map_zero' := by simp [h0]
      map_add' := fun x y => by simp [hadd, Matrix.map_add]
      commutes' := fun c => by
        rw [hsc]
        ext i k
        by_cases hik : i = k <;> simp [hik, Matrix.algebraMap_matrix_apply]
        rfl }
  have memE : ∀ w : Fin h → C, w ∈ eig C ρ τ ↔ ∀ b, Matrix.toLin' (R b) w = t b • w := by
    intro w
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    rfl
  change Matrix.toLin' (Polynomial.aeval (R a) _) u ∈ _ ∧
    (_ → Matrix.toLin' (Polynomial.aeval (R a) _) u = u)
  constructor
  · rw [memE]
    apply eigen_all (padic_injective _) a ha R t
    have hz : Polynomial.aeval (R a) f = 0 := by
      rw [hf, Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have e : R a * Polynomial.aeval (R a) (Polynomial.C (g.eval (t a))⁻¹ * g) =
        t a • Polynomial.aeval (R a) (Polynomial.C (g.eval (t a))⁻¹ * g) := by
      rw [hg, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_mul, sub_eq_zero,
        ← Algebra.smul_def] at hz
      rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def, mul_smul_comm, hz, smul_comm]
    rw [← Matrix.toLin'_mul_apply, e, map_smul, LinearMap.smul_apply]
  · intro hu
    rw [aeval_eigen _ _ u ((memE u).1 hu a)]
    simp [inv_mul_cancel₀ hg0]

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ N h hh ρ τ hτ`. Take `⟨a, ha, hdeg⟩` from `exists_generator p Λ`. Establish `hch` using `charpoly_action_eq_pow p Λ a hdeg N h hh ρ`. Use `letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (padicToO p O)).toAlgebra`. Set `t : Λ →ₐ[ℤ_[p]] C` to `{ (algebraMap O C).comp τ with commutes' := fun c => congrArg (algebraMap O C) (hτ c) }`.

Set `R : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) C` to `(Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ`. Establish `hsep` using `minpoly_separable (algebraMap ℤ_[p] C) a`. Use `set f := (minpoly ℤ_[p] a).map (algebraMap ℤ_[p] C) with hf`. Establish `hroot : f.IsRoot (t a)`. Rewrite using `[Polynomial.IsRoot, hf, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`.

Establish `he : eig C (fun a => (ρ a).map (padicToO p O)) τ = Module.End.eigenspace (Matrix.toLin' (R a)) (t a)`. Use extensionality with `w`. Simplify using `only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Conclude with `⟨fun H => H a, fun H b => eigen_all (padic_injective _) a ha R t w H b⟩`. Establish `hz : Polynomial.aeval (R a) f = 0`.

Rewrite using `[hf, Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hz' : Polynomial.aeval (Matrix.toLin' (R a)) f = 0`. Establish `h3` using `Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := C) (n := Fin h)) (R a) f`. Rewrite `h3` using `[hz, map_zero]`. Conclude with `h3`.

Establish `hss` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree hz'`. Establish `hcp : (R a).charpoly = f ^ N`. Rewrite using `[hf, ← Polynomial.map_pow, ← hch, ← Matrix.charpoly_map]`. Both sides reduce to the same expression. Rewrite using `[he, ← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', hcp, ← Polynomial.count_roots, Polynomial.roots_pow, Multiset.count_nsmul, Multiset.count_eq_one_of_mem (Polynomial.nodup_roots hsep) ((Polynomial.mem_ro …`.
-/
theorem finrank_eig_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (ρT : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (τ : Λ →+* O),
      (∀ c : ℤ_[p], τ (algebraMap ℤ_[p] Λ c) = GlobalTheory.Sandwich.padicToO p O c) →
      Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.eig C (fun a => (ρT a).map (GlobalTheory.Sandwich.padicToO p O)) τ) = N := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ N h hh ρ τ hτ
  classical
  obtain ⟨a, ha, hdeg⟩ := exists_generator p Λ
  have hch := charpoly_action_eq_pow p Λ a hdeg N h hh ρ
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (padicToO p O)).toAlgebra
  let t : Λ →ₐ[ℤ_[p]] C := { (algebraMap O C).comp τ with
    commutes' := fun c => congrArg (algebraMap O C) (hτ c) }
  let R : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) C := (Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ
  have hsep := minpoly_separable (algebraMap ℤ_[p] C) a
  set f := (minpoly ℤ_[p] a).map (algebraMap ℤ_[p] C) with hf
  have hroot : f.IsRoot (t a) := by
    rw [Polynomial.IsRoot, hf, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply,
      minpoly.aeval, map_zero]
  have he : eig C (fun a => (ρ a).map (padicToO p O)) τ =
      Module.End.eigenspace (Matrix.toLin' (R a)) (t a) := by
    ext w
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    exact ⟨fun H => H a, fun H b => eigen_all (padic_injective _) a ha R t w H b⟩
  have hz : Polynomial.aeval (R a) f = 0 := by
    rw [hf, Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hz' : Polynomial.aeval (Matrix.toLin' (R a)) f = 0 := by
    have h3 := Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := C) (n := Fin h)) (R a) f
    rw [hz, map_zero] at h3
    exact h3
  have hss := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree hz'
  have hcp : (R a).charpoly = f ^ N := by
    rw [hf, ← Polynomial.map_pow, ← hch, ← Matrix.charpoly_map]; rfl
  rw [he, ← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', hcp, ← Polynomial.count_roots,
    Polynomial.roots_pow, Multiset.count_nsmul,
    Multiset.count_eq_one_of_mem (Polynomial.nodup_roots hsep)
      ((Polynomial.mem_roots hsep.ne_zero).2 hroot), mul_one]

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ`. Establish `hτ : ∀ c : ℤ_[p], τ (algebraMap ℤ_[p] Λ c) = padicToO p O c` using `fun c => by`. Establish `e` using `ringHom_padicInt_eq p O (τ.comp (algebraMap ℤ_[p] Λ))`. Conclude with `congrArg (fun f : ℤ_[p] →+* O => f c) e`. Take `⟨hbH, haT, hsT, hsH⟩` from `datum_equivariant p C v O hv ε hε h Λ D`.

Take `⟨hkb, hka⟩` from `hodgeTate_exact p C v O hv ε hε h Λ D`. Take `⟨a, P, hP⟩` from `exists_projector p C v O hv Λ τ hτ`. Establish `hPT` using `hP h (actT D) (by simp [actT]) (by intro x y; simp [actT, Matrix.map_mul]) (by intro x y; simp [actT, Matrix.map_add]) hsT`. Establish `hPH` using `hP h (actH D) (by simp [actH]) (by intro x y; simp [actH, Matrix.map_mul]) (by intro x y; simp [actH, Matrix.map_add]) hsH`. Establish `memE : ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (u : Fin h → C), u ∈ eig C ρ τ ↔ ∀ b, Matrix.toLin' ((ρ b).map (algebraMap O C)) u = algebraMap O C (τ b) • u`.

Introduce `ρ u`. Simplify using `[eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Use `set V := eig C (actT D) τ with hVdef`. Use `set W := eig C (actH D) τ with hWdef`. Use `set Fc : Matrix (Fin h) (Fin h) C := D.F.map ((algebraMap O C).comp (fontaineTheta O p)) with hFc`.

Use `set Gc : Matrix (Fin h) (Fin h) C := D.G.map ((algebraMap O C).comp (fontaineTheta O p)) with hGc`. Establish `hal : alC C D = Matrix.toLin' Fc` using `rfl`. Establish `hbl : bC C D = Matrix.toLin' Gc` using `rfl`. Establish `bmap : ∀ y ∈ W, bC C D y ∈ V`. Introduce `y hy`.

Rewrite `hy`, the goal using `[memE]`. Introduce `b`. Establish `e` using `congrArg (fun f => f y) (hbH b)`. Simplify using `only [LinearMap.comp_apply] at e`. Rewrite using `[← e, hy b, map_smul]`.

Establish `amap : ∀ x ∈ V, alC C D x ∈ W`. Introduce `x hx`. Rewrite `hx`, the goal using `[memE]`. Introduce `b`. Establish `e` using `congrArg (fun f => f x) (haT b)`.

Simplify using `only [LinearMap.comp_apply] at e`. Rewrite using `[← e, hx b, map_smul]`. Establish `semi : ∀ (X M1 M2 : Matrix (Fin h) (Fin h) C), X * M1 = M2 * X → ∀ Q : Polynomial C, X * Polynomial.aeval M1 Q = Polynomial.aeval M2 Q * X`. Introduce `X M1 M2 hX Q`. Proceed by induction on `Q using Polynomial.induction_on' with`.

Consider the case `add q r hq hr => simp [mul_add, add_mul, hq, hr]`. Consider the case `monomial n c`. Establish `e : X * M1 ^ n = M2 ^ n * X` using `(SemiconjBy.pow_right hX n)`. Simplify using `only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, e]`. Use `set MT : Matrix (Fin h) (Fin h) C := (actT D a).map (algebraMap O C) with hMT`.

Use `set MH : Matrix (Fin h) (Fin h) C := (actH D a).map (algebraMap O C) with hMH`. Establish `sG : Gc * MH = MT * Gc`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul, ← hbl]`. Conclude with `hbH a`.

Establish `sF : Fc * MT = MH * Fc`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul, ← hal]`. Conclude with `haT a`. Establish `pG : ∀ w, bC C D (Matrix.toLin' (Polynomial.aeval MH P) w) = Matrix.toLin' (Polynomial.aeval MT P) (bC C D w)`.

Introduce `w`. Establish `e` using `congrArg (fun M => Matrix.toLin' M w) (semi Gc MH MT sG P)`. Simplify `e` using `only [Matrix.toLin'_mul, LinearMap.comp_apply, hbl]`. Establish `pF : ∀ w, alC C D (Matrix.toLin' (Polynomial.aeval MT P) w) = Matrix.toLin' (Polynomial.aeval MH P) (alC C D w)`. Introduce `w`.

Establish `e` using `congrArg (fun M => Matrix.toLin' M w) (semi Fc MT MH sF P)`. Simplify `e` using `only [Matrix.toLin'_mul, LinearMap.comp_apply, hal]`. Establish `c3 : ∀ y ∈ W, bC C D y = 0 → ∃ x ∈ V, alC C D x = y`. Introduce `y hy hy0`. Establish `: y ∈ LinearMap.range (alC C D)` using `by rw [← hkb]; exact hy0`.

Take `⟨x0, rfl⟩` from `this`. Conclude with `⟨_, (hPT x0).1, by rw [pF]; exact (hPH _).2 hy⟩`. Establish `c5 : ∀ z ∈ V, z ∈ LinearMap.range (bC C D) → ∃ y ∈ W, bC C D y = z`. Introduce `z hz hz'`. Take `⟨w0, rfl⟩` from `hz'`.

Conclude with `⟨_, (hPH w0).1, by rw [pG]; exact (hPT _).2 hz⟩`. Set `α : V →ₗ[C] W` to `(alC C D).restrict amap`. Set `β : W →ₗ[C] V` to `(bC C D).restrict bmap`. Establish `h1 : LinearMap.ker α = LinearMap.range β`. Use extensionality with `x`.

Simplify using `only [LinearMap.mem_ker, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : alC C D x = 0` using `by simpa [α, Subtype.ext_iff] using hx`. Establish `: (x : Fin h → C) ∈ LinearMap.range (bC C D)` using `by rw [← hka]; exact hx'`.

Take `⟨y, hy, hyx⟩` from `c5 x x.2 this`. Conclude with `⟨⟨y, hy⟩, Subtype.ext hyx⟩`. Introduce and unpack `⟨y, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show alC C D (bC C D y) = 0`.

Establish `: bC C D y ∈ LinearMap.ker (alC C D)` using `by rw [hka]; exact ⟨y, rfl⟩`. Conclude with `this`. Establish `h2 : LinearMap.ker β = LinearMap.range α`. Use extensionality with `y`. Simplify using `only [LinearMap.mem_ker, LinearMap.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy' : bC C D y = 0` using `by simpa [β, Subtype.ext_iff] using hy`. Take `⟨x, hx, hxy⟩` from `c3 y y.2 hy'`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxy⟩`.

Introduce and unpack `⟨x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show bC C D (alC C D x) = 0`. Establish `: alC C D x ∈ LinearMap.ker (bC C D)` using `by rw [hkb]; exact ⟨x, rfl⟩`. Conclude with `this`.

Establish `hV : Module.finrank C V = N` using `finrank_eig_eq p C v O hv Λ N h hh D.ρT τ hτ`. Establish `hrange : (LinearMap.range β).map V.subtype = LinearMap.range (bC C D) ⊓ V`. Use extensionality with `z`. Simplify using `only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_inf, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, ⟨y, rfl⟩, rfl⟩`. Conclude with `⟨⟨y, rfl⟩, (β y).2⟩`. Introduce and unpack `⟨hz, hzV⟩`. Take `⟨y, hy, hyz⟩` from `c5 z hzV hz`. Conclude with `⟨⟨z, hzV⟩, ⟨⟨y, hy⟩, Subtype.ext hyz⟩, rfl⟩`.

Establish `ha : D.lieRank τ = Module.finrank C (LinearMap.range β)`. Rewrite using `[lieRank_eq_finrank p C v O hv ε h Λ D τ, ← hrange, Submodule.finrank_map_subtype_eq]`. Use `haveI : FiniteDimensional C W := inferInstance`. Take `⟨hex, hbij⟩` from `exists_unique_wedge_map C V W N hV α β h1 h2 (D.lieRank τ) ha`. Establish `key : ∀ ι : ⋀[C]^N V →ₗ[C] ⋀[C]^N W, IsIota C D τ N ι ↔ ∀ (x : Fin N → V) (y : Fin N → W), (∀ i : Fin N, (i : ℕ) < D.lieRank τ → x i = β (y i)) → (∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) → y i = α (x i)) → ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y`.

Introduce `ι`. Prove the components needed by the constructor for the conclusion. Introduce `H x y e1 e2`. Conclude with `H x y (fun i hi => congrArg Subtype.val (e1 i hi)) (fun i hi => congrArg Subtype.val (e2 i hi))`. Introduce `H x y e1 e2`.

Conclude with `H x y (fun i hi => Subtype.ext (e1 i hi)) (fun i hi => Subtype.ext (e2 i hi))`. Take `⟨ι, hι, huniq⟩` from `hex`. Conclude with `⟨⟨ι, (key ι).2 hι, fun ι' h' => huniq ι' ((key ι').1 h')⟩, fun ι' h' => hbij ι' ((key ι').1 h')⟩`.
-/
theorem iota_existsUnique_bijective : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (D : GlobalTheory.Sandwich.Datum ε h Λ) (τ : Λ →+* O),
        (∃! ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι) ∧
          ∀ ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι → Function.Bijective ι := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ
  classical
  have hτ : ∀ c : ℤ_[p], τ (algebraMap ℤ_[p] Λ c) = padicToO p O c := fun c => by
    have e := ringHom_padicInt_eq p O (τ.comp (algebraMap ℤ_[p] Λ))
    exact congrArg (fun f : ℤ_[p] →+* O => f c) e
  obtain ⟨hbH, haT, hsT, hsH⟩ := datum_equivariant p C v O hv ε hε h Λ D
  obtain ⟨hkb, hka⟩ := hodgeTate_exact p C v O hv ε hε h Λ D
  obtain ⟨a, P, hP⟩ := exists_projector p C v O hv Λ τ hτ
  have hPT := hP h (actT D) (by simp [actT]) (by intro x y; simp [actT, Matrix.map_mul])
    (by intro x y; simp [actT, Matrix.map_add]) hsT
  have hPH := hP h (actH D) (by simp [actH]) (by intro x y; simp [actH, Matrix.map_mul])
    (by intro x y; simp [actH, Matrix.map_add]) hsH
  have memE : ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (u : Fin h → C), u ∈ eig C ρ τ ↔
      ∀ b, Matrix.toLin' ((ρ b).map (algebraMap O C)) u = algebraMap O C (τ b) • u := by
    intro ρ u; simp [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  set V := eig C (actT D) τ with hVdef
  set W := eig C (actH D) τ with hWdef
  set Fc : Matrix (Fin h) (Fin h) C := D.F.map ((algebraMap O C).comp (fontaineTheta O p)) with hFc
  set Gc : Matrix (Fin h) (Fin h) C := D.G.map ((algebraMap O C).comp (fontaineTheta O p)) with hGc
  have hal : alC C D = Matrix.toLin' Fc := rfl
  have hbl : bC C D = Matrix.toLin' Gc := rfl
  have bmap : ∀ y ∈ W, bC C D y ∈ V := by
    intro y hy; rw [memE] at hy ⊢; intro b
    have e := congrArg (fun f => f y) (hbH b)
    simp only [LinearMap.comp_apply] at e
    rw [← e, hy b, map_smul]
  have amap : ∀ x ∈ V, alC C D x ∈ W := by
    intro x hx; rw [memE] at hx ⊢; intro b
    have e := congrArg (fun f => f x) (haT b)
    simp only [LinearMap.comp_apply] at e
    rw [← e, hx b, map_smul]
  have semi : ∀ (X M1 M2 : Matrix (Fin h) (Fin h) C), X * M1 = M2 * X →
      ∀ Q : Polynomial C, X * Polynomial.aeval M1 Q = Polynomial.aeval M2 Q * X := by
    intro X M1 M2 hX Q
    induction Q using Polynomial.induction_on' with
    | add q r hq hr => simp [mul_add, add_mul, hq, hr]
    | monomial n c =>
      have e : X * M1 ^ n = M2 ^ n * X := (SemiconjBy.pow_right hX n)
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        mul_smul_comm, e]
  set MT : Matrix (Fin h) (Fin h) C := (actT D a).map (algebraMap O C) with hMT
  set MH : Matrix (Fin h) (Fin h) C := (actH D a).map (algebraMap O C) with hMH
  have sG : Gc * MH = MT * Gc := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, ← hbl]; exact hbH a
  have sF : Fc * MT = MH * Fc := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, ← hal]; exact haT a
  have pG : ∀ w, bC C D (Matrix.toLin' (Polynomial.aeval MH P) w) =
      Matrix.toLin' (Polynomial.aeval MT P) (bC C D w) := by
    intro w
    have e := congrArg (fun M => Matrix.toLin' M w) (semi Gc MH MT sG P)
    simpa only [Matrix.toLin'_mul, LinearMap.comp_apply, hbl] using e
  have pF : ∀ w, alC C D (Matrix.toLin' (Polynomial.aeval MT P) w) =
      Matrix.toLin' (Polynomial.aeval MH P) (alC C D w) := by
    intro w
    have e := congrArg (fun M => Matrix.toLin' M w) (semi Fc MT MH sF P)
    simpa only [Matrix.toLin'_mul, LinearMap.comp_apply, hal] using e

  have c3 : ∀ y ∈ W, bC C D y = 0 → ∃ x ∈ V, alC C D x = y := by
    intro y hy hy0
    have : y ∈ LinearMap.range (alC C D) := by rw [← hkb]; exact hy0
    obtain ⟨x0, rfl⟩ := this
    exact ⟨_, (hPT x0).1, by rw [pF]; exact (hPH _).2 hy⟩
  have c5 : ∀ z ∈ V, z ∈ LinearMap.range (bC C D) → ∃ y ∈ W, bC C D y = z := by
    intro z hz hz'
    obtain ⟨w0, rfl⟩ := hz'
    exact ⟨_, (hPH w0).1, by rw [pG]; exact (hPT _).2 hz⟩
  let α : V →ₗ[C] W := (alC C D).restrict amap
  let β : W →ₗ[C] V := (bC C D).restrict bmap
  have h1 : LinearMap.ker α = LinearMap.range β := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      have hx' : alC C D x = 0 := by simpa [α, Subtype.ext_iff] using hx
      have : (x : Fin h → C) ∈ LinearMap.range (bC C D) := by rw [← hka]; exact hx'
      obtain ⟨y, hy, hyx⟩ := c5 x x.2 this
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      show alC C D (bC C D y) = 0
      have : bC C D y ∈ LinearMap.ker (alC C D) := by rw [hka]; exact ⟨y, rfl⟩
      exact this
  have h2 : LinearMap.ker β = LinearMap.range α := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have hy' : bC C D y = 0 := by simpa [β, Subtype.ext_iff] using hy
      obtain ⟨x, hx, hxy⟩ := c3 y y.2 hy'
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      show bC C D (alC C D x) = 0
      have : alC C D x ∈ LinearMap.ker (bC C D) := by rw [hkb]; exact ⟨x, rfl⟩
      exact this
  have hV : Module.finrank C V = N := finrank_eig_eq p C v O hv Λ N h hh D.ρT τ hτ
  have hrange : (LinearMap.range β).map V.subtype = LinearMap.range (bC C D) ⊓ V := by
    ext z
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, (β y).2⟩
    · rintro ⟨hz, hzV⟩
      obtain ⟨y, hy, hyz⟩ := c5 z hzV hz
      exact ⟨⟨z, hzV⟩, ⟨⟨y, hy⟩, Subtype.ext hyz⟩, rfl⟩
  have ha : D.lieRank τ = Module.finrank C (LinearMap.range β) := by
    rw [lieRank_eq_finrank p C v O hv ε h Λ D τ, ← hrange, Submodule.finrank_map_subtype_eq]
  haveI : FiniteDimensional C W := inferInstance
  obtain ⟨hex, hbij⟩ := exists_unique_wedge_map C V W N hV α β h1 h2 (D.lieRank τ) ha
  have key : ∀ ι : ⋀[C]^N V →ₗ[C] ⋀[C]^N W, IsIota C D τ N ι ↔
      ∀ (x : Fin N → V) (y : Fin N → W),
        (∀ i : Fin N, (i : ℕ) < D.lieRank τ → x i = β (y i)) →
        (∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) → y i = α (x i)) →
        ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y := by
    intro ι
    constructor
    · intro H x y e1 e2
      exact H x y (fun i hi => congrArg Subtype.val (e1 i hi)) (fun i hi => congrArg Subtype.val (e2 i hi))
    · intro H x y e1 e2
      exact H x y (fun i hi => Subtype.ext (e1 i hi)) (fun i hi => Subtype.ext (e2 i hi))
  obtain ⟨ι, hι, huniq⟩ := hex
  exact ⟨⟨ι, (key ι).2 hι, fun ι' h' => huniq ι' ((key ι').1 h')⟩, fun ι' h' => hbij ι' ((key ι').1 h')⟩

end GlobalTheory.IotaDet
