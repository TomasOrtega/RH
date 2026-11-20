import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.SteinFibre

/- English proof (translation)
Use `haveI : y.asIdeal.IsPrime := y.isPrime`. Use `letI : Algebra Γ(X, W) (X.presheaf.stalk (hW.fromSpec y)) := X.presheaf.algebra_section_stalk ⟨_, hy⟩`. Use `haveI : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec y)) y.asIdeal := hW.isLocalization_stalk' y hy`. Establish `h` using `IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (hW.fromSpec y)) y.asIdeal (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t)`. Rewrite using `[mem_under_iff, ← X.presheaf.germ_res_apply (homOfLE le_top) _ hy t]`.

Express the relevant statement in the definitionally equal form `¬ IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk (hW.fromSpec y)) _) ↔ _`. Rewrite using `[h]`. Simplify using `[Ideal.primeCompl]`.
-/
theorem mem_under_fromSpec_iff {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    (y : Spec Γ(X, W)) (hy : hW.fromSpec y ∈ W) (t : Γ(X, ⊤)) :
    t ∈ under (hW.fromSpec y) ↔ X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t ∈ y.asIdeal := by
  haveI : y.asIdeal.IsPrime := y.isPrime
  letI : Algebra Γ(X, W) (X.presheaf.stalk (hW.fromSpec y)) :=
    X.presheaf.algebra_section_stalk ⟨_, hy⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec y)) y.asIdeal :=
    hW.isLocalization_stalk' y hy
  have h := IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (hW.fromSpec y)) y.asIdeal
    (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t)
  rw [mem_under_iff, ← X.presheaf.germ_res_apply (homOfLE le_top) _ hy t]
  change ¬ IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk (hW.fromSpec y)) _) ↔ _
  rw [h]
  simp [Ideal.primeCompl]

/- English proof (translation)
Rewrite using `[X.mem_basicOpen t _ trivial]`. Establish `hne : X.presheaf.germ ⊤ (genericPoint X) trivial t ≠ 0`. Introduce `h0`. Apply `ht` to reduce the goal to its premises. Conclude with `germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial (h0.trans (map_zero _).symm)`.

Conclude with `(isUnit_iff_ne_zero (G₀ := X.functionField)).2 hne`.
-/
theorem genericPoint_mem_basicOpen {X : Scheme.{0}} [IsIntegral X] (t : Γ(X, ⊤)) (ht : t ≠ 0) :
    genericPoint X ∈ X.basicOpen t := by
  rw [X.mem_basicOpen t _ trivial]
  have hne : X.presheaf.germ ⊤ (genericPoint X) trivial t ≠ 0 := by
    intro h0
    apply ht
    exact germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial (h0.trans (map_zero _).symm)
  exact (isUnit_iff_ne_zero (G₀ := X.functionField)).2 hne

/- English proof (translation)
Introduce `h0`. Establish `hmax : IsMax z` using `Order.coheight_eq_zero.1 h0`. Establish `hg : z ⤳ genericPoint X` using `hmax (genericPoint_specializes z)`. Establish `heq : z = genericPoint X` using `(hg.antisymm (genericPoint_specializes z)).eq`. Use `genericPoint_mem_basicOpen t ht` as an intermediate fact.

Rewrite `this` using `[← heq, X.mem_basicOpen t z trivial]`. Conclude with `(mem_under_iff z t).1 hz this`.
-/
theorem coheight_ne_zero_of_mem_under {X : Scheme.{0}} [IsIntegral X] {t : Γ(X, ⊤)} (ht : t ≠ 0)
    {z : X} (hz : t ∈ under z) : Order.coheight z ≠ 0 := by
  intro h0
  have hmax : IsMax z := Order.coheight_eq_zero.1 h0
  have hg : z ⤳ genericPoint X := hmax (genericPoint_specializes z)
  have heq : z = genericPoint X := (hg.antisymm (genericPoint_specializes z)).eq
  have := genericPoint_mem_basicOpen t ht
  rw [← heq, X.mem_basicOpen t z trivial] at this
  exact (mem_under_iff z t).1 hz this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hne : ((X.basicOpen t : X.Opens) : Set X).Nonempty` using `⟨genericPoint X, genericPoint_mem_basicOpen t ht⟩`. Use `(GlobalTheory.ZH.finite_notMem_coheight_le_one (X.basicOpen t) hne).subset ?_` and prove the remaining obligations. Introduce and unpack `z ⟨hz, h1⟩`. Use `⟨fun hb => ?_, h1.le⟩` and prove the remaining obligations.

Rewrite `hb` using `[X.mem_basicOpen t z trivial]`. Conclude with `(mem_under_iff z t).1 (hz ▸ htP) hb`. Introduce `x hx`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Use `haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`.

Take `⟨y, rfl⟩ : x ∈ Set.range hW.fromSpec` from `by rw [hW.range_fromSpec]; exact hxW`. Use `set tW := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t with htW`. Establish `hty : tW ∈ y.asIdeal` using `(mem_under_fromSpec_iff hW y hxW t).1 (hx ▸ htP)`. Use `haveI : y.asIdeal.IsPrime := y.isPrime`. Take `⟨q, hqmin, hqy⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {tW}) (J := y.asIdeal) ((Ideal.span_singleton_le_iff_mem _).2 hty)`.

Use `haveI hqp : q.IsPrime := hqmin.1.1`. Set `z : Spec Γ(X, W)` to `⟨q, hqp⟩`. Establish `hzW : hW.fromSpec z ∈ W`. Rewrite using `[← SetLike.mem_coe, ← hW.range_fromSpec]`. Conclude with `⟨z, rfl⟩`.

Establish `htq : t ∈ under (hW.fromSpec z)` using `(mem_under_fromSpec_iff hW z hzW t).2 (hqmin.1.2 (Ideal.mem_span_singleton_self tW))`. Establish `hsp : hW.fromSpec z ⤳ hW.fromSpec y` using `((PrimeSpectrum.le_iff_specializes z y).1 hqy).map hW.fromSpec.continuous`. Establish `hle : Order.coheight (hW.fromSpec z) ≤ 1`. Use `letI : Algebra Γ(X, W) (X.presheaf.stalk (hW.fromSpec z)) := X.presheaf.algebra_section_stalk ⟨_, hzW⟩`. Use `haveI : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec z)) q := hW.isLocalization_stalk' z hzW`.

Establish `e` using `IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk (hW.fromSpec z))`. Rewrite `e` using `[ringKrullDim_stalk_eq_coheight]`. Establish `hk : q.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hqmin`. Establish `: ((Order.coheight (hW.fromSpec z) : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞)`. Rewrite using `[e]`.

Conclude with `hk` after adjusting the coercions. Conclude with `this` after adjusting the coercions. Establish `h1 : Order.coheight (hW.fromSpec z) = 1` using `le_antisymm hle (ENat.one_le_iff_ne_zero.2 (coheight_ne_zero_of_mem_under ht htq))`. Establish `hne : under (hW.fromSpec z) ≠ ⊥` using `fun h => ht (by simpa [h] using htq)`. Establish `hmax : (under (hW.fromSpec z)).IsMaximal` using `Ring.DimensionLEOne.maximalOfPrime hne inferInstance`.

Establish `hzP : under (hW.fromSpec z) = P` using `hmax.eq_of_le hP.ne_top (hx ▸ under_le_of_specializes hsp)`. Conclude with `⟨_, hzP, h1, hsp⟩`.
-/
theorem finite_coheight_one_and_exists_specializes (X : Scheme.{0}) [IsIntegral X] [IsNoetherian X]
    [Ring.DimensionLEOne Γ(X, ⊤)] (P : Ideal Γ(X, ⊤)) (t : Γ(X, ⊤)) (hP : P.IsMaximal)
    (htP : t ∈ P) (ht : t ≠ 0) :
    {z : X | under z = P ∧ Order.coheight z = 1}.Finite ∧
      ∀ x : X, under x = P → ∃ z : X, under z = P ∧ Order.coheight z = 1 ∧ z ⤳ x := by
  constructor
  · have hne : ((X.basicOpen t : X.Opens) : Set X).Nonempty :=
      ⟨genericPoint X, genericPoint_mem_basicOpen t ht⟩
    refine (GlobalTheory.ZH.finite_notMem_coheight_le_one (X.basicOpen t) hne).subset ?_
    rintro z ⟨hz, h1⟩
    refine ⟨fun hb => ?_, h1.le⟩
    rw [X.mem_basicOpen t z trivial] at hb
    exact (mem_under_iff z t).1 (hz ▸ htP) hb
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    obtain ⟨y, rfl⟩ : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hxW
    set tW := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t with htW
    have hty : tW ∈ y.asIdeal := (mem_under_fromSpec_iff hW y hxW t).1 (hx ▸ htP)
    haveI : y.asIdeal.IsPrime := y.isPrime
    obtain ⟨q, hqmin, hqy⟩ := Ideal.exists_minimalPrimes_le
      (I := Ideal.span {tW}) (J := y.asIdeal) ((Ideal.span_singleton_le_iff_mem _).2 hty)
    haveI hqp : q.IsPrime := hqmin.1.1
    let z : Spec Γ(X, W) := ⟨q, hqp⟩
    have hzW : hW.fromSpec z ∈ W := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]; exact ⟨z, rfl⟩
    have htq : t ∈ under (hW.fromSpec z) :=
      (mem_under_fromSpec_iff hW z hzW t).2 (hqmin.1.2 (Ideal.mem_span_singleton_self tW))
    have hsp : hW.fromSpec z ⤳ hW.fromSpec y :=
      ((PrimeSpectrum.le_iff_specializes z y).1 hqy).map hW.fromSpec.continuous

    have hle : Order.coheight (hW.fromSpec z) ≤ 1 := by
      letI : Algebra Γ(X, W) (X.presheaf.stalk (hW.fromSpec z)) :=
        X.presheaf.algebra_section_stalk ⟨_, hzW⟩
      haveI : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec z)) q :=
        hW.isLocalization_stalk' z hzW
      have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk (hW.fromSpec z))
      rw [ringKrullDim_stalk_eq_coheight] at e
      have hk : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hqmin
      have : ((Order.coheight (hW.fromSpec z) : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [e]; exact_mod_cast hk
      exact_mod_cast this
    have h1 : Order.coheight (hW.fromSpec z) = 1 :=
      le_antisymm hle (ENat.one_le_iff_ne_zero.2 (coheight_ne_zero_of_mem_under ht htq))

    have hne : under (hW.fromSpec z) ≠ ⊥ := fun h => ht (by simpa [h] using htq)
    have hmax : (under (hW.fromSpec z)).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    have hzP : under (hW.fromSpec z) = P :=
      hmax.eq_of_le hP.ne_top (hx ▸ under_le_of_specializes hsp)
    exact ⟨_, hzP, h1, hsp⟩

end GlobalTheory.SteinFibre
