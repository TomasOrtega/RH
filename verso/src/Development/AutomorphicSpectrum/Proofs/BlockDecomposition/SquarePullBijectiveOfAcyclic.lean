import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LengthOneCochainExactness

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

noncomputable def incl (b : IdF A) : CH.Mor (sq b (IdF.bot A)) (CH.modF A) (RingHom.id R) where
  G := 𝟭 C
  τ T := (AlgEquiv.quotientBot R (A.obj T)).toLinearMap ∘ₗ (sqM b (IdF.bot A) T).subtype
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/- English proof (translation)
Take `⟨x, hx⟩` from `x`. Take `⟨y, hy, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx`. Conclude with `hy`.
-/
theorem incl_mem (b : IdF A) {T : C} (x : (sq b (IdF.bot A)).obj T) : (incl b).τ T x ∈ b.S T := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact hy

/- English proof (translation)
Use `⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Establish `h : (incl b).τ _ (x (s ⋙ 𝟭 C)) = (incl b).τ _ (y (s ⋙ 𝟭 C))` using `congrFun hxy s`. Conclude with `Subtype.ext ((AlgEquiv.quotientBot R _).injective h)`. Establish `hm : ∀ s : ComposableArrows C n, (show A.obj (s.obj (Fin.last n)) from y s) ∈ b.S (s.obj (Fin.last n))` using `fun s => by`.

Establish `h` using `congrArg Subtype.val (congrFun hy s)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h`. Conclude with `⟨fun s => sqMk b (IdF.bot A) _ (hm s), rfl⟩`. Introduce and unpack `⟨x, rfl⟩`. Use function extensionality and compare the values at `s`.

Conclude with `Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incl_mem b (x (s ⋙ 𝟭 C))))`. Establish `hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)), Ideal.Quotient.mk _ t = (show sqM a b _ from y s).1` using `fun s => Ideal.Quotient.mk_surjective _ choose t ht using hm`. Conclude with `⟨t, funext fun s => Subtype.ext (ht s)⟩`.
-/
theorem cochain_exact (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ n, Function.Injective ((incl b).hom.f n)) ∧
    (∀ n, Function.Exact ((incl b).hom.f n) ((toSq a b ha).hom.f n)) ∧
    ∀ n, Function.Surjective ((toSq a b ha).hom.f n) := by
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    have h : (incl b).τ _ (x (s ⋙ 𝟭 C)) = (incl b).τ _ (y (s ⋙ 𝟭 C)) := congrFun hxy s
    exact Subtype.ext ((AlgEquiv.quotientBot R _).injective h)
  · have hm : ∀ s : ComposableArrows C n,
        (show A.obj (s.obj (Fin.last n)) from y s) ∈ b.S (s.obj (Fin.last n)) := fun s => by
      have h := congrArg Subtype.val (congrFun hy s)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    exact ⟨fun s => sqMk b (IdF.bot A) _ (hm s), rfl⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incl_mem b (x (s ⋙ 𝟭 C))))
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

/- English proof (translation)
Introduce `hv j`. Take `⟨hf, hfg, hg⟩` from `cochain_exact a b ha`. Take `⟨δ, -, -, hex, hex2, -⟩` from `CrystallineSemistableComparison.P.les _ _ hf hfg hg`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `(hex j x).1 hx`. Rewrite using `[(hv j).elim y 0, map_zero]`. Introduce `y`. Take `⟨x, hx⟩` from `(hex2 j y).1 ((hv (j + 1)).elim _ _)`.

Conclude with `⟨x, hx⟩`.
-/
theorem pull_toSq_bijective (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) →
      ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  intro hv j
  obtain ⟨hf, hfg, hg⟩ := cochain_exact a b ha
  obtain ⟨δ, -, -, hex, hex2, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex j x).1 hx
    rw [(hv j).elim y 0, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := (hex2 j y).1 ((hv (j + 1)).elim _ _)
    exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.LengthOneCochainExactness
