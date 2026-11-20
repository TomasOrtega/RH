import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in

/- English proof (translation)
Introduce `U P hP`. Unfold `_root_.GlobalTheory.EtC.Loc`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, hSP⟩ x`. Take `⟨𝒰, h𝒰⟩` from `(Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS`.

Use `haveI : Scheme.JointlySurjective (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) := Scheme.instJointlySurjectivePrecoverage`. Take `⟨i, y, rfl⟩` from `𝒰.exists_eq x`. Set `A` to `(𝒰.X i).affineCover`. Take `⟨z, hz⟩` from `A.covers y`. Establish `hE : Etale (𝒰.f i)` using `𝒰.map_prop i`.

Use `⟨A.X (A.idx y), A.f (A.idx y) ≫ 𝒰.f i, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply, hz]`. Conclude with `hSP _ _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk i)) _)`. Introduce `h choose V g hV hE hx hPg using h`. Set `S : Sieve U` to `{ arrows := fun W f => P W f, downward_closed := fun hf k => hP _ _ _ k hf }`.

Use `⟨S, ?_, fun W f hf => hf⟩` and prove the remaining obligations. Use `(Scheme.mem_grothendieckTopology_iff (P := @Etale)).2 ⟨Scheme.Cover.mkOfCovers U V g (fun x => ?_) (fun x => hE x), ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx x`. Conclude with `⟨x, y, hy⟩`. Introduce and unpack `_ _ ⟨x⟩`.

Conclude with `hPg x`.
-/
theorem _root_.GlobalTheory.EtC.loc_iff_etale_affine_points : ∀ (U : Scheme.{0})
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    (_root_.GlobalTheory.EtC.Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U),
      IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  intro U P hP
  unfold _root_.GlobalTheory.EtC.Loc
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    haveI : Scheme.JointlySurjective (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
      Scheme.instJointlySurjectivePrecoverage
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    let A := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := A.covers y
    have hE : Etale (𝒰.f i) := 𝒰.map_prop i
    refine ⟨A.X (A.idx y), A.f (A.idx y) ≫ 𝒰.f i, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hz]
    · exact hSP _ _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hV hE hx hPg using h
    let S : Sieve U :=
      { arrows := fun W f => P W f, downward_closed := fun hf k => hP _ _ _ k hf }
    refine ⟨S, ?_, fun W f hf => hf⟩
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V g (fun x => ?_) (fun x => hE x), ?_⟩
    · obtain ⟨y, hy⟩ := hx x
      exact ⟨x, y, hy⟩
    · rintro _ _ ⟨x⟩
      exact hPg x

end GlobalTheory.EtC
