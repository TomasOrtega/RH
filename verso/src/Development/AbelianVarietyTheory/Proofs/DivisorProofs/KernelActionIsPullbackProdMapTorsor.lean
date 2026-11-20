import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]`.
-/
theorem comp_one_hom {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

/- English proof (translation)
Introduce `S A A' N T _ _ _ i q hi hq hker`. Establish `hiq : i ≫ q = 1` using `by rw [hker.w, Hom.one_def]`. Establish `hpf : pmap q T ≫ fst A' T = fst A T ≫ q` using `by simp [pmap]`. Establish `hps : pmap q T ≫ snd A' T = snd A T` using `by simp [pmap]`. Establish `hc : prMap A N T ≫ pmap q T = actMap i T ≫ pmap q T`.

Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hpf]`. Simplify using `only [prMap, actMap, lift_fst_assoc, mul_comp, Category.assoc, hiq]`. Simplify using `only [comp_one_hom, _root_.mul_one]`. Rewrite using `[Category.assoc, Category.assoc, hps]`.

Simplify using `[prMap, actMap]`. Establish `hfs : ∀ s : PullbackCone (pmap q T) (pmap q T), (s.fst ≫ fst A T) ≫ q = (s.snd ≫ fst A T) ≫ q`. Introduce `s`. Establish `h` using `congrArg (· ≫ fst A' T) s.condition`. Simplify using `only [Category.assoc, hpf] at h`.

Simplify `h` using `only [Category.assoc]`. Establish `hss : ∀ s : PullbackCone (pmap q T) (pmap q T), s.fst ≫ snd A T = s.snd ≫ snd A T`. Introduce `s`. Establish `h` using `congrArg (· ≫ snd A' T) s.condition`. Simplify `h` using `only [Category.assoc, hps]`.

Establish `hk : ∀ s : PullbackCone (pmap q T) (pmap q T), ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) ≫ q = toUnit s.pt ≫ η[A']`. Introduce `s`. Rewrite using `[mul_comp, GrpObj.inv_comp, hfs s, _root_.inv_mul_cancel, Hom.one_def]`. Use `⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc (fun s => lift (s.fst ≫ fst A T) (lift (hker.lift ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) (toUnit _) (hk s)) (s.fst ≫ snd A T))) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s`.

Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [prMap]`. Introduce `s`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `only [actMap, Category.assoc, lift_fst, comp_mul, lift_fst_assoc, lift_snd_assoc, hker.lift_fst]`. Conclude with `_root_.mul_inv_cancel_left _ _`.

Simplify using `[actMap, hss]`. Introduce `s m h1 h2`. Establish `ha : m ≫ fst A (N ⊗ T) = s.fst ≫ fst A T` using `by rw [← h1]; simp [prMap]`. Establish `ht : m ≫ snd A (N ⊗ T) ≫ snd N T = s.fst ≫ snd A T` using `by rw [← h1]; simp [prMap]`. Establish `hb : m ≫ fst A (N ⊗ T) * m ≫ snd A (N ⊗ T) ≫ fst N T ≫ i = s.snd ≫ fst A T`.

Rewrite using `[← h2]`. Simplify using `[actMap, comp_mul]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `using ha`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Apply `hker.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, lift_snd_assoc, lift_fst_assoc, hker.lift_fst]`. Rewrite using `[← ha]`. Conclude with `eq_inv_mul_of_mul_eq hb`. Conclude with `toUnit_unique _ _`.

Simplify using `using ht`.
-/
theorem pmap_isPullback_actMap : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  intro S A A' N T _ _ _ i q hi hq hker
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hpf : pmap q T ≫ fst A' T = fst A T ≫ q := by simp [pmap]
  have hps : pmap q T ≫ snd A' T = snd A T := by simp [pmap]
  have hc : prMap A N T ≫ pmap q T = actMap i T ≫ pmap q T := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hpf]
      simp only [prMap, actMap, lift_fst_assoc, mul_comp, Category.assoc, hiq]
      simp only [comp_one_hom, _root_.mul_one]
    · rw [Category.assoc, Category.assoc, hps]
      simp [prMap, actMap]
  have hfs : ∀ s : PullbackCone (pmap q T) (pmap q T), (s.fst ≫ fst A T) ≫ q = (s.snd ≫ fst A T) ≫ q := by
    intro s
    have h := congrArg (· ≫ fst A' T) s.condition
    simp only [Category.assoc, hpf] at h
    simpa only [Category.assoc] using h
  have hss : ∀ s : PullbackCone (pmap q T) (pmap q T), s.fst ≫ snd A T = s.snd ≫ snd A T := by
    intro s
    have h := congrArg (· ≫ snd A' T) s.condition
    simpa only [Category.assoc, hps] using h
  have hk : ∀ s : PullbackCone (pmap q T) (pmap q T),
      ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) ≫ q = toUnit s.pt ≫ η[A'] := by
    intro s
    rw [mul_comp, GrpObj.inv_comp, hfs s, _root_.inv_mul_cancel, Hom.one_def]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => lift (s.fst ≫ fst A T)
      (lift (hker.lift ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) (toUnit _) (hk s)) (s.fst ≫ snd A T)))
    ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext <;> simp [prMap]
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp only [actMap, Category.assoc, lift_fst, comp_mul, lift_fst_assoc, lift_snd_assoc, hker.lift_fst]
      exact _root_.mul_inv_cancel_left _ _
    · simp [actMap, hss]
  · intro s m h1 h2
    have ha : m ≫ fst A (N ⊗ T) = s.fst ≫ fst A T := by rw [← h1]; simp [prMap]
    have ht : m ≫ snd A (N ⊗ T) ≫ snd N T = s.fst ≫ snd A T := by rw [← h1]; simp [prMap]
    have hb : m ≫ fst A (N ⊗ T) * m ≫ snd A (N ⊗ T) ≫ fst N T ≫ i = s.snd ≫ fst A T := by
      rw [← h2]; simp [actMap, comp_mul]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using ha
    · apply CartesianMonoidalCategory.hom_ext
      · apply hker.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, hker.lift_fst]
          rw [← ha]
          exact eq_inv_mul_of_mul_eq hb
        · exact toUnit_unique _ _
      · simpa using ht

end GlobalTheory.CharKer
