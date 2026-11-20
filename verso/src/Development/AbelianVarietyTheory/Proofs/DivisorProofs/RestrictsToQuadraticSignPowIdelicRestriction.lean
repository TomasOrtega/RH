import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Classical in

/- English proof (translation)
Introduce `D χ n h`. Use `⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η hη a => ?_⟩` and prove the remaining obligations. Establish `hsq : ∀ x, η x * η x = 1` using `GlobalTheory.VolHeckeCompare.IsEta_mul_self hη`. Take `⟨-, h1, h2, h3⟩` from `hη`. Use `set S := (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)).range with hSdef`.

Establish `key : ∀ x, ((χ (idF D x) : Circle) : ℂ) = if x ∈ S then 1 else (-1) ^ n` using `fun x => h x`. Establish `hS : ∀ x ∈ S, η x = 1`. Establish `: S ≤ η.ker` using `sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)`. Conclude with `fun x hx => this hx`. Apply `Circle.ext` to reduce the goal to its premises.

Rewrite using `[key a, Circle.coe_pow]`. Distinguish the cases in `ha : a ∈ S`. Rewrite using `[if_pos ha, hS a ha]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg ha]`.

Break down `Nat.even_or_odd n with ⟨k, rfl⟩ | hn` into its components or cases. Rewrite using `[← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]`. Simplify using the standard rewrite rules. Establish `hn1 : ((-1 : ℂ)) ^ n = -1` using `hn.neg_one_pow`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, η b ≠ 1 := by`.

Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `h3 (MonoidHom.ext hh)`. Establish `hbS : b ∉ S` using `fun hm => hb (hS b hm)`. Establish `hab : a * b ∈ S`.

Assume the negation of the conclusion as `hn2`. Establish `e` using `key (a * b)`. Rewrite `e` using `[map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1]`. Evaluate the numerical expressions using `at e`. Establish `hηb : (η b : ℂ) = -1` using `GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb`.

Establish `e2 : (η a : ℂ) * η b = 1` using `by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp`. Rewrite `e2` using `[hηb]`. Establish `hηa : (η a : ℂ) = -1` using `by linear_combination -e2`. Rewrite using `[hηa]`.
-/
theorem GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  intro D χ n h
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η hη a => ?_⟩
  have hsq : ∀ x, η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη
  obtain ⟨-, h1, h2, h3⟩ := hη
  set S := (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range ⊔
    (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)).range with hSdef
  have key : ∀ x, ((χ (idF D x) : Circle) : ℂ) = if x ∈ S then 1 else (-1) ^ n := fun x => h x
  have hS : ∀ x ∈ S, η x = 1 := by
    have : S ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ S
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ S := fun hm => hb (hS b hm)
  have hab : a * b ∈ S := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
