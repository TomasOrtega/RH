import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ResEtaFOfPow
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Classical in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB χ n hχ`. Establish `hcm : IsCMExt F E σ` using `hB.cm`. Use `⟨exists_isEtaF hcm, fun η hη a => ?_⟩` and prove the remaining obligations. Take `⟨-, h1, h2, h3⟩` from `hη`. Establish `hS : ∀ x ∈ normGrp F E, η x = 1`.

Establish `: normGrp F E ≤ η.ker` using `sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)`. Conclude with `fun x hx => this hx`. Establish `hsq : ∀ x, η x * η x = 1` using `fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)`. Establish `key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n` using `fun x => hχ x`. Apply `Circle.ext` to reduce the goal to its premises.

Rewrite using `[key a, Circle.coe_pow]`. Distinguish the cases in `ha : a ∈ normGrp F E`. Rewrite using `[if_pos ha, hS a ha]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg ha]`.

Break down `Nat.even_or_odd n with ⟨k, rfl⟩ | hn` into its components or cases. Rewrite using `[← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]`. Simplify using the standard rewrite rules. Establish `hn1 : ((-1 : ℂ)) ^ n = -1` using `hn.neg_one_pow`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, η b ≠ 1 := by`.

Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `h3 (MonoidHom.ext hh)`. Establish `hbS : b ∉ normGrp F E` using `fun hm => hb (hS b hm)`. Establish `hab : a * b ∈ normGrp F E`.

Assume the negation of the conclusion as `hn2`. Establish `e` using `key (a * b)`. Rewrite `e` using `[map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1]`. Evaluate the numerical expressions using `at e`. Establish `hηb : (η b : ℂ) = -1` using `GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb`.

Establish `e2 : (η a : ℂ) * η b = 1` using `by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp`. Rewrite `e2` using `[hηb]`. Establish `hηa : (η a : ℂ) = -1` using `by linear_combination -e2`. Rewrite using `[hηa]`.
-/
theorem resEtaF_of_resEtaPow_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  intro F E _ _ _ _ _ σ B hB χ n hχ
  have hcm : IsCMExt F E σ := hB.cm
  refine ⟨exists_isEtaF hcm, fun η hη a => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hη
  have hS : ∀ x ∈ normGrp F E, η x = 1 := by
    have : normGrp F E ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  have hsq : ∀ x, η x * η x = 1 := fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)
  have key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n :=
    fun x => hχ x
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ normGrp F E
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ normGrp F E := fun hm => hb (hS b hm)
  have hab : a * b ∈ normGrp F E := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end GlobalTheory.ResEtaFOfPow
end
end
