import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToDualNumbersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldHomFlatSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangent

/- English proof (translation)
Set `π : DualNumber K →+* K` to `(TrivSqZeroExt.fstHom K K K).toRingHom`. Establish `hnK : (n : K) ≠ 0`. Use `((isUnit_natCast hn).map (π.comp β)).ne_zero` as an intermediate fact. Simplify using `using this`. Set `S : Subring (cycAway n)` to `{ carrier := {x | TrivSqZeroExt.snd (β x) = 0} mul_mem' := fun {a b} ha hb => by`.

Simplify using `only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *`. Simplify using `[ha, hb]`. Use the proof step `one_mem' := by simp`. Use the proof step `add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add, TrivSqZeroExt.snd_add] at *`.

Simplify using `[ha, hb]`. Use the proof step `zero_mem' := by simp`. Use the proof step `neg_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *`. Simplify using `[ha] }`.

Establish `hζ : zetaAway n ∈ S`. Establish `hz : zetaAway n ^ n = 1` using `Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one`. Establish `h1 : β (zetaAway n) ^ n = 1` using `by rw [← map_pow, hz, map_one]`. Establish `h2` using `congrArg TrivSqZeroExt.snd h1`. Establish `h3` using `congrArg TrivSqZeroExt.fst h1`.

Rewrite `h2` using `[TrivSqZeroExt.snd_pow]`. Rewrite `h3` using `[TrivSqZeroExt.fst_pow]`. Simplify using `only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3`. Establish `ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0`. Introduce `h0`.

Rewrite `h3` using `[h0, zero_pow hn]`. Conclude with `zero_ne_one h3`. Use `show TrivSqZeroExt.snd (β (zetaAway n)) = 0`. Rewrite `h2` using `[nsmul_eq_mul, smul_eq_mul]`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases.

Conclude with `absurd h hnK`. Break down `mul_eq_zero.1 h with h' | h'` into its components or cases. Conclude with `absurd h' (pow_ne_zero _ ha)`. Conclude with `h'`. Establish `hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S` using `by set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩`.

Establish `hu : (n : cycAway n) * u = 1` using `Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))`. Establish `h1 : (n : DualNumber K) * β u = 1` using `by rw [← map_natCast β, ← map_mul, hu, map_one]`. Establish `h2` using `congrArg TrivSqZeroExt.snd h1`. Simplify using `only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2`. Use `show TrivSqZeroExt.snd (β u) = 0`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd h hnK`. Conclude with `h`. Establish `hall : ∀ x : cycAway n, x ∈ S`. Introduce and unpack `⟨x, hx⟩`.

Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem y hy`. Break down `hy with rfl | rfl` into its components or cases. Conclude with `hζ`. Conclude with `hinv`.

Consider the case `zero => exact S.zero_mem`. Consider the case `one => exact S.one_mem`. Consider the case `add y z _ _ hy hz => exact S.add_mem hy hz`. Consider the case `neg y _ hy => exact S.neg_mem hy`. Consider the case `mul y z _ _ hy hz => exact S.mul_mem hy hz`.

Use `⟨π.comp β, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Use `ext`. Both sides reduce to the same expression. Conclude with `(hall x).trans (TrivSqZeroExt.snd_inl _ _).symm`.
-/
theorem cycAway_dualNumber_factor {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] (β : cycAway n →+* DualNumber K) :
    ∃ β₀ : cycAway n →+* K, β = (algebraMap K (DualNumber K)).comp β₀ := by
  let π : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have hnK : (n : K) ≠ 0 := by
    have := ((isUnit_natCast hn).map (π.comp β)).ne_zero
    simpa using this
  let S : Subring (cycAway n) :=
    { carrier := {x | TrivSqZeroExt.snd (β x) = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *
        simp [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, TrivSqZeroExt.snd_add] at *
        simp [ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *
        simp [ha] }
  have hζ : zetaAway n ∈ S := by
    have hz : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    have h1 : β (zetaAway n) ^ n = 1 := by rw [← map_pow, hz, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    have h3 := congrArg TrivSqZeroExt.fst h1
    rw [TrivSqZeroExt.snd_pow] at h2
    rw [TrivSqZeroExt.fst_pow] at h3
    simp only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3
    have ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at h3; exact zero_ne_one h3
    show TrivSqZeroExt.snd (β (zetaAway n)) = 0
    rw [nsmul_eq_mul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (pow_ne_zero _ ha)
      · exact h'
  have hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S := by
    set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    have hu : (n : cycAway n) * u = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
    have h1 : (n : DualNumber K) * β u = 1 := by rw [← map_natCast β, ← map_mul, hu, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2
    show TrivSqZeroExt.snd (β u) = 0
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · exact h
  have hall : ∀ x : cycAway n, x ∈ S := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hζ
      · exact hinv
    | zero => exact S.zero_mem
    | one => exact S.one_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | neg y _ hy => exact S.neg_mem hy
    | mul y z _ _ hy hz => exact S.mul_mem hy hz
  refine ⟨π.comp β, RingHom.ext fun x => ?_⟩
  ext
  · rfl
  · exact (hall x).trans (TrivSqZeroExt.snd_inl _ _).symm

/- English proof (translation)
Introduce `g n hg hn hodd F K _ β c hc`. Establish `hn0 : n ≠ 0` using `by omega`. Take `⟨β₀, rfl⟩` from `cycAway_dualNumber_factor hn0 K β`. Set `L` to `AlgebraicClosure K`. Take `⟨ψ, h1, -, hfl, hsurj⟩` from `GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)`.

Establish `hff : ψ.FaithfullyFlat` using `(flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩`. Use `letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra`. Use `haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff`. Use `GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_` and prove the remaining obligations. Introduce `c' hc'`.

Establish `hp : c'.Principal`. Use `(GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀)) (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀))) (spMap …` and prove the remaining obligations. Rewrite using `[GlobalTheory.SiegelRingChange.spMap_comp']`. Simplify using `[spMap]`. Establish `e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀)`.

Rewrite using `[← RingHom.comp_assoc, ← RingHom.comp_assoc]`. Conclude with `congrArg (fun q => q.comp β₀) h1`. Establish `key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) → ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal → ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f`. Introduce and unpack `b rfl c' hc'`. Conclude with `GlobalTheory.T.siegel_point_lifts_to_dual_numbers g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'`.

Conclude with `key _ e c' hp`.
-/
theorem classified_dualNumber : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β₀, rfl⟩ := cycAway_dualNumber_factor hn0 K β
  let L := AlgebraicClosure K
  obtain ⟨ψ, h1, -, hfl, hsurj⟩ := GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)
  have hff : ψ.FaithfullyFlat := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩
  letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_
  intro c' hc'
  have hp : c'.Principal := by
    refine (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀))
      (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀)))
      (spMap (algebraMap (DualNumber K) (DualNumber L))) rfl ?_).2.1 c c' hc' hc
    rw [GlobalTheory.SiegelRingChange.spMap_comp']
    simp [spMap]
  have e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) =
      (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (fun q => q.comp β₀) h1
  have key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) →
      ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal →
      ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f := by
    rintro b rfl c' hc'
    exact GlobalTheory.T.siegel_point_lifts_to_dual_numbers g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'
  exact key _ e c' hp

end GlobalTheory.SiegelTangent
