import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GenLatCmp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩`.
-/
theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/- English proof (translation)
Simplify using `only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]`. Conclude with `forall_congr' fun i => mem_range_iff (v i)`.
-/
theorem mem_std (v : Fin n → E) : v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff (v i)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Rewrite `hv` using `[mem_std]`. Establish `: v = ∑ i, (⟨v i, hv i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E)`. Use extensionality with `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_std]`. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[Pi.single_apply, h]`.
-/
theorem std_eq : Formalism.L2.Pj.stdLat E n = stdL E n := by
  apply le_antisymm
  · intro v hv
    rw [mem_std] at hv
    have : v = ∑ i, (⟨v i, hv i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_std]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

/- English proof (translation)
Establish `e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v` using `fun v => by`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[Submodule.ideal_span_singleton_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h v hv`.

Rewrite using `[← e]`. Conclude with `h (Submodule.smul_mem_pointwise_smul v _ A hv)`. Introduce `h x hx`. Take `⟨v, hv, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx`. Rewrite using `[e]`.

Conclude with `h v hv`.
-/
theorem span_smul_le (k : ℕ) (A B : Lt E n) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (k : E) • v ∈ B := by
  have e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← e]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [e]; exact h v hv

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `A.toAddSubgroup.nsmul_mem hv k`.
-/
theorem natCast_smul_mem (k : ℕ) {A : Lt E n} {v : Fin n → E} (hv : v ∈ A) : (k : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.toAddSubgroup.nsmul_mem hv k

/- English proof (translation)
Establish `h0 : (stdL E n).FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `h1` using `h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))`. Use `h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩` and prove the remaining obligations. Establish `: (s : E) ≠ 0` using `by exact_mod_cast hs.ne'`. Simplify using `[smul_smul, this]`.
-/
theorem fg_of_smul_le {Λ : Lt E n} {s : ℕ} (hs : 0 < s) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ.FG := by
  have h0 : (stdL E n).FG := Submodule.fg_span (Set.finite_range _)
  have h1 := h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))
  refine h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩
  have : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  simp [smul_smul, this]

variable [IsCMField E]

/- English proof (translation)
Simplify using `[herm, cc, Matrix.one_apply]`.
-/
theorem herm_one_eq (x y : Fin n → E) :
    herm 1 x y = cc (∑ j, IsCMField.complexConj E (x j) * y j) := by
  simp [herm, cc, Matrix.one_apply]

/- English proof (translation)
Use `forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)` and prove the remaining obligations. Rewrite using `[mem_range_iff, herm_one_eq]`. Use `⟨Base.isIntegral_cc, fun h => ?_⟩` and prove the remaining obligations. Simplify `Base.isIntegral_cc h` using `[cc]`.
-/
theorem unimod_iff (Λ : Lt E n) : (⟨Λ⟩ : GenLat E n).Unimod ↔
    ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  rw [mem_range_iff, herm_one_eq]
  refine ⟨Base.isIntegral_cc, fun h => ?_⟩
  simpa [cc] using Base.isIntegral_cc h

/- English proof (translation)
Introduce `v hv`. Rewrite using `[← std_eq, mem_std]`. Introduce `i`. Use `(hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `[herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]`.
-/
theorem smul_mem_std {Λ : Lt E n} (hU : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {s : ℕ}
    (h : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n := by
  intro v hv
  rw [← std_eq, mem_std]
  intro i
  have := (hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))
  convert this using 1
  simp [herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]

/- English proof (translation)
Introduce `E _ _ _ n Λ`. Use `⟨?_, ?_, ?_, std_eq⟩` and prove the remaining obligations. Introduce and unpack `bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩`. Establish `t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m` using `fun m hm => ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩`. Use `⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right, t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩` and prove the remaining obligations.

Conclude with `(Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM`. Rewrite using `[span_smul_le]`. Introduce `v hv`. Use `⟨?_, natCast_smul_mem _ hv⟩` and prove the remaining obligations. Rewrite `hv` using `[std_eq]`.

Rewrite using `[mul_comm, Nat.cast_mul, mul_smul]`. Conclude with `natCast_smul_mem M (h2 v hv)`. Introduce and unpack `M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩`. Rewrite `hU` using `[unimod_iff]`. Rewrite `h1`, `h2`, `h3` using `[std_eq, span_smul_le]`.

Establish `h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ` using `fun v hv => (h3 v hv).1`. Establish `h5` using `smul_mem_std hU h4`. Use `⟨fg_of_smul_le hN.pos h5, hU, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Rewrite `hk` using `[Nat.coprime_zero_left]`.

Conclude with `⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩`. Conclude with `⟨k, hk0, hk, h1, h2⟩`. Introduce and unpack `M M' hM ⟨a, b, s, hs, hc, h⟩`. Conclude with `⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩`.
-/
theorem genLat_vset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Lt E n), (∀ bad M : ℕ, 0 < bad → Odd M → Λ ∈ Vset E n (2 * bad * M) → (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt bad ∧ (⟨Λ⟩ : GenLat E n).TrivAt M ∧ ∃ N, NOK Λ N M) ∧ (∀ M N : ℕ, 0 < M → (⟨Λ⟩ : GenLat E n).Unimod → (⟨Λ⟩ : GenLat E n).TrivAt M → NOK Λ N M → Λ ∈ Vset E n M) ∧ (∀ M M' : ℕ, M ∣ M' → Λ ∈ Vset E n M' → Λ ∈ Vset E n M) ∧ stdLat E n = stdL E n := by
  intro E _ _ _ n Λ
  refine ⟨?_, ?_, ?_, std_eq⟩
  · rintro bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩
    have t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m := fun m hm =>
      ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩
    refine ⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right,
      t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩
    · exact (Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM
    · rw [span_smul_le]
      intro v hv
      refine ⟨?_, natCast_smul_mem _ hv⟩
      rw [std_eq] at hv
      rw [mul_comm, Nat.cast_mul, mul_smul]
      exact natCast_smul_mem M (h2 v hv)
  · rintro M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩
    rw [unimod_iff] at hU
    rw [std_eq, span_smul_le] at h1 h2 h3
    have h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := fun v hv => (h3 v hv).1
    have h5 := smul_mem_std hU h4
    refine ⟨fg_of_smul_le hN.pos h5, hU, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      exact ⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩
    · exact ⟨k, hk0, hk, h1, h2⟩
  · rintro M M' hM ⟨a, b, s, hs, hc, h⟩
    exact ⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩

end GlobalTheory.Dict.GenLatCmp
