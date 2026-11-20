import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Apply the tactic sequence `cases i <;> simp [repL, Matrix.det_fin_two_of]`.
-/
lemma repL_det (L q : ℕ) (i : Option (Fin q)) : (repL L q i).det = q := by
  cases i <;> simp [repL, Matrix.det_fin_two_of]

/- English proof (translation)
Use `Gamma0_mem.mp γ.2` as an intermediate fact. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast this)`.
-/
lemma gamma0_lower_dvd {L : ℕ} (γ : Gamma0 L) : (L : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 := by
  have := Gamma0_mem.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast this)

/- English proof (translation)
Distinguish the cases in `hd : d = 0`. Establish `hb : b ≠ 0` using `hbd.resolve_right (by simpa using hd)`. Use `⟨a / (l * b), by field_simp, ?_⟩` and prove the remaining obligations. Substitute `hd` using the available equality. Establish `: b * c = 0` using `by linear_combination -hdet`.

Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h hb`. Simplify using `[h]`. Use `⟨c / (l * d), ?_, by field_simp⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hdet`.
-/
lemma exists_kernel_param {K : Type*} [Field K] (a b c d l : K) (hl : l ≠ 0)
    (hdet : a * d - b * c = 0) (hbd : b ≠ 0 ∨ d ≠ 0) : ∃ u, a = l * u * b ∧ c = l * u * d := by
  by_cases hd : d = 0
  · have hb : b ≠ 0 := hbd.resolve_right (by simpa using hd)
    refine ⟨a / (l * b), by field_simp, ?_⟩
    subst hd
    have : b * c = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb
    · simp [h]
  · refine ⟨c / (l * d), ?_, by field_simp⟩
    field_simp
    linear_combination hdet

/- English proof (translation)
Introduce `L q hq hqL`. Establish `hq0 : (q : ℤ) ≠ 0` using `by exact_mod_cast hq.ne_zero`. Establish `hqZ : Prime (q : ℤ)` using `Nat.prime_iff_prime_int.mp hq`. Establish `hqLZ : ¬ (q : ℤ) ∣ L` using `by exact_mod_cast hqL`. Use `haveI := Fact.mk hq`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨γ, i⟩ -`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.det_mul, repL_det]`. Establish `h` using `gamma0_lower_dvd γ`.

Consider the cases of `i with`. Consider the case `none => simpa [repL, Matrix.mul_apply, Fin.sum_univ_two] using h`. Consider the case `some j`. Simplify using `only [repL, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using the standard rewrite rules.

Conclude with `dvd_add (dvd_mul_of_dvd_left h _) (Dvd.dvd.mul_left (dvd_mul_right _ _) _)`. Introduce and unpack `⟨γ, i⟩ - ⟨γ', i'⟩ - h dsimp only at h`. Establish `hd` using `(γ : SL(2, ℤ)).2`. Establish `hd'` using `(γ' : SL(2, ℤ)).2`. Rewrite `hd`, `hd'` using `[Matrix.det_fin_two]`.

Establish `e00` using `congrFun (congrFun h 0) 0`. Establish `e01` using `congrFun (congrFun h 0) 1`. Establish `e10` using `congrFun (congrFun h 1) 0`. Establish `e11` using `congrFun (congrFun h 1) 1`. Establish `hq0' : q ≠ 0` using `hq.ne_zero`.

Establish `hq1 : ¬ (q : ℤ) ∣ 1` using `hqZ.not_dvd_one`. Apply the tactic sequence `rcases i with _ | j <;> rcases i' with _ | j' <;>`. Simplify using `[repL, Matrix.mul_apply, Fin.sum_univ_two, hq0'] at e00 e01 e10 e11`. Apply the tactic sequence `refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)) rfl fin_cases i <;> fin_cases j <;> simp <;> assumption`. Conclude with `absurd (Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 * ((γ : SL(2, ℤ)) : M2) 1 1 - ((γ : SL(2, ℤ)) : M2) 0 1 * ((γ' : SL(2, ℤ)) : M2) 1 0) (by linear_combination hd' + ((γ' : SL(2, ℤ)) : M2) 0 0 * e11 - ((γ' : SL(2, ℤ)) : M2) 1 0 * e01)) hq1`.

Conclude with `absurd (Dvd.intro (((γ : SL(2, ℤ)) : M2) 0 0 * ((γ' : SL(2, ℤ)) : M2) 1 1 - ((γ' : SL(2, ℤ)) : M2) 0 1 * ((γ : SL(2, ℤ)) : M2) 1 0) (by linear_combination hd - ((γ : SL(2, ℤ)) : M2) 0 0 * e11 + ((γ : SL(2, ℤ)) : M2) 1 0 * e01)) hq1`. Establish `h0 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 0 1` using `Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 - ((γ : SL(2, ℤ)) : M2) 0 0) (by linear_combination -e00 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e01)`. Establish `h1 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 1 1` using `Dvd.intro (((γ' : SL(2, ℤ)) : M2) 1 0 - ((γ : SL(2, ℤ)) : M2) 1 0) (by linear_combination -e10 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e11)`. Establish `hjj : (q : ℤ) ∣ ((j : ℕ) - (j' : ℕ) : ℤ)`. Assume the negation of the conclusion as `hn`.

Establish `hLj : ¬ (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ)` using `fun hh => (hqZ.dvd_or_dvd hh).elim hqLZ hn`. Establish `a0` using `(hqZ.dvd_or_dvd h0).resolve_left hLj`. Establish `a1` using `(hqZ.dvd_or_dvd h1).resolve_left hLj`. Apply `hq1` to reduce the goal to its premises. Rewrite using `[← hd]`.

Conclude with `(Dvd.dvd.mul_left a1 _).sub (Dvd.dvd.mul_right a0 _)`. Establish `hj` using `j.isLt`. Establish `hj'` using `j'.isLt`. Establish `hz` using `Int.eq_zero_of_abs_lt_dvd hjj (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)`. Establish `hjeq : j = j'` using `Fin.ext (by omega)`.

Substitute `hjeq` using the available equality. Use `Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_)) rfl` and prove the remaining obligations. Establish `f00 : ((γ : SL(2, ℤ)) : M2) 0 0 = ((γ' : SL(2, ℤ)) : M2) 0 0` using `mul_right_cancel₀ hq0 (by linear_combination e00 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e01)`. Establish `f10 : ((γ : SL(2, ℤ)) : M2) 1 0 = ((γ' : SL(2, ℤ)) : M2) 1 0` using `mul_right_cancel₀ hq0 (by linear_combination e10 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e11)`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp <;> assumption`.

Introduce and unpack `δ ⟨hdet, hL⟩`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Distinguish the cases in `hbd : (q : ℤ) ∣ δ 0 1 ∧ (q : ℤ) ∣ δ 1 1`. Take `⟨⟨b', hb⟩, ⟨d', hd⟩⟩` from `hbd`. Establish `hdet1 : (!![δ 0 0, b'; δ 1 0, d'] : M2).det = 1`.

Rewrite using `[Matrix.det_fin_two_of]`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Rewrite `hdet` using `[hb, hd]`. Take the linear combination `hdet`. Set `g : SL(2, ℤ)` to `⟨_, hdet1⟩`.

Establish `hg : g ∈ Gamma0 L`. Rewrite using `[Gamma0_mem]`. Establish `: ((δ 1 0 : ℤ) : ZMod L) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL`. Simplify `this` using `[g]`. Use `⟨(⟨g, hg⟩, none), trivial, ?_⟩` and prove the remaining obligations.

Use extensionality with `i k`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two, hb, hd] <;> ring`. Establish `hu : ∃ u : ZMod q, ((δ 0 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 0 1 : ℤ) : ZMod q) ∧ ((δ 1 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 1 1 : ℤ) : ZMod q)`. Apply `exists_kernel_param` to reduce the goal to its premises. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`.

Conclude with `hqL`. Use `congrArg (fun x : ℤ => (x : ZMod q)) hdet` as an intermediate fact. Simplify using `using this`. Assume the negation of the conclusion as `hn push_neg at hn`. Conclude with `hbd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.2⟩`.

Take `⟨u, hu0, hu1⟩` from `hu`. Use `set j : Fin q := ⟨u.val, ZMod.val_lt u⟩ with hjdef`. Establish `hju : (((j : ℕ) : ℤ) : ZMod q) = u` using `by simp [hjdef]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : (q : ℤ) ∣ δ 0 0 - L * (j : ℕ) * δ 0 1 := by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Move the coercions through the operations in `at hju ⊢`. Rewrite using `[hju, hu0]`. Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : (q : ℤ) ∣ δ 1 0 - L * (j : ℕ) * δ 1 1 := by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Move the coercions through the operations in `at hju ⊢`. Rewrite using `[hju, hu1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcop : IsCoprime (L : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL).symm`. Establish `hLz : (L : ℤ) ∣ z`.

Apply `hcop.dvd_of_dvd_mul_left` to reduce the goal to its premises. Rewrite using `[← hz]`. Conclude with `dvd_sub hL (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)`. Establish `hdet1 : (!![x, δ 0 1; z, δ 1 1] : M2).det = 1`. Rewrite using `[Matrix.det_fin_two_of]`.

Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Take the linear combination `-(δ 1 1) * hx + δ 0 1 * hz + hdet`. Set `g : SL(2, ℤ)` to `⟨_, hdet1⟩`. Establish `hg : g ∈ Gamma0 L`. Rewrite using `[Gamma0_mem]`.

Establish `: ((z : ℤ) : ZMod L) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLz`. Simplify `this` using `[g]`. Use `⟨(⟨g, hg⟩, some j), trivial, ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination -hx | linear_combination -hz`.
-/
theorem repL_LRep : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  intro L q hq hqL
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqLZ : ¬ (q : ℤ) ∣ L := by exact_mod_cast hqL
  haveI := Fact.mk hq
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, i⟩ -
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_mul, repL_det]
    · have h := gamma0_lower_dvd γ
      cases i with
      | none => simpa [repL, Matrix.mul_apply, Fin.sum_univ_two] using h
      | some j =>
        simp only [repL, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        exact dvd_add (dvd_mul_of_dvd_left h _) (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  · rintro ⟨γ, i⟩ - ⟨γ', i'⟩ - h
    dsimp only at h
    have hd := (γ : SL(2, ℤ)).2
    have hd' := (γ' : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at hd hd'
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    have hq0' : q ≠ 0 := hq.ne_zero
    have hq1 : ¬ (q : ℤ) ∣ 1 := hqZ.not_dvd_one
    rcases i with _ | j <;> rcases i' with _ | j' <;>
      simp [repL, Matrix.mul_apply, Fin.sum_univ_two, hq0'] at e00 e01 e10 e11
    · refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)) rfl
      fin_cases i <;> fin_cases j <;> simp <;> assumption
    · exact absurd (Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 * ((γ : SL(2, ℤ)) : M2) 1 1 -
          ((γ : SL(2, ℤ)) : M2) 0 1 * ((γ' : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd' + ((γ' : SL(2, ℤ)) : M2) 0 0 * e11 - ((γ' : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · exact absurd (Dvd.intro (((γ : SL(2, ℤ)) : M2) 0 0 * ((γ' : SL(2, ℤ)) : M2) 1 1 -
          ((γ' : SL(2, ℤ)) : M2) 0 1 * ((γ : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd - ((γ : SL(2, ℤ)) : M2) 0 0 * e11 + ((γ : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · have h0 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 0 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 - ((γ : SL(2, ℤ)) : M2) 0 0)
          (by linear_combination -e00 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e01)
      have h1 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 1 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 1 0 - ((γ : SL(2, ℤ)) : M2) 1 0)
          (by linear_combination -e10 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e11)
      have hjj : (q : ℤ) ∣ ((j : ℕ) - (j' : ℕ) : ℤ) := by
        by_contra hn
        have hLj : ¬ (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) := fun hh =>
          (hqZ.dvd_or_dvd hh).elim hqLZ hn
        have a0 := (hqZ.dvd_or_dvd h0).resolve_left hLj
        have a1 := (hqZ.dvd_or_dvd h1).resolve_left hLj
        apply hq1
        rw [← hd]
        exact (Dvd.dvd.mul_left a1 _).sub (Dvd.dvd.mul_right a0 _)
      have hj := j.isLt
      have hj' := j'.isLt
      have hz := Int.eq_zero_of_abs_lt_dvd hjj (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)
      have hjeq : j = j' := Fin.ext (by omega)
      subst hjeq
      refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_)) rfl
      have f00 : ((γ : SL(2, ℤ)) : M2) 0 0 = ((γ' : SL(2, ℤ)) : M2) 0 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e00 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e01)
      have f10 : ((γ : SL(2, ℤ)) : M2) 1 0 = ((γ' : SL(2, ℤ)) : M2) 1 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e10 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e11)
      fin_cases i <;> fin_cases k <;> simp <;> assumption
  · rintro δ ⟨hdet, hL⟩
    rw [Matrix.det_fin_two] at hdet
    by_cases hbd : (q : ℤ) ∣ δ 0 1 ∧ (q : ℤ) ∣ δ 1 1
    · obtain ⟨⟨b', hb⟩, ⟨d', hd⟩⟩ := hbd
      have hdet1 : (!![δ 0 0, b'; δ 1 0, d'] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        rw [hb, hd] at hdet
        linear_combination hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((δ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two, hb, hd] <;> ring
    · have hu : ∃ u : ZMod q, ((δ 0 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 0 1 : ℤ) : ZMod q) ∧
          ((δ 1 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 1 1 : ℤ) : ZMod q) := by
        apply exists_kernel_param
        · rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqL
        · have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
          simpa using this
        · by_contra hn
          push_neg at hn
          exact hbd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.1,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.2⟩
      obtain ⟨u, hu0, hu1⟩ := hu
      set j : Fin q := ⟨u.val, ZMod.val_lt u⟩ with hjdef
      have hju : (((j : ℕ) : ℤ) : ZMod q) = u := by simp [hjdef]
      obtain ⟨x, hx⟩ : (q : ℤ) ∣ δ 0 0 - L * (j : ℕ) * δ 0 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu0]; ring
      obtain ⟨z, hz⟩ : (q : ℤ) ∣ δ 1 0 - L * (j : ℕ) * δ 1 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu1]; ring
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL).symm
      have hLz : (L : ℤ) ∣ z := by
        apply hcop.dvd_of_dvd_mul_left
        rw [← hz]
        exact dvd_sub hL (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
      have hdet1 : (!![x, δ 0 1; z, δ 1 1] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        linear_combination -(δ 1 1) * hx + δ 0 1 * hz + hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((z : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLz
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, some j), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination -hz

end GlobalTheory.EisM
