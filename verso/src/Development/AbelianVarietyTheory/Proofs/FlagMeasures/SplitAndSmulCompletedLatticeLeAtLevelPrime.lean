import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.LocCong

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D Z P hP`. Use `set p : PlF D := below D P with hp`. Establish `hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal)`. Introduce `n`. Use `show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _`.

Rewrite using `[Ideal.mem_comap, map_natCast]`. Establish `hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal`. Establish `h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal` using `(hmem _).2 hP`. Simplify using `only [gS, Nat.cast_mul] at h1`. Break down `p.isPrime.mem_or_mem h1 with h | h` into its components or cases.

Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`. Take `⟨i, hi⟩` from `hg`. Establish `hchar : Loc.resChar p = D.host.g i`. Establish `hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hi`. Establish `hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i` using `ringChar.dvd hz`. Conclude with `(Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd`. Take `⟨j, hne, hgg⟩ : ∃ j : Fin 2, D.host.g i ≠ D.host.g j ∧ gS D = D.host.g i * D.host.g j` from `by fin_cases i`.

Conclude with `⟨1, D.host.g_ne, rfl⟩`. Conclude with `⟨0, D.host.g_ne.symm, by simp [gS, mul_comm]⟩`. Establish `hsome : (D.s.atP p).split.isSome` using `(D.s_split p).2 (by`. Apply the tactic sequence `rw [hchar]; fin_cases i <;> simp)`. Take `⟨sg0, hsg0⟩` from `Option.isSome_iff_exists.1 hsome`.

Establish `hag` using `(Z.agree p).2.2.2.2.2`. Break down `hZs : (Z.M p).split with _ | sg` into its components or cases. Rewrite `hag` using `[hZs, hsg0]`. Conclude with `hag.elim`. Rewrite `hag` using `[hZs, hsg0]`.

Use `⟨sg, rfl, ?_⟩` and prove the remaining obligations. Establish `hq : ((sg.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp)`. Rewrite using `[hag.2, sg0.q_eq, hchar]`. Establish `hqO : (sg.q : 𝒪[(D.s.atP p).Fp]) = ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp])`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hq]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hcop : Nat.Coprime (D.host.g i) (D.host.g j)` using `(Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hne`. Establish `hbez : (1 : ℤ) = (D.host.g i : ℤ) * Int.gcdA (D.host.g i) (D.host.g j) + (D.host.g j : ℤ) * Int.gcdB (D.host.g i) (D.host.g j)`.

Use `Int.gcd_eq_gcd_ab (D.host.g i : ℤ) (D.host.g j : ℤ)` as an intermediate fact. Rewrite `this` using `[Int.gcd_natCast_natCast, hcop.gcd_eq_one]`. Conclude with `this` after adjusting the coercions. Establish `hunit : IsUnit ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp])`. Establish `hqn : ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) ∈ IsLocalRing.maximalIdeal 𝒪[(D.s.atP p).Fp]`.

Rewrite using `[← hqO]`. Conclude with `sg.q_irr.not_isUnit`. Establish `h1 : IsUnit (1 - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]))` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hqn)`. Establish `h2 : (1 : 𝒪[(D.s.atP p).Fp]) - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) = ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdB (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp])`. Use `congrArg (Int.cast : ℤ → 𝒪[(D.s.atP p).Fp]) hbez` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2]`. Conclude with `isUnit_of_mul_isUnit_left h1`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp) = 1 := by`. Use `⟨((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_⟩` and prove the remaining obligations. Establish `h1 : ((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]) * ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) = 1`. Use `hunit.unit.inv_mul` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis.

Establish `h2` using `congrArg Subtype.val h1`. Conclude with `h2` after adjusting the coercions. Establish `hwO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) ∈ (Z.M p).L.O`. Rewrite using `[(Z.agree p).2.2.2.1, (D.s.atP p).O_def]`. Conclude with `isIntegral_algebraMap`.

Establish `hsc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((gS D : ℕ) : (D.s.atP p).Ep)`. Rewrite using `[← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hq, hgg]`. Use `congr 1`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Introduce `Λ v hv`. Unfold `Loc.HermSp.smulLat at hv`. Use `(Submodule.span_le.2 ?_) hv` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Simplify using `only [SetLike.mem_coe]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Rewrite using `[hsc, mul_smul]`. Establish `e : ((gS D : ℕ) : (D.s.atP p).Ep) • baseChange₂ D p x = baseChange₂ D p (((gS D : ℕ) : 𝓞 D.host.E) • x)`.

Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]`. Rewrite using `[e]`. Conclude with `(lattice₂ D Z.M p _).smul_mem (⟨_, hwO⟩ : (Z.M p).L.O) (Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx, rfl⟩)`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul o y _ hy`. Establish `e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • (o • y) = o • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • y)` using `by show _ • ((o : (D.s.atP p).Ep) • y) = (o : (D.s.atP p).Ep) • _`. Rewrite using `[smul_smul, smul_smul, mul_comm]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem qsmul_latP_le_gS : ∀ (D : D7) (Z : LocDat D) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ sg : Loc.SplitG (Z.M (below D P)).L, (Z.M (below D P)).split = some sg ∧ ∀ (Λ : LV D) (v : Vp D (below D P)), v ∈ (locH Z (below D P)).smulLat (algebraMap (D.s.atP (below D P)).Fp (D.s.atP (below D P)).Ep (sg.q : (D.s.atP (below D P)).Fp)) (lattice₂ D Z.M (below D P) Λ) → v ∈ lattice₂ D Z.M (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D Z P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  obtain ⟨j, hne, hgg⟩ : ∃ j : Fin 2, D.host.g i ≠ D.host.g j ∧ gS D = D.host.g i * D.host.g j := by
    fin_cases i
    · exact ⟨1, D.host.g_ne, rfl⟩
    · exact ⟨0, D.host.g_ne.symm, by simp [gS, mul_comm]⟩
  have hsome : (D.s.atP p).split.isSome := (D.s_split p).2 (by
    rw [hchar]; fin_cases i <;> simp)
  obtain ⟨sg0, hsg0⟩ := Option.isSome_iff_exists.1 hsome
  have hag := (Z.agree p).2.2.2.2.2
  rcases hZs : (Z.M p).split with _ | sg
  · rw [hZs, hsg0] at hag; exact hag.elim
  rw [hZs, hsg0] at hag
  refine ⟨sg, rfl, ?_⟩
  have hq : ((sg.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) := by
    rw [hag.2, sg0.q_eq, hchar]
  have hqO : (sg.q : 𝒪[(D.s.atP p).Fp]) = ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    apply Subtype.ext; rw [hq]; push_cast; rfl
  have hcop : Nat.Coprime (D.host.g i) (D.host.g j) :=
    (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hne
  have hbez : (1 : ℤ) = (D.host.g i : ℤ) * Int.gcdA (D.host.g i) (D.host.g j) +
      (D.host.g j : ℤ) * Int.gcdB (D.host.g i) (D.host.g j) := by
    have := Int.gcd_eq_gcd_ab (D.host.g i : ℤ) (D.host.g j : ℤ)
    rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at this
    exact_mod_cast this
  have hunit : IsUnit ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    have hqn : ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) ∈ IsLocalRing.maximalIdeal 𝒪[(D.s.atP p).Fp] := by
      rw [← hqO]; exact sg.q_irr.not_isUnit
    have h1 : IsUnit (1 - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hqn)
    have h2 : (1 : 𝒪[(D.s.atP p).Fp]) - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) =
        ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdB (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) := by
      have := congrArg (Int.cast : ℤ → 𝒪[(D.s.atP p).Fp]) hbez
      push_cast at this
      rw [this]; ring
    rw [h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp) = 1 := by
    refine ⟨((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_⟩
    have h1 : ((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]) * ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) = 1 := by
      have := hunit.unit.inv_mul
      rwa [IsUnit.unit_spec] at this
    have h2 := congrArg Subtype.val h1
    exact_mod_cast h2
  have hwO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) ∈ (Z.M p).L.O := by
    rw [(Z.agree p).2.2.2.1, (D.s.atP p).O_def]
    exact isIntegral_algebraMap
  have hsc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((gS D : ℕ) : (D.s.atP p).Ep) := by
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hq, hgg]
    congr 1
    push_cast
    calc ((D.host.g i : ℕ) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) * ((w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp)) := by rw [hw, mul_one]
      _ = _ := by ring
  intro Λ v hv
  unfold Loc.HermSp.smulLat at hv
  refine (Submodule.span_le.2 ?_) hv
  rintro _ ⟨y, hy, rfl⟩
  simp only [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hsc, mul_smul]
    have e : ((gS D : ℕ) : (D.s.atP p).Ep) • baseChange₂ D p x = baseChange₂ D p (((gS D : ℕ) : 𝓞 D.host.E) • x) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [e]
    exact (lattice₂ D Z.M p _).smul_mem (⟨_, hwO⟩ : (Z.M p).L.O)
      (Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx, rfl⟩)
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o y _ hy =>
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • (o • y) =
        o • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • y) := by
      show _ • ((o : (D.s.atP p).Ep) • y) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.LocCong
