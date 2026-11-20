import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf

noncomputable section

namespace Formalism.L2.KerInert

namespace AlgTP

open NumberField Formalism.BasicNotions Formalism.L2.Ker

/- English proof (translation)
Establish `: NeZero (4 * d)` using `⟨by have := hd.pos; omega⟩`. Establish `hu : IsUnit (-1 : ZMod (4 * d))` using `isUnit_one.neg`. Take `⟨p, hpn, hp, hpa⟩` from `Nat.forall_exists_prime_gt_and_eq_mod hu n`. Use `⟨p, hpn, hp, ?_⟩` and prove the remaining obligations. Establish `hmod : (p : ℤ) ≡ -1 [ZMOD ((4 * d : ℕ) : ℤ)]`.

Rewrite using `[← ZMod.intCast_eq_intCast_iff]`. Use `push_cast`. Conclude with `hpa`. Establish `hm4 : (p : ℤ) ≡ -1 [ZMOD 4]`. Establish `h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)]` using `by simpa using hmod`.

Conclude with `Int.ModEq.of_mul_right _ h`. Establish `hmd : (p : ℤ) ≡ -1 [ZMOD (d : ℤ)]`. Establish `h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)]` using `by simpa using hmod`. Conclude with `Int.ModEq.of_mul_left _ h`. Establish `hp4 : p % 4 = 3`.

Unfold `Int.ModEq at hm4`. Use linear arithmetic over natural numbers and integers. Establish `hodd : Odd p` using `Nat.odd_iff.2 (by omega)`. Establish `hdodd : Odd d` using `Nat.odd_iff.2 (by omega)`. Rewrite using `[jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four hp4, jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4, jacobiSym.mod_left' hmd, jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd4]`.

Evaluate the numerical expressions.
-/
theorem exists_inert_prime (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ jacobiSym (-(d : ℤ)) p = -1 := by
  have : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  have hu : IsUnit (-1 : ZMod (4 * d)) := isUnit_one.neg
  obtain ⟨p, hpn, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu n
  refine ⟨p, hpn, hp, ?_⟩
  have hmod : (p : ℤ) ≡ -1 [ZMOD ((4 * d : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact hpa
  have hm4 : (p : ℤ) ≡ -1 [ZMOD 4] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_right _ h
  have hmd : (p : ℤ) ≡ -1 [ZMOD (d : ℤ)] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_left _ h
  have hp4 : p % 4 = 3 := by
    unfold Int.ModEq at hm4
    omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  have hdodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four hp4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4, jacobiSym.mod_left' hmd,
    jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd4]
  norm_num

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Conclude with `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm`.
-/
theorem mem_one_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ w := by
  rw [Submodule.mem_one]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

/- English proof (translation)
Rewrite using `[RingHom.mem_range]`. Conclude with `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm`.
-/
theorem mem_range_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ w := by
  rw [RingHom.mem_range]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

/- English proof (translation)
Set `_` to `D.host.cmStar`. Take `⟨S, hS⟩` from `hL.1`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (S.biUnion fun v => Finset.univ.image v)`. Establish `hint : ∀ w ∈ S.biUnion (fun v => Finset.univ.image v), IsIntegral ℤ ((y.natAbs : D.host.E) * w)`. Introduce `w hw`.

Establish `h` using `hy w hw`. Rewrite `h` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases. Establish `: ((y.natAbs : ℤ) : D.host.E) = (y : D.host.E)` using `by rw [← e]`. Rewrite `h` using `[← this]`.

Simplify using `using h`. Establish `: ((y.natAbs : ℤ) : D.host.E) = -(y : D.host.E)`. Rewrite using `[show ((y.natAbs : ℤ)) = -y by omega]; push_cast; ring`. Establish `h'` using `h.neg`. Rewrite `h'` using `[show -((y : D.host.E) * w) = ((y.natAbs : ℤ) : D.host.E) * w by rw [this]; ring]`.

Simplify using `using h'`. Establish `hfirst : ∀ x ∈ L, ((y.natAbs : ℕ) : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N`. Establish `hgen : ∀ v ∈ (S : Set (Fin N → D.host.E)), ((y.natAbs : ℕ) : D.host.E) • v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N`. Introduce `v hv`. Rewrite using `[Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]`.

Introduce `i _`. Rewrite using `[mem_one_iff, Pi.smul_apply, smul_eq_mul]`. Conclude with `hint (v i) (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)`. Introduce `x hx`. Rewrite `hx` using `[← hS]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem v hv => exact hgen v hv`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul r a _ ha => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ r ha`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy0, hfirst, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Use `(hL.2.2 _).2 ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hz'` using `hfirst z hz`. Rewrite `hx`, `hz'` using `[Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]`. Establish `e : stdH D.host.E N z (((y.natAbs : ℕ) : D.host.E) • x) = stdH D.host.E N (((y.natAbs : ℕ) : D.host.E) • z) x`.

Unfold `stdH`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, mem_range_iff]`.

Unfold `stdH`. Use `IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_` and prove the remaining obligations. Establish `h` using `(mem_one_iff _).1 (hz' i (Set.mem_univ i))`. Establish `h2` using `h.map (starRingEnd D.host.E).toIntAlgHom`. Apply the tactic sequence `convert h2 using 1 <;> rfl`.

Conclude with `(mem_one_iff _).1 (hx i (Set.mem_univ i))`.
-/
theorem exists_den (D : D7) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ s : ℕ, 0 < s ∧ (∀ x ∈ L, (s : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N) ∧
      ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, (s : D.host.E) • x ∈ L := by
  let _ := D.host.cmStar
  classical
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (S.biUnion fun v => Finset.univ.image v)
  have hint : ∀ w ∈ S.biUnion (fun v => Finset.univ.image v), IsIntegral ℤ ((y.natAbs : D.host.E) * w) := by
    intro w hw
    have h := hy w hw
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℤ) : D.host.E) = (y : D.host.E) := by rw [← e]
      rw [← this] at h
      simpa using h
    · have : ((y.natAbs : ℤ) : D.host.E) = -(y : D.host.E) := by
        rw [show ((y.natAbs : ℤ)) = -y by omega]; push_cast; ring
      have h' := h.neg
      rw [show -((y : D.host.E) * w) = ((y.natAbs : ℤ) : D.host.E) * w by rw [this]; ring] at h'
      simpa using h'
  have hfirst : ∀ x ∈ L, ((y.natAbs : ℕ) : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    have hgen : ∀ v ∈ (S : Set (Fin N → D.host.E)), ((y.natAbs : ℕ) : D.host.E) • v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro v hv
      rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]
      intro i _
      rw [mem_one_iff, Pi.smul_apply, smul_eq_mul]
      exact hint (v i) (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, hfirst, ?_⟩
  intro x hx
  refine (hL.2.2 _).2 ?_
  intro z hz
  have hz' := hfirst z hz
  rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi] at hx hz'
  have e : stdH D.host.E N z (((y.natAbs : ℕ) : D.host.E) • x) =
      stdH D.host.E N (((y.natAbs : ℕ) : D.host.E) • z) x := by
    unfold stdH
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast]
    ring
  rw [e, mem_range_iff]
  unfold stdH
  refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
  · have h := (mem_one_iff _).1 (hz' i (Set.mem_univ i))
    have h2 := h.map (starRingEnd D.host.E).toIntAlgHom
    convert h2 using 1 <;> rfl
  · exact (mem_one_iff _).1 (hx i (Set.mem_univ i))

/- English proof (translation)
Introduce `D cc δ B χ hcc hδ hχ N N' L L' hA t ⟨a, ha, hat⟩ α`. Take `⟨s, hs, hsL1, hsL2⟩` from `exists_den D L hA.2.2.1`. Take `⟨s', hs', hsL1', hsL2'⟩` from `exists_den D L' hA.2.2.2`. Establish `hd` using `D.host.hyp`. Take `⟨p, hpn, hp, hJ⟩` from `exists_inert_prime D.host.d hd.2.1 (by have := hd.2.2.2.1; omega) (a * s * s' + 4)`.

Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hpos : 0 < a * s * s'` using `by positivity`. Establish `hcop : ∀ m : ℕ, m ∣ a * s * s' → Nat.Coprime m p` using `fun m hm => Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => absurd (Nat.le_of_dvd hpos (h.trans hm)) (by omega))`. Establish `H` using `(AlgP.algebraic_fact_kernels D cc δ B hcc hδ χ hχ p (by omega) hJ N N').1 L L' hA ⟨s, hcop s (Dvd.intro_left _ rfl |>.mul_right _), hsL2, hsL1⟩ ⟨s', hcop s' (Dvd.intro_left _ rfl), hsL2', hsL1'⟩ t ⟨a, ha, hcop a ((Dvd.intro _ rfl).mul_right _), hat⟩`. Conclude with `H.2 α`.
-/
theorem algebraic_translates_all_data : AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ⟨a, ha, hat⟩ α
  obtain ⟨s, hs, hsL1, hsL2⟩ := exists_den D L hA.2.2.1
  obtain ⟨s', hs', hsL1', hsL2'⟩ := exists_den D L' hA.2.2.2
  have hd := D.host.hyp
  obtain ⟨p, hpn, hp, hJ⟩ :=
    exists_inert_prime D.host.d hd.2.1 (by have := hd.2.2.2.1; omega) (a * s * s' + 4)
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < a * s * s' := by positivity
  have hcop : ∀ m : ℕ, m ∣ a * s * s' → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      absurd (Nat.le_of_dvd hpos (h.trans hm)) (by omega))
  have H := (AlgP.algebraic_fact_kernels D cc δ B hcc hδ χ hχ p (by omega) hJ N N').1 L L' hA
    ⟨s, hcop s (Dvd.intro_left _ rfl |>.mul_right _), hsL2, hsL1⟩
    ⟨s', hcop s' (Dvd.intro_left _ rfl), hsL2', hsL1'⟩ t
    ⟨a, ha, hcop a ((Dvd.intro _ rfl).mul_right _), hat⟩
  exact H.2 α

/- English proof (translation)
The claim follows from `algebraic_translates_all_data D cc δ B χ hcc hδ hχ`.
-/
theorem algT_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ}
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.AlgT χ :=
  algebraic_translates_all_data D cc δ B χ hcc hδ hχ

end AlgTP

end Formalism.L2.KerInert
