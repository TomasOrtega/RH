import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryMovingToSelfDualSkewLStatement
open scoped Pointwise nonZeroDivisors
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.FunObj.EigUnit

/- English proof (translation)
Establish `h2 : D.host.conj * D.host.conj = 1` using `AlgEquiv.ext fun x => VacMove.conj_conj D x`. Rewrite using `[smul_smul, h2, one_smul]`.
-/
theorem conj_smul_smul (D : D7) (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
  rw [smul_smul, h2, one_smul]

/- English proof (translation)
Simplify using `only [Ideal.pointwise_smul_def, Ideal.map_mul]`.
-/
theorem conj_smul_mul (D : D7) (I J : Ideal (𝓞 D.host.E)) :
    D.host.conj • (I * J) = D.host.conj • I * D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def, Ideal.map_mul]

/- English proof (translation)
Simplify using `only [Ideal.pointwise_smul_def]`. Conclude with `Ideal.map_mono h`.
-/
theorem conj_smul_mono (D : D7) {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def]; exact Ideal.map_mono h

/- English proof (translation)
Proceed by induction on `𝔪 using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => exact absurd rfl h𝔪`. Consider the case `h₂ x hx`. Rewrite `hx` using `[Ideal.isUnit_iff]`. Substitute `hx` using the available equality.

Conclude with `⟨⊤, top_ne_bot, by rw [Ideal.isCoprime_iff_sup_eq]; exact top_sup_eq _, rfl⟩`. Consider the case `h₃ x p hx hp ih`. Take `⟨n, hn, hcop, hxn⟩` from `ih hx`. Establish `hpb : p ≠ ⊥` using `hp.ne_zero`. Establish `hpP : p.IsPrime` using `Ideal.isPrime_of_prime hp`.

Establish `hpM : p.IsMaximal` using `hpP.isMaximal hpb`. Establish `hsb : D.host.conj • p ≠ ⊥` using `GlobalTheory.BotPairSmall.conj_smul_ne_bot D hpb`. Establish `hsM : (D.host.conj • p).IsMaximal` using `(Ideal.IsPrime.smul D.host.conj).isMaximal hsb`. Distinguish the cases in `hfix : D.host.conj • p = p`. Use `⟨n, hn, hcop, ?_⟩` and prove the remaining obligations.

Rewrite using `[conj_smul_mul, hfix, mul_assoc, hxn]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hdiv : n ≤ D.host.conj • p`. Take `⟨n', rfl⟩` from `Ideal.dvd_iff_le.2 hdiv`. Use `⟨n', fun h0 => hn (by rw [h0, Ideal.mul_bot]), ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hcop` using `[conj_smul_mul]`. Conclude with `(hcop.of_mul_left_right).of_mul_right_right`. Simplify using `only [conj_smul_mul, conj_smul_smul] at hxn ⊢`. Combine the equalities or inequalities in the displayed calculation. Use `⟨p * n, mul_ne_zero hpb hn, ?_, ?_⟩` and prove the remaining obligations.

Establish `hnot : ¬ D.host.conj • n ≤ p` using `fun h => hdiv (by`. Use `conj_smul_mono D h` as an intermediate fact. Rewrite using `[conj_smul_smul] at this)` and apply the resulting hypothesis. Establish `c1 : IsCoprime p (D.host.conj • p)`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Assume the negation of the conclusion as `hne`. Establish `h3 : p = p ⊔ D.host.conj • p` using `hpM.eq_of_le hne le_sup_left`. Conclude with `hfix (hsM.eq_of_le hpM.ne_top (le_sup_right.trans h3.ge))`. Establish `c2 : IsCoprime p (D.host.conj • n)`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Assume the negation of the conclusion as `hne`. Establish `h3 : p = p ⊔ D.host.conj • n` using `hpM.eq_of_le hne le_sup_left`. Conclude with `hnot (le_sup_right.trans h3.ge)`. Establish `c3 : IsCoprime n (D.host.conj • p)`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, sup_comm]`.

Assume the negation of the conclusion as `hne`. Establish `h3 : D.host.conj • p = D.host.conj • p ⊔ n` using `hsM.eq_of_le hne le_sup_left`. Conclude with `hdiv (le_sup_right.trans h3.ge)`. Rewrite using `[conj_smul_mul]`. Conclude with `IsCoprime.mul_left (IsCoprime.mul_right c1 c2) (IsCoprime.mul_right c3 hcop)`.

Rewrite using `[conj_smul_mul, conj_smul_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coprime_rep (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ 𝔫 : Ideal (𝓞 D.host.E), 𝔫 ≠ ⊥ ∧ IsCoprime 𝔫 (D.host.conj • 𝔫) ∧
      𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪 := by
  induction 𝔪 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h𝔪
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    exact ⟨⊤, top_ne_bot, by rw [Ideal.isCoprime_iff_sup_eq]; exact top_sup_eq _, rfl⟩
  | h₃ x p hx hp ih =>
    obtain ⟨n, hn, hcop, hxn⟩ := ih hx
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    have hpM : p.IsMaximal := hpP.isMaximal hpb
    have hsb : D.host.conj • p ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hpb
    have hsM : (D.host.conj • p).IsMaximal := (Ideal.IsPrime.smul D.host.conj).isMaximal hsb
    by_cases hfix : D.host.conj • p = p
    · refine ⟨n, hn, hcop, ?_⟩
      rw [conj_smul_mul, hfix, mul_assoc, hxn]
      ring
    by_cases hdiv : n ≤ D.host.conj • p
    · obtain ⟨n', rfl⟩ := Ideal.dvd_iff_le.2 hdiv
      refine ⟨n', fun h0 => hn (by rw [h0, Ideal.mul_bot]), ?_, ?_⟩
      · rw [conj_smul_mul] at hcop
        exact (hcop.of_mul_left_right).of_mul_right_right
      · simp only [conj_smul_mul, conj_smul_smul] at hxn ⊢
        calc p * x * D.host.conj • n' = x * p * D.host.conj • n' := by ring
          _ = D.host.conj • p * n' * D.host.conj • x := by rw [mul_assoc, hxn]
          _ = n' * (D.host.conj • p * D.host.conj • x) := by ring
    · refine ⟨p * n, mul_ne_zero hpb hn, ?_, ?_⟩
      · have hnot : ¬ D.host.conj • n ≤ p := fun h => hdiv (by
          have := conj_smul_mono D h
          rwa [conj_smul_smul] at this)
        have c1 : IsCoprime p (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • p := hpM.eq_of_le hne le_sup_left
          exact hfix (hsM.eq_of_le hpM.ne_top (le_sup_right.trans h3.ge))
        have c2 : IsCoprime p (D.host.conj • n) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • n := hpM.eq_of_le hne le_sup_left
          exact hnot (le_sup_right.trans h3.ge)
        have c3 : IsCoprime n (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
          by_contra hne
          have h3 : D.host.conj • p = D.host.conj • p ⊔ n := hsM.eq_of_le hne le_sup_left
          exact hdiv (le_sup_right.trans h3.ge)
        rw [conj_smul_mul]
        exact IsCoprime.mul_left (IsCoprime.mul_right c1 c2) (IsCoprime.mul_right c3 hcop)
      · rw [conj_smul_mul, conj_smul_mul]
        calc p * x * (D.host.conj • p * D.host.conj • n) = p * D.host.conj • p * (x * D.host.conj • n) := by ring
          _ = p * D.host.conj • p * (n * D.host.conj • x) := by rw [hxn]
          _ = p * n * (D.host.conj • p * D.host.conj • x) := by ring

/- English proof (translation)
Introduce `_` and use `⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩`.
-/
theorem zeroAt_zero' (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

/- English proof (translation)
Introduce `q _ _ i j` and use `by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero' D q`.
-/
theorem suppSplit_one' (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero' D q

/- English proof (translation)
Establish `e : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) = ((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))`. Rewrite using `[div_eq_div_iff (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔪)) (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔫)), ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul, h]`. Unfold `skewLat`. Rewrite using `[e]`.
-/
theorem skewLat_eq (D : D7) {𝔪 𝔫 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (h𝔫 : 𝔫 ≠ ⊥)
    (h : 𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪) (N : ℕ) : skewLat D 𝔪 N = skewLat D 𝔫 N := by
  have e : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) =
      ((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
    rw [div_eq_div_iff (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔪))
      (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔫)), ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul, h]
  unfold skewLat
  rw [e]

/- English proof (translation)
Introduce `D δ hc a d e0 he W 𝔪 h𝔪 r hr c hrc`. Establish `h1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `hT` using `VacMove.vac_TT h1 hc he`. Take `⟨𝔫, h𝔫, hcop, hmn⟩` from `coprime_rep D 𝔪 h𝔪`. Rewrite using `[skewLat_eq D h𝔪 h𝔫 hmn d]`.

Take `⟨g', x', hg's, hg'm, hx'q, hx'd⟩` from `GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔫 h𝔫 hcop d`. Establish `hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0`. Rewrite using `[W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔫 d) (suppSplit_one' D a) hg's (fun q hq hi => ⟨by simpa using zeroAt_zero' D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]`. Both sides reduce to the same expression. Establish `hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0`. Rewrite using `[hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Establish `e1` using `W.mul r 1 1 g' e0 hT`. Establish `e2` using `W.mul 1 r g' 1 e0 hT`. Rewrite `e1` using `[mul_one, one_mul]`.

Rewrite `e2` using `[one_mul, mul_one, hrc, W.smul _ _ _ _ hT]`. Rewrite using `[hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2, smul_comm]`.
-/
theorem eig_unit : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∀ c : ℂ, W.Om r 1 e0 = c • e0 → W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = c • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr c hrc
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨𝔫, h𝔫, hcop, hmn⟩ := coprime_rep D 𝔪 h𝔪
  rw [skewLat_eq D h𝔪 h𝔫 hmn d]
  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔫 h𝔫 hcop d
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔫 d) (suppSplit_one' D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero' D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 := W.mul r 1 1 g' e0 hT
  have e2 := W.mul 1 r g' 1 e0 hT
  rw [mul_one, one_mul] at e1
  rw [one_mul, mul_one, hrc, W.smul _ _ _ _ hT] at e2
  rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2, smul_comm]

end GlobalTheory.FunObj.EigUnit
