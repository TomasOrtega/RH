import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo

namespace PositivityTheory.HtPt.KtwS

open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial

noncomputable section

universe u v w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨twistBundle S x 0, rfl⟩`. Consider the case `succ n ih`. Take `⟨Q', hQ'⟩` from `ih`. Take `⟨Q'', hQ''⟩` from `hLT S Ω N x Q' Q`.

Conclude with `⟨Q'', by rw [hQ'', hQ']; rfl⟩`.
-/
theorem exists_lineBundle_pow (hLT : LineTwist.Statement.{u, w}) (Q : LineBundle S x) (n : ℕ) :
    ∃ Q' : LineBundle S x, Q'.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨twistBundle S x 0, rfl⟩
  | succ n ih =>
    obtain ⟨Q', hQ'⟩ := ih
    obtain ⟨Q'', hQ''⟩ := hLT S Ω N x Q' Q
    exact ⟨Q'', by rw [hQ'', hQ']; rfl⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `exists_lineBundle_pow hLT M a`. Take `⟨Q, hQ⟩` from `hLT S Ω N x P (twistBundle S x c)`. Conclude with `⟨Q, by rw [hQ, hP]; rfl⟩`.
-/
theorem exists_lineBundle_twistMulOf (hLT : LineTwist.Statement.{u, w}) (M : LineBundle S x) (a : ℕ)
    (c : ℤ) : ∃ Q : LineBundle S x, Q.toSubSystem = twistMul M.toSubSystem a c := by
  obtain ⟨P, hP⟩ := exists_lineBundle_pow hLT M a
  obtain ⟨Q, hQ⟩ := hLT S Ω N x P (twistBundle S x c)
  exact ⟨Q, by rw [hQ, hP]; rfl⟩

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Take `⟨r', hr'⟩` from `hRT.1 S Ω N x K' y hxy hle 0`. Conclude with `⟨twistBundle S x 0, twistBundle S y 0, r', rfl, rfl, hr'⟩`. Consider the case `succ n ih`.

Take `⟨Q, Q', r', hQ, hQ', hr⟩` from `ih`. Take `⟨Qn, hQn⟩` from `hLT S Ω N x Q M`. Take `⟨Qn', hQn'⟩` from `hLT S K' N y Q' M'`. Take `⟨r'', hr''⟩` from `hRT.2 S Ω N x K' y hxy Q M Q' M' r' r hr h`. Use `⟨Qn, Qn', r'', by rw [hQn, hQ]; rfl, by rw [hQn', hQ']; rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[hQn, hQn']`. Conclude with `hr''`.
-/
theorem exists_restrict_pow (hLT : LineTwist.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y)
    (M : LineBundle S x) (M' : LineBundle S y) (r : Ω → K')
    (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'), Q.toSubSystem = M.toSubSystem.pow n ∧
      Q'.toSubSystem = M'.toSubSystem.pow n ∧ RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  induction n with
  | zero =>
    obtain ⟨r', hr'⟩ := hRT.1 S Ω N x K' y hxy hle 0
    exact ⟨twistBundle S x 0, twistBundle S y 0, r', rfl, rfl, hr'⟩
  | succ n ih =>
    obtain ⟨Q, Q', r', hQ, hQ', hr⟩ := ih
    obtain ⟨Qn, hQn⟩ := hLT S Ω N x Q M
    obtain ⟨Qn', hQn'⟩ := hLT S K' N y Q' M'
    obtain ⟨r'', hr''⟩ := hRT.2 S Ω N x K' y hxy Q M Q' M' r' r hr h
    refine ⟨Qn, Qn', r'', by rw [hQn, hQ]; rfl, by rw [hQn', hQ']; rfl, ?_⟩
    rw [hQn, hQn']
    exact hr''

/- English proof (translation)
Take `⟨P, P', rP, hP, hP', hrP⟩` from `exists_restrict_pow hLT hRT hxy hle M M' r h a`. Take `⟨rc, hrc⟩` from `hRT.1 S Ω N x K' y hxy hle c`. Take `⟨L, hL⟩` from `hLT S Ω N x P (twistBundle S x c)`. Take `⟨L', hL'⟩` from `hLT S K' N y P' (twistBundle S y c)`. Take `⟨rL, hrL⟩` from `hRT.2 S Ω N x K' y hxy P (twistBundle S x c) P' (twistBundle S y c) rP rc hrP hrc`.

Take `⟨Q, Q', r', hQ, hQ', hr'⟩` from `exists_restrict_pow hLT hRT hxy hle L L' rL (by rw [hL, hL']; exact hrL) b`. Use `⟨Q, Q', r', ?_, ?_, hr'⟩` and prove the remaining obligations. Rewrite using `[hQ, hL, hP]`. Both sides reduce to the same expression. Rewrite using `[hQ', hL', hP']`.

Both sides reduce to the same expression.
-/
theorem exists_restrict_twistMul_pow (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (a : ℕ) (c : ℤ) (b : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'),
      Q.toSubSystem = (twistMul M.toSubSystem a c).pow b ∧
      Q'.toSubSystem = (twistMul M'.toSubSystem a c).pow b ∧
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  obtain ⟨P, P', rP, hP, hP', hrP⟩ := exists_restrict_pow hLT hRT hxy hle M M' r h a
  obtain ⟨rc, hrc⟩ := hRT.1 S Ω N x K' y hxy hle c
  obtain ⟨L, hL⟩ := hLT S Ω N x P (twistBundle S x c)
  obtain ⟨L', hL'⟩ := hLT S K' N y P' (twistBundle S y c)
  obtain ⟨rL, hrL⟩ := hRT.2 S Ω N x K' y hxy P (twistBundle S x c) P' (twistBundle S y c) rP rc hrP hrc
  obtain ⟨Q, Q', r', hQ, hQ', hr'⟩ := exists_restrict_pow hLT hRT hxy hle L L' rL
    (by rw [hL, hL']; exact hrL) b
  refine ⟨Q, Q', r', ?_, ?_, hr'⟩
  · rw [hQ, hL, hP]; rfl
  · rw [hQ', hL', hP']; rfl

end Helpers

section OnW

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Take `⟨j, hjp⟩` from `hrel`. Establish `hj : x j ≠ 0` using `fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr (by rw [aeval_X]; exact h0)))`. Take `⟨hcp, hpt⟩` from `hPt k Ω N x pp hpr hhom hle j hj hjp`. Use `hcp` as an intermediate fact. Set `A` to `chartRing k x (singleChart hj)`.

Set `I : Ideal A` to `chartPrime pp hj`. Set `ψ : A →ₐ[k] I.ResidueField` to `IsScalarTower.toAlgHom k A I.ResidueField`. Establish `hker : RingHom.ker ψ = I` using `Ideal.ker_algebraMap_residueField I`. Establish `hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0`. Introduce `i h hx`.

Apply `h` to reduce the goal to its premises. Establish `h0 : ratio (S` using `k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])`. Rewrite using `[h0, map_zero]`. Establish `hpy : primeOf (S` using `k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker`. Establish `hxy' : primeOf (S` using `k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle`.

Take `⟨f, e₀, hfJ, hfh, hfq⟩` from `hJP k Ω N x T`. Take `⟨e, he, hsub⟩` from `hDrop k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hJ f e₀ hfJ hfh, hfq⟩`. Establish `hsubW : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S` using `k) (fun i => ψ (ratio hj i))) e := by`. Rewrite using `[hpy]`. Conclude with `⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩`.

Take `⟨M', rM, hM'⟩` from `hRes k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M`. Establish `hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM` using `⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩`. Establish `hnef : Nef M'.toSubSystem` using `hNR k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef`. Establish `hts : 0 < T.t - T.s'`. Establish `hd : (1 : ℚ) ≤ (T.d : ℚ) + 1`.

Use `(Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht : 0 < T.t`. Assume the negation of the conclusion as `hneg'`. Establish `hneg : T.t ≤ 0` using `not_lt.mp hneg'`.

Establish `: T.t / ((T.d : ℚ) + 1) ≤ 0` using `div_nonpos_of_nonpos_of_nonneg hneg (by positivity)`. Combine the linear relations using `[T.s'_pos, T.s'_lt]`. Establish `: T.t / ((T.d : ℚ) + 1) ≤ T.t` using `div_le_self ht.le hd`. Combine the linear relations using `[T.s'_lt]`. Take `⟨q, m', hq, hm', hva⟩` from `hK e he _ N _ M' hsubW hnef (T.t - T.s') hts`.

Take `⟨rr, h, hvb⟩` from `hva`. Establish `hqm : (q : ℤ) * T.m = T.p * m'`. Establish `: (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ)` using `by push_cast; rw [T.m_eq, hm']; ring`. Conclude with `this` after adjusting the coercions. Take `⟨B, hB⟩` from `exists_lineBundle_twistMulOf hLT M' q m'`.

Take `⟨L', hL'⟩` from `exists_lineBundle_twistMulOf hLT M' T.p T.m`. Establish `hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ (b' : ℕ) (c : ℤ), c₀ ≤ c → Subsingleton (((((twistMul M'.toSubSystem T.p T.m).pow b₂).twist ((twistMul M'.toSubSystem q m').pow b')).twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1)`. Introduce `b₂`. Take `⟨G, hG⟩` from `exists_lineBundle_pow hLT L' b₂`. Take `⟨c₀, hc₀⟩` from `hTV k _ N _ G B rr h (fun l => by rw [hB]; exact hvb.mem_secs l) (fun I => by rw [hB]; exact hvb.generates I)`.

Use `⟨c₀, fun b' c hc => ?_⟩` and prove the remaining obligations. Establish `hs` using `hc₀ b' c hc`. Rewrite `hs` using `[hG, hL', hB]`. Then use the resulting hypothesis. Use `choose cv hcv using hv`. Use `⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b Q hQ c hc => ?_⟩` and prove the remaining obligations.

Take `⟨Qb, Qb', r', hQb, hQb', hrd⟩` from `exists_restrict_twistMul_pow hLT hRT hxy hxy' T.M M' rM hRM T.p T.m b`. Take `⟨eqv⟩` from `hRQ k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy Qb Qb' r' hrd c 1`. Establish `hQbQ : Qb.toSubSystem = Q.toSubSystem` using `by rw [hQb, hQ]; rfl`. Establish `hW : Qb'.toSubSystem = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist ((twistMul M'.toSubSystem q m').pow (T.p * (b / q)))`. Rewrite using `[hQb', ← hTA k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]`.

Establish `hlt : b % q < q` using `Nat.mod_lt b (by omega)`. Establish `hcb : cv (b % q) ≤ c` using `le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)`. Establish `hs : Subsingleton ((Qb'.twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1)`. Rewrite using `[hW]`. Conclude with `hcv (b % q) (T.p * (b / q)) c hcb`.

Rewrite using `[← hQbQ]`. Conclude with `@Equiv.subsingleton _ _ eqv.toEquiv hs`.
-/
theorem StepTwo.onW (hLT : LineTwist.Statement.{u, w}) (hTA : TwistAlg.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hNR : NefRestrict.Statement.{u, w})
    (hJP : StepData.JProper.Statement.{u, w}) (hDrop : SubvarDrop.Statement.{u, w})
    (hPt : PrimeFiltration.Point.Statement.{u, w}) (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w})
    (T : StepData k x) (hK : ∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e)
    (pp : Ideal (Poly k N)) (hpr : pp.IsPrime) (hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp)
    (hle : primeOf (S := k) x ≤ pp) (hJ : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → f ∈ pp)
    (hrel : ∃ j, (X j : Poly k N) ∉ pp) :
    ∃ c₁ : ℤ, ∀ (b : ℕ) (Q : LineBundle k x), Q.toSubSystem = T.L.pow b → ∀ c : ℤ, c₁ ≤ c →
      Subsingleton (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 1) := by
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := hPt k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let I : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] I.ResidueField := IsScalarTower.toAlgHom k A I.ResidueField
  have hker : RingHom.ker ψ = I := Ideal.ker_algebraMap_residueField I
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := hJP k Ω N x T
  obtain ⟨e, he, hsub⟩ := hDrop k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hJ f e₀ hfJ hfh, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i))
      (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := hRes k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem := hNR k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  obtain ⟨B, hB⟩ := exists_lineBundle_twistMulOf hLT M' q m'
  obtain ⟨L', hL'⟩ := exists_lineBundle_twistMulOf hLT M' T.p T.m
  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ (b' : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        ((twistMul M'.toSubSystem q m').pow b')).twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    intro b₂
    obtain ⟨G, hG⟩ := exists_lineBundle_pow hLT L' b₂
    obtain ⟨c₀, hc₀⟩ := hTV k _ N _ G B rr h (fun l => by rw [hB]; exact hvb.mem_secs l)
      (fun I => by rw [hB]; exact hvb.generates I)
    refine ⟨c₀, fun b' c hc => ?_⟩
    have hs := hc₀ b' c hc
    rwa [hG, hL', hB] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b Q hQ c hc => ?_⟩
  obtain ⟨Qb, Qb', r', hQb, hQb', hrd⟩ :=
    exists_restrict_twistMul_pow hLT hRT hxy hxy' T.M M' rM hRM T.p T.m b
  obtain ⟨eqv⟩ := hRQ k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy Qb Qb' r' hrd c 1
  have hQbQ : Qb.toSubSystem = Q.toSubSystem := by rw [hQb, hQ]; rfl
  have hW : Qb'.toSubSystem = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [hQb', ← hTA k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hs : Subsingleton ((Qb'.twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    rw [hW]; exact hcv (b % q) (T.p * (b / q)) c hcb
  rw [← hQbQ]
  exact @Equiv.subsingleton _ _ eqv.toEquiv hs

end OnW

/- English proof (translation)
Introduce `k _ Ω _ _ N x T hK E _ _ _ _ M₁ M₂ hle hJ`. Take `⟨n, pr, sh, hpr, hred⟩` from `hRed k Ω N x E M₁ M₂ hle T.J hJ`. Establish `hLpow : ∀ b : ℕ, ∃ Q : LineBundle k x, Q.toSubSystem = T.L.pow b` using `fun b => by`. Take `⟨L, hL⟩` from `exists_lineBundle_twistMulOf hLT T.M T.p T.m`. Take `⟨Q, hQ⟩` from `exists_lineBundle_pow hLT L b`.

Conclude with `⟨Q, by rw [hQ, hL]; rfl⟩`. Use `choose Qb hQb using hLpow`. Establish `hW : ∀ i, ∃ c₁ : ℤ, (∃ j, (X j : Poly k N) ∉ pr i) → ∀ (b : ℕ) (c : ℤ), c₁ ≤ c → Subsingleton (SubSystem.quotH ((Qb b).twist (twistSys k x c)) (((Qb b).twist (twistSys k x c)).twist (idealSys x (pr i))) 1)`. Introduce `i`. Distinguish the cases in `hrel : ∃ j, (X j : Poly k N) ∉ pr i`.

Take `⟨c₁, hc₁⟩` from `StepTwo.onW hLT hTA hRT hNR hJP hDrop hPt hRes hRQ hTV T hK (pr i) (hpr i).1 (hpr i).2.1 (hpr i).2.2.1 (hpr i).2.2.2 hrel`. Conclude with `⟨c₁, fun _ b c hc => hc₁ b (Qb b) (hQb b) c hc⟩`. Conclude with `⟨0, fun h => absurd h hrel⟩`. Use `choose cw hcw using hW`. Use `⟨∑ i, |cw i - sh i|, fun b c hc => ?_⟩` and prove the remaining obligations.

Establish `hs` using `hred (Qb b) c (fun i hi => hcw i hi b (c + sh i) (by`. Establish `h1 : |cw i - sh i| ≤ ∑ i, |cw i - sh i|` using `Finset.single_le_sum (f := fun i => |cw i - sh i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)`. Establish `h2` using `le_abs_self (cw i - sh i)`. Use the proof step `linarith))`. Rewrite `hs` using `[hQb b]`. Then use the resulting hypothesis.
-/
theorem StepTwo.proof (hRed : StepTwo.Reduce.Statement.{u, v, w}) (hLT : LineTwist.Statement.{u, w})
    (hTA : TwistAlg.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hNR : NefRestrict.Statement.{u, w}) (hJP : StepData.JProper.Statement.{u, w})
    (hDrop : SubvarDrop.Statement.{u, w}) (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w}) :
    StepTwo.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x T hK E _ _ _ _ M₁ M₂ hle hJ
  obtain ⟨n, pr, sh, hpr, hred⟩ := hRed k Ω N x E M₁ M₂ hle T.J hJ
  have hLpow : ∀ b : ℕ, ∃ Q : LineBundle k x, Q.toSubSystem = T.L.pow b := fun b => by
    obtain ⟨L, hL⟩ := exists_lineBundle_twistMulOf hLT T.M T.p T.m
    obtain ⟨Q, hQ⟩ := exists_lineBundle_pow hLT L b
    exact ⟨Q, by rw [hQ, hL]; rfl⟩
  choose Qb hQb using hLpow
  have hW : ∀ i, ∃ c₁ : ℤ, (∃ j, (X j : Poly k N) ∉ pr i) → ∀ (b : ℕ) (c : ℤ), c₁ ≤ c →
      Subsingleton (SubSystem.quotH ((Qb b).twist (twistSys k x c))
        (((Qb b).twist (twistSys k x c)).twist (idealSys x (pr i))) 1) := by
    intro i
    by_cases hrel : ∃ j, (X j : Poly k N) ∉ pr i
    · obtain ⟨c₁, hc₁⟩ := StepTwo.onW hLT hTA hRT hNR hJP hDrop hPt hRes hRQ hTV T hK (pr i)
        (hpr i).1 (hpr i).2.1 (hpr i).2.2.1 (hpr i).2.2.2 hrel
      exact ⟨c₁, fun _ b c hc => hc₁ b (Qb b) (hQb b) c hc⟩
    · exact ⟨0, fun h => absurd h hrel⟩
  choose cw hcw using hW
  refine ⟨∑ i, |cw i - sh i|, fun b c hc => ?_⟩
  have hs := hred (Qb b) c (fun i hi => hcw i hi b (c + sh i) (by
    have h1 : |cw i - sh i| ≤ ∑ i, |cw i - sh i| :=
      Finset.single_le_sum (f := fun i => |cw i - sh i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (cw i - sh i)
    linarith))
  rwa [hQb b] at hs

end

end PositivityTheory.HtPt.KtwS
