import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Establish `h` using `Measure.map_apply (μ := X.muN u) (measurable_const_mul a) hA`. Rewrite `h` using `[(X.muN_haar u).2.2.2 a ha]`. Conclude with `h.symm`.
-/
theorem muN_preimage (a : X.B.I.Ginf) (ha : a ∈ X.NinfU u) {A : Set X.B.I.Ginf} (hA : MeasurableSet A) :
    X.muN u {y | a * y ∈ A} = X.muN u A := by
  have h := Measure.map_apply (μ := X.muN u) (measurable_const_mul a) hA
  rw [(X.muN_haar u).2.2.2 a ha] at h
  exact h.symm

end Gen

/- English proof (translation)
Introduce `D X u Γ Ω Ω' hsub hc hΩ hΩ'`. Establish `hcs : (Γ : Set X.B.I.Ginf).Countable` using `Set.countable_coe_iff.1 hc`. Establish `hun : ∀ (P : Set X.B.I.Ginf), IsSFund X.B.I Γ P → ∀ n, ∀ a ∈ (Γ : Set X.B.I.Ginf), ∀ a' ∈ (Γ : Set X.B.I.Ginf), a * n ∈ P → a' * n ∈ P → a = a'`. Introduce `P hP n a ha a' ha' h1 h2`. Establish `h3 : (a' * a⁻¹) * (a * n) ∈ P` using `by simpa [mul_assoc] using h2`.

Use `hP.2.2 _ h1 _ (Γ.mul_mem ha' (Γ.inv_mem ha)) h3` as an intermediate fact. Conclude with `(mul_inv_eq_one.1 this).symm`. Rewrite using `[Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω Ω' (X.muN u) hcs hΩ.1 hΩ'.1 hΩ'.2.1 (hun Ω' hΩ'), Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω' Ω (X.muN u) hcs hΩ'.1 hΩ.1 hΩ.2.1 (hun Ω hΩ)]`. Establish `hterm : ∀ a : (Γ : Set X.B.I.Ginf), X.muN u (Ω ∩ {n | (a : X.B.I.Ginf) * n ∈ Ω'}) = X.muN u (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω})`. Introduce `a`.

Establish `hS : MeasurableSet (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω})` using `hΩ'.1.inter ((measurable_const_mul _) hΩ.1)`. Rewrite using `[← muN_preimage X u (a : X.B.I.Ginf) (hsub a.2) hS]`. Use `congr 1`. Use extensionality with `n`. Simplify using `[and_comm]`.

Repeatedly rewrite using `[hterm]`. Set `e : (Γ : Set X.B.I.Ginf) ≃ (Γ : Set X.B.I.Ginf)` to `⟨fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩, fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩, fun a => by simp, fun a => by simp⟩`. Conclude with `e.tsum_eq (fun b : (Γ : Set X.B.I.Ginf) => X.muN u (Ω' ∩ {m | (b : X.B.I.Ginf) * m ∈ Ω}))`.
-/
theorem fundMeasEqC_holds : FundMeasEqC := by
  intro D X u Γ Ω Ω' hsub hc hΩ hΩ'
  have hcs : (Γ : Set X.B.I.Ginf).Countable := Set.countable_coe_iff.1 hc
  have hun : ∀ (P : Set X.B.I.Ginf), IsSFund X.B.I Γ P → ∀ n, ∀ a ∈ (Γ : Set X.B.I.Ginf), ∀ a' ∈ (Γ : Set X.B.I.Ginf),
      a * n ∈ P → a' * n ∈ P → a = a' := by
    intro P hP n a ha a' ha' h1 h2
    have h3 : (a' * a⁻¹) * (a * n) ∈ P := by simpa [mul_assoc] using h2
    have := hP.2.2 _ h1 _ (Γ.mul_mem ha' (Γ.inv_mem ha)) h3
    exact (mul_inv_eq_one.1 this).symm
  rw [Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω Ω' (X.muN u) hcs hΩ.1 hΩ'.1 hΩ'.2.1
      (hun Ω' hΩ'),
    Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω' Ω (X.muN u) hcs hΩ'.1 hΩ.1 hΩ.2.1 (hun Ω hΩ)]
  have hterm : ∀ a : (Γ : Set X.B.I.Ginf),
      X.muN u (Ω ∩ {n | (a : X.B.I.Ginf) * n ∈ Ω'}) =
        X.muN u (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) := by
    intro a
    have hS : MeasurableSet (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) :=
      hΩ'.1.inter ((measurable_const_mul _) hΩ.1)
    rw [← muN_preimage X u (a : X.B.I.Ginf) (hsub a.2) hS]
    congr 1
    ext n
    simp [and_comm]
  simp_rw [hterm]
  let e : (Γ : Set X.B.I.Ginf) ≃ (Γ : Set X.B.I.Ginf) :=
    ⟨fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩, fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩,
      fun a => by simp, fun a => by simp⟩
  exact e.tsum_eq (fun b : (Γ : Set X.B.I.Ginf) => X.muN u (Ω' ∩ {m | (b : X.B.I.Ginf) * m ∈ Ω}))

/- English proof (translation)
Introduce `D X u Γ Γ' Ω hle hsub hc hk hΩ`. Use `set H : Subgroup Γ := Γ'.subgroupOf Γ with hH`. Establish `: H.FiniteIndex` using `⟨hk⟩`. Establish `: Finite (Γ ⧸ H)` using `Subgroup.finite_quotient_of_finiteIndex`. Use `haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _`.

Set `r : Γ ⧸ H → Γ` to `fun q => Quotient.out q`. Establish `hr : ∀ q, ((r q : Γ) : Γ ⧸ H) = q` using `fun q => Quotient.out_eq q`. Set `A : Γ ⧸ H → Set X.B.I.Ginf` to `fun q => {y | ((r q : Γ) : X.B.I.Ginf) * y ∈ Ω}`. Establish `hA : ∀ q, MeasurableSet (A q)` using `fun q => (measurable_const_mul _) hΩ.1`. Establish `key : ∀ (a b : Γ) (y : X.B.I.Ginf), (a : X.B.I.Ginf) * y ∈ Ω → (b : X.B.I.Ginf) * y ∈ Ω → a = b`.

Introduce `a b y ha hb`. Establish `h3 : ((b : X.B.I.Ginf) * (a : X.B.I.Ginf)⁻¹) * ((a : X.B.I.Ginf) * y) ∈ Ω`. Simplify `hb` using `[mul_assoc]`. Use `hΩ.2.2 _ ha _ (Γ.mul_mem b.2 (Γ.inv_mem a.2)) h3` as an intermediate fact. Conclude with `Subtype.ext (mul_inv_eq_one.1 this).symm`.

Use `⟨⋃ q, A q, ⟨MeasurableSet.iUnion hA, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨s, hs, hsx⟩` from `hΩ.2.1 x`. Set `sΓ : Γ` to `⟨s, hs⟩`. Establish `hq : (r (sΓ : Γ ⧸ H))⁻¹ * sΓ ∈ H` using `QuotientGroup.eq.1 (hr _)`.

Use `⟨(((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf), Subgroup.mem_subgroupOf.1 hq, ?_⟩` and prove the remaining obligations. Use `Set.mem_iUnion.2 ⟨(sΓ : Γ ⧸ H), ?_⟩` and prove the remaining obligations. Use `show ((r (sΓ : Γ ⧸ H) : Γ) : X.B.I.Ginf) * ((((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf) * x) ∈ Ω`. Simplify `hsx` using `[mul_assoc, sΓ]`. Introduce `x hx s hs hsx`.

Take `⟨q, hq⟩` from `Set.mem_iUnion.1 hx`. Take `⟨p, hp⟩` from `Set.mem_iUnion.1 hsx`. Set `sΓ : Γ` to `⟨s, hle hs⟩`. Establish `hp0 : ((r p : Γ) : X.B.I.Ginf) * (s * x) ∈ Ω` using `hp`. Establish `hp' : ((r p * sΓ : Γ) : X.B.I.Ginf) * x ∈ Ω`.

Simplify `hp0` using `[mul_assoc, sΓ]`. Establish `e1 : r p * sΓ = r q` using `key _ _ x hp' hq`. Establish `e2 : sΓ = (r p)⁻¹ * r q` using `by rw [← e1]; group`. Establish `hmem : (r p)⁻¹ * r q ∈ H`. Rewrite using `[← e2]`.

Conclude with `Subgroup.mem_subgroupOf.2 hs`. Establish `hpq : p = q`. Use `QuotientGroup.eq.2 hmem` as an intermediate fact. Rewrite `this` using `[hr, hr]`. Conclude with `this`.

Substitute `hpq` using the available equality. Establish `: sΓ = 1` using `by rw [e2]; group`. Conclude with `congrArg Subtype.val this`. Establish `hdisj : Pairwise (Function.onFun Disjoint A)`. Introduce `p q hpq`.

Use `Set.disjoint_left.2 fun y hy1 hy2 => hpq ?_` and prove the remaining obligations. Use `key _ _ y hy1 hy2` as an intermediate fact. Rewrite using `[← hr p, ← hr q, this]`. Rewrite using `[measure_iUnion hdisj hA, tsum_fintype]`. Establish `hterm : ∀ q, X.muN u (A q) = X.muN u Ω` using `fun q => muN_preimage X u _ (hsub (r q).2) hΩ.1`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `congr 1`. Rewrite using `[Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]`.
-/
theorem indexVolC_holds : IndexVolC := by
  intro D X u Γ Γ' Ω hle hsub hc hk hΩ
  set H : Subgroup Γ := Γ'.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hk⟩
  have : Finite (Γ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let r : Γ ⧸ H → Γ := fun q => Quotient.out q
  have hr : ∀ q, ((r q : Γ) : Γ ⧸ H) = q := fun q => Quotient.out_eq q
  let A : Γ ⧸ H → Set X.B.I.Ginf := fun q => {y | ((r q : Γ) : X.B.I.Ginf) * y ∈ Ω}
  have hA : ∀ q, MeasurableSet (A q) := fun q => (measurable_const_mul _) hΩ.1

  have key : ∀ (a b : Γ) (y : X.B.I.Ginf), (a : X.B.I.Ginf) * y ∈ Ω → (b : X.B.I.Ginf) * y ∈ Ω → a = b := by
    intro a b y ha hb
    have h3 : ((b : X.B.I.Ginf) * (a : X.B.I.Ginf)⁻¹) * ((a : X.B.I.Ginf) * y) ∈ Ω := by
      simpa [mul_assoc] using hb
    have := hΩ.2.2 _ ha _ (Γ.mul_mem b.2 (Γ.inv_mem a.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  refine ⟨⋃ q, A q, ⟨MeasurableSet.iUnion hA, ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
    let sΓ : Γ := ⟨s, hs⟩
    have hq : (r (sΓ : Γ ⧸ H))⁻¹ * sΓ ∈ H := QuotientGroup.eq.1 (hr _)
    refine ⟨(((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf), Subgroup.mem_subgroupOf.1 hq, ?_⟩
    refine Set.mem_iUnion.2 ⟨(sΓ : Γ ⧸ H), ?_⟩
    show ((r (sΓ : Γ ⧸ H) : Γ) : X.B.I.Ginf) * ((((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf) * x) ∈ Ω
    simpa [mul_assoc, sΓ] using hsx
  · intro x hx s hs hsx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hsx
    let sΓ : Γ := ⟨s, hle hs⟩
    have hp0 : ((r p : Γ) : X.B.I.Ginf) * (s * x) ∈ Ω := hp
    have hp' : ((r p * sΓ : Γ) : X.B.I.Ginf) * x ∈ Ω := by
      simpa [mul_assoc, sΓ] using hp0
    have e1 : r p * sΓ = r q := key _ _ x hp' hq
    have e2 : sΓ = (r p)⁻¹ * r q := by rw [← e1]; group
    have hmem : (r p)⁻¹ * r q ∈ H := by
      rw [← e2]; exact Subgroup.mem_subgroupOf.2 hs
    have hpq : p = q := by
      have := QuotientGroup.eq.2 hmem
      rw [hr, hr] at this
      exact this
    subst hpq
    have : sΓ = 1 := by rw [e2]; group
    exact congrArg Subtype.val this
  · have hdisj : Pairwise (Function.onFun Disjoint A) := by
      intro p q hpq
      refine Set.disjoint_left.2 fun y hy1 hy2 => hpq ?_
      have := key _ _ y hy1 hy2
      rw [← hr p, ← hr q, this]
    rw [measure_iUnion hdisj hA, tsum_fintype]
    have hterm : ∀ q, X.muN u (A q) = X.muN u Ω := fun q =>
      muN_preimage X u _ (hsub (r q).2) hΩ.1
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Formalism.L2.SG.Pf.IdMeet
