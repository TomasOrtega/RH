import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TpDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private noncomputable def UpperTheory.V.Pa.phDecD {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) : S.Bh →+ S.F where
  toFun b := Φ (b • y) - S.rF b * Φ y
  map_zero' := by simp
  map_add' b b' := by rw [add_smul, map_add, map_add]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.Pa.phDecD_apply {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) (b : S.Bh) :
    phDecD S Φ y b = Φ (b • y) - S.rF b * Φ y := rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `hΦ`. Establish `hm : ∀ q ∈ maximalIdeal S.Bh, S.rF q = 0` using `fun q hq => by`. Rewrite `hq` using `[← S.rF_ker]`. Conclude with `hq`. Establish `dec : ∀ b : S.Bh, ∃ (o : S.OO) (q : S.Bh), q ∈ maximalIdeal S.Bh ∧ b = algebraMap S.OO S.Bh o + q`.

Introduce `b`. Take `⟨o, ho⟩` from `S.oo_surj (S.rF b)`. Use `⟨o, b - algebraMap S.OO S.Bh o, ?_, by ring⟩` and prove the remaining obligations. Rewrite using `[← S.rF_ker, RingHom.mem_ker, map_sub, ← ho]`. Simplify using the standard rewrite rules.

Use `⟨fun b b' => ?_, fun o => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨o, q, hq, rfl⟩` from `dec b`. Take `⟨o', q', hq', rfl⟩` from `dec b'`. Establish `hqq : q * q' ∈ S.J2`. Use `Ideal.mem_sup_left (Ideal.mem_sup_right ?_)` and prove the remaining obligations.

Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hq hq'`. Establish `e : ((algebraMap S.OO S.Bh o + q) * (algebraMap S.OO S.Bh o' + q')) • y = algebraMap S.OO S.Bh o • (algebraMap S.OO S.Bh o' • y) + algebraMap S.OO S.Bh o • (q' • y) + algebraMap S.OO S.Bh o' • (q • y) + (q * q') • y`. Simplify using `only [smul_smul, ← add_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [phDecD_apply]`. Rewrite using `[e]`. Simplify using `only [add_smul, map_add, map_mul, h1, h2 _ hqq, hm q hq, hm q' hq']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[phDecD_apply, h1, sub_self]`. Rewrite using `[phDecD_apply, h2 b (Ideal.mem_sup_right hb), hm b ((prAdd l S).2.2.2.2.2.1 hb)]`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.Pa.phDecD_mem {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (hΦ : Φ ∈ S.Ph)
    (y : S.U.N) : phDecD S Φ y ∈ S.Tp := by
  obtain ⟨h1, h2⟩ := hΦ
  have hm : ∀ q ∈ maximalIdeal S.Bh, S.rF q = 0 := fun q hq => by
    rw [← S.rF_ker] at hq; exact hq
  have dec : ∀ b : S.Bh, ∃ (o : S.OO) (q : S.Bh), q ∈ maximalIdeal S.Bh ∧ b = algebraMap S.OO S.Bh o + q := by
    intro b
    obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
    refine ⟨o, b - algebraMap S.OO S.Bh o, ?_, by ring⟩
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ← ho]
    simp
  refine ⟨fun b b' => ?_, fun o => ?_, fun b hb => ?_⟩
  · obtain ⟨o, q, hq, rfl⟩ := dec b
    obtain ⟨o', q', hq', rfl⟩ := dec b'
    have hqq : q * q' ∈ S.J2 := by
      refine Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul hq hq'
    have e : ((algebraMap S.OO S.Bh o + q) * (algebraMap S.OO S.Bh o' + q')) • y =
        algebraMap S.OO S.Bh o • (algebraMap S.OO S.Bh o' • y) + algebraMap S.OO S.Bh o • (q' • y) +
          algebraMap S.OO S.Bh o' • (q • y) + (q * q') • y := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    simp only [phDecD_apply]
    rw [e]
    simp only [add_smul, map_add, map_mul, h1, h2 _ hqq, hm q hq, hm q' hq']
    ring
  · rw [phDecD_apply, h1, sub_self]
  · rw [phDecD_apply, h2 b (Ideal.mem_sup_right hb), hm b ((prAdd l S).2.2.2.2.2.1 hb)]
    simp

/- English proof (translation)
Set `ev : T →ₗ[F] F` to `{ toFun := fun α => (α : A →+ F) b map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Express the relevant statement in the definitionally equal form `ev d = ∑ k, ev (v k) * v.coord k d`. Use `conv_lhs => rw [← v.sum_repr d, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply]`.
-/
private theorem UpperTheory.V.Pa.phDec_expand {F A : Type} [Field F] [AddCommGroup A] (T : Submodule F (A →+ F)) {e : ℕ}
    (v : Module.Basis (Fin e) F T) (d : T) (b : A) :
    (d : A →+ F) b = ∑ k, (v k : A →+ F) b * v.coord k d := by
  let ev : T →ₗ[F] F :=
    { toFun := fun α => (α : A →+ F) b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev d = ∑ k, ev (v k) * v.coord k d
  conv_lhs => rw [← v.sum_repr d, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply]

/- English proof (translation)
Introduce `l _ S Φ hΦ`. Establish `: Module.Finite S.F S.Tp` using `(tpDual l S).1`. Set `v` to `Module.finBasis S.F S.Tp`. Set `D : S.U.N →+ S.Tp` to `{ toFun := fun y => ⟨phDecD S Φ y, phDecD_mem S Φ hΦ y⟩ map_zero' := by`. Use `Subtype.ext (AddMonoidHom.ext fun b => ?_)` and prove the remaining obligations.

Simplify using `[phDecD_apply]`. Use the proof step `map_add' := fun y y' => by`. Use `Subtype.ext (AddMonoidHom.ext fun b => ?_)` and prove the remaining obligations. Simplify using `only [Submodule.coe_add, AddMonoidHom.add_apply, phDecD_apply, smul_add, map_add]`. Use `ring }`.

Establish `hD : ∀ y b, (D y : S.Bh →+ S.F) b = Φ (b • y) - S.rF b * Φ y` using `fun _ _ => rfl`. Establish `hs : ∀ (c : S.Bh) y, D (c • y) = S.rF c • D y`. Introduce `c y`. Use `Subtype.ext (AddMonoidHom.ext fun b => ?_)` and prove the remaining obligations. Use `(D y).2.1 b c` as an intermediate fact.

Rewrite `this` using `[hD, hD, hD, map_mul]`. Rewrite using `[Submodule.coe_smul, AddMonoidHom.smul_apply, hD, hD, smul_smul, smul_eq_mul]`. Take the linear combination `this`. Use `⟨_, fun k => v k, fun k => (v.coord k).toAddMonoidHom.comp D, fun k => (v k).2, fun k c y => ?_, fun b y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `v.coord k (D (c • y)) = S.rF c * v.coord k (D y)`.

Rewrite using `[hs, map_smul, smul_eq_mul]`. Use `phDec_expand S.Tp v (D y) b` as an intermediate fact. Rewrite `this` using `[hD]`. Express the relevant statement in the definitionally equal form `Φ (b • y) = S.rF b * Φ y + ∑ k, (v k : S.Bh →+ S.F) b * v.coord k (D y)`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Pa.phDec :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Φ ∈ S.Ph, ∃ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) ∧ (∀ k, μ k ∈ S.La) ∧ ∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y := by
  intro l _ S Φ hΦ
  have : Module.Finite S.F S.Tp := (tpDual l S).1
  let v := Module.finBasis S.F S.Tp
  let D : S.U.N →+ S.Tp :=
    { toFun := fun y => ⟨phDecD S Φ y, phDecD_mem S Φ hΦ y⟩
      map_zero' := by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp [phDecD_apply]
      map_add' := fun y y' => by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, phDecD_apply, smul_add, map_add]
        ring }
  have hD : ∀ y b, (D y : S.Bh →+ S.F) b = Φ (b • y) - S.rF b * Φ y := fun _ _ => rfl
  have hs : ∀ (c : S.Bh) y, D (c • y) = S.rF c • D y := by
    intro c y
    refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
    have := (D y).2.1 b c
    rw [hD, hD, hD, map_mul] at this
    rw [Submodule.coe_smul, AddMonoidHom.smul_apply, hD, hD, smul_smul, smul_eq_mul]
    linear_combination this
  refine ⟨_, fun k => v k, fun k => (v.coord k).toAddMonoidHom.comp D, fun k => (v k).2, fun k c y => ?_,
    fun b y => ?_⟩
  · change v.coord k (D (c • y)) = S.rF c * v.coord k (D y)
    rw [hs, map_smul, smul_eq_mul]
  · have := phDec_expand S.Tp v (D y) b
    rw [hD] at this
    change Φ (b • y) = S.rF b * Φ y + ∑ k, (v k : S.Bh →+ S.F) b * v.coord k (D y)
    rw [← this]
    ring
