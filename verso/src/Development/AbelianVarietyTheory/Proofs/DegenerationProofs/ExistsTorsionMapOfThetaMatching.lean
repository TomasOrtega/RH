import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.TorsMatch

/- English proof (translation)
Simplify using `only [NumD.txT, NumD.vt, NumD.wQ, NumB.uth, NumB.mth, NumB.uV, hp, toAdd_one, NumD.ψ_zero, NumD.Gt.s_zero, NumD.c_zero, N.cub.N_one, N.cub.face, _root_.one_mul, div_one, NumD.Gt.pow_b, Units.val_one, div_eq_mul_inv, Units.val_mul, inv_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem txT_zero {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) :
    N.txT m p 0 = N.uth m p.1.2.b 1 := by
  simp only [NumD.txT, NumD.vt, NumD.wQ, NumB.uth, NumB.mth, NumB.uV, hp, toAdd_one, NumD.ψ_zero, NumD.Gt.s_zero,
    NumD.c_zero, N.cub.N_one, N.cub.face, _root_.one_mul, div_one, NumD.Gt.pow_b, Units.val_one, div_eq_mul_inv,
    Units.val_mul, inv_one]
  ring

variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (mt : Match N N' n)

/- English proof (translation)
Substitute `hK` using the available equality. Take `⟨p', h⟩` from `mt.tot i p`. Take `⟨z, hz⟩` from `(hA.2 i p p' h).1.1 ⟨0, by rw [hp, smul_zero, toAdd_one]⟩`. Use `⟨p' * N'.qTriv _ (-z), (mt.eqv _ p p p' _ h ((N.qEq_equivalence _).refl p)).2 ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p'.1.1.toAdd + n ^ i • (-z) = 0`.

Rewrite using `[hz, smul_neg, add_neg_cancel]`.
-/
theorem exists_partner (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) (p : N.QT K) (hp : p.1.1 = 1) :
    ∃ p', mt.r K p p' ∧ p'.1.1 = 1 := by
  subst hK
  obtain ⟨p', h⟩ := mt.tot i p
  obtain ⟨z, hz⟩ := (hA.2 i p p' h).1.1 ⟨0, by rw [hp, smul_zero, toAdd_one]⟩
  refine ⟨p' * N'.qTriv _ (-z), (mt.eqv _ p p p' _ h ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ i • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

/- English proof (translation)
Substitute `hK` using the available equality. Take `⟨t, ht⟩` from `mt.tot i (p⁻¹ * q)`. Establish `hT : N.InT (p⁻¹ * q)` using `⟨_, (N.qEq_equivalence _).refl _, by`. Express the relevant statement in the definitionally equal form `p.1.1⁻¹ * q.1.1 = 1`. Rewrite using `[hp, hq, inv_mul_cancel], by`.

Express the relevant statement in the definitionally equal form `p.1.2.b⁻¹ * q.1.2.b = 1`. Rewrite using `[hb, inv_mul_cancel]⟩`. Take `⟨t', e, t1, t2⟩` from `(hA.2 i _ _ ht).2.1 hT`. Establish `r1` using `mt.mul _ _ _ _ _ h ((mt.eqv _ _ _ _ _ ht ((N.qEq_equivalence _).refl _)).2 e)`. Rewrite `r1` using `[mul_inv_cancel_left]`.

Take `⟨z, z1, z2⟩` from `(mt.eqv _ _ _ _ _ r1 ((N.qEq_equivalence _).refl _)).1 h'`. Express the relevant statement in the definitionally equal form `_ = p'.1.1.toAdd + t'.1.1.toAdd + _ at z1`. Rewrite `z1` using `[hq', hp', t1, toAdd_one, add_zero, zero_add, ← natCast_zsmul]`. Establish `hz : z = 0` using `(smul_eq_zero_iff_right (Int.natCast_ne_zero.2 (pow_ne_zero i hn))).1 z1.symm`. Rewrite `z2` using `[hz, N'.io_zero, _root_.mul_one]`.

Rewrite using `[z2]`. Express the relevant statement in the definitionally equal form `_ = p'.1.2.b * t'.1.2.b`. Rewrite using `[t2, _root_.mul_one]`.
-/
theorem partner_b (hn : n ≠ 0) (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) {p q : N.QT K} {p' q' : N'.QT K}
    (h : mt.r K p p') (h' : mt.r K q q') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) (hq : q.1.1 = 1) (hq' : q'.1.1 = 1)
    (hb : p.1.2.b = q.1.2.b) : p'.1.2.b = q'.1.2.b := by
  subst hK
  obtain ⟨t, ht⟩ := mt.tot i (p⁻¹ * q)
  have hT : N.InT (p⁻¹ * q) := ⟨_, (N.qEq_equivalence _).refl _, by
      change p.1.1⁻¹ * q.1.1 = 1
      rw [hp, hq, inv_mul_cancel], by
      change p.1.2.b⁻¹ * q.1.2.b = 1
      rw [hb, inv_mul_cancel]⟩
  obtain ⟨t', e, t1, t2⟩ := (hA.2 i _ _ ht).2.1 hT
  have r1 := mt.mul _ _ _ _ _ h ((mt.eqv _ _ _ _ _ ht ((N.qEq_equivalence _).refl _)).2 e)
  rw [mul_inv_cancel_left] at r1
  obtain ⟨z, z1, z2⟩ := (mt.eqv _ _ _ _ _ r1 ((N.qEq_equivalence _).refl _)).1 h'
  change _ = p'.1.1.toAdd + t'.1.1.toAdd + _ at z1
  rw [hq', hp', t1, toAdd_one, add_zero, zero_add, ← natCast_zsmul] at z1
  have hz : z = 0 := (smul_eq_zero_iff_right (Int.natCast_ne_zero.2 (pow_ne_zero i hn))).1 z1.symm
  rw [hz, N'.io_zero, _root_.mul_one] at z2
  rw [z2]
  change _ = p'.1.2.b * t'.1.2.b
  rw [t2, _root_.mul_one]

/- English proof (translation)
Substitute `hK` using the available equality. Use `⟨⟨(1, p.1.2), ?_⟩, ⟨(1, p'.1.2), ?_⟩, ?_, rfl, rfl, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[NumD.mem_QT, pow_mul, N.mem_QT.1 p.2, hp, toAdd_one, N.io_zero, one_pow]`. Rewrite using `[NumD.mem_QT, pow_mul, N'.mem_QT.1 p'.2, hp', toAdd_one, N'.io_zero, one_pow]`. Conclude with `(mt.incl k k' p p' _ _ hk (((congrArg (· ^ k') hp).trans (one_pow k')).symm) rfl (((congrArg (· ^ k') hp').trans (one_pow k')).symm) rfl).1 h`.
-/
theorem raise {k k' K : ℕ} (hk : k' ≠ 0) (hK : K = k * k') {p : N.QT k} {p' : N'.QT k} (h : mt.r k p p')
    (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) :
    ∃ q q', mt.r K q q' ∧ q.1.1 = 1 ∧ q'.1.1 = 1 ∧ q.1.2 = p.1.2 ∧ q'.1.2 = p'.1.2 := by
  subst hK
  refine ⟨⟨(1, p.1.2), ?_⟩, ⟨(1, p'.1.2), ?_⟩, ?_, rfl, rfl, rfl, rfl⟩
  · rw [NumD.mem_QT, pow_mul, N.mem_QT.1 p.2, hp, toAdd_one, N.io_zero, one_pow]
  · rw [NumD.mem_QT, pow_mul, N'.mem_QT.1 p'.2, hp', toAdd_one, N'.io_zero, one_pow]
  · exact (mt.incl k k' p p' _ _ hk (((congrArg (· ^ k') hp).trans (one_pow k')).symm) rfl
      (((congrArg (· ^ k') hp').trans (one_pow k')).symm) rfl).1 h

/- English proof (translation)
Take `⟨u, h, h'⟩` from `QStr.root_over N (hK ▸ pow_ne_zero i hn : K ≠ 0) 1 b hb`. Take `⟨p', r, hp'⟩` from `exists_partner mt hA i K hK ⟨(1, u), h'.trans N.io_zero.symm⟩ rfl`. Conclude with `⟨_, p', r, rfl, hp', h⟩`.
-/
theorem exists_pair [IsAlgClosed C] (hn : n ≠ 0) (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) (b : N.A) (hb : b ^ K = 1) :
    ∃ p p', mt.r K p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  obtain ⟨u, h, h'⟩ := QStr.root_over N (hK ▸ pow_ne_zero i hn : K ≠ 0) 1 b hb
  obtain ⟨p', r, hp'⟩ := exists_partner mt hA i K hK ⟨(1, u), h'.trans N.io_zero.symm⟩ rfl
  exact ⟨_, p', r, rfl, hp', h⟩

/- English proof (translation)
Use `⟨fun b => if h : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = b then h.choose.2.1.2.b else 1, ?_⟩` and prove the remaining obligations. Introduce and unpack `K rfl p p' h hp hp'`. Establish `ex : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = p.1.2.b` using `⟨(p, p'), h, hp, hp', rfl⟩`. Take `⟨a, b, c, d⟩` from `ex.choose_spec`. Use `beta_reduce`.

Rewrite using `[dif_pos ex]`. Conclude with `partner_b mt hn hA i _ rfl h a hp hp' b c d.symm`.
-/
theorem exists_map (hn : n ≠ 0) (hA : mt.A) (i : ℕ) : ∃ ρ : N.A → N'.A, ∀ K, K = n ^ i →
    ∀ p p', mt.r K p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b := by
  classical
  refine ⟨fun b => if h : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = b
    then h.choose.2.1.2.b else 1, ?_⟩
  rintro K rfl p p' h hp hp'
  have ex : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = p.1.2.b :=
    ⟨(p, p'), h, hp, hp', rfl⟩
  obtain ⟨a, b, c, d⟩ := ex.choose_spec
  beta_reduce
  rw [dif_pos ex]
  exact partner_b mt hn hA i _ rfl h a hp hp' b c d.symm

/- English proof (translation)
Introduce `C _ _ _ _ N N' q q' n g g' hp _ _ _ _ _ _ mt hA e hT j`. Establish `hn : n ≠ 0` using `hp.ne_zero`. Establish `hK : (n ^ j) ^ 2 = n ^ (2 * j)` using `by rw [← pow_mul, mul_comm]`. Take `⟨ρ, hρ⟩` from `exists_map mt hn hA (2 * j)`. Use `⟨ρ, ⟨fun b b' hb hb' => ?_, fun b hb => ?_⟩, fun i hi p p' h h1 h1' => ?_, fun b hb => ?_⟩` and prove the remaining obligations.

Take `⟨p, p', h, h1, h2, rfl⟩` from `exists_pair mt hn hA _ _ hK b hb`. Take `⟨r, r', h', h3, h4, rfl⟩` from `exists_pair mt hn hA _ _ hK b' hb'`. Rewrite using `[← hρ _ hK p p' h h1 h2, ← hρ _ hK r r' h' h3 h4]`. Use `⟨(hρ _ hK _ _ (mt.mul _ _ _ _ _ h h') ?_ ?_).symm, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p.1.1 * r.1.1 = 1`.

Rewrite using `[h1, h3, _root_.mul_one]`. Express the relevant statement in the definitionally equal form `p'.1.1 * r'.1.1 = 1`. Rewrite using `[h2, h4, _root_.mul_one]`. Rewrite using `[← N.wp_of_eq_zero p r h1 h3, ← N'.wp_of_eq_zero p' r' h2 h4]`. Conclude with `mt.wp _ _ _ _ _ h h'`.

Take `⟨p, p', h, h1, h2, rfl⟩` from `exists_pair mt hn hA _ _ hK b hb`. Rewrite using `[← hρ _ hK p p' h h1 h2]`. Use `⟨by rw [N'.QT_pow_b, h2, toAdd_one, N'.c_zero], ?_⟩` and prove the remaining obligations. Establish `t` using `hT j p p' h h1 h2 0`. Rewrite `t` using `[map_zero, txT_zero _ _ _ h1, txT_zero _ _ _ h2]`. Then use the resulting hypothesis.

Take `⟨r, r', h', h3, h4, h5, h6⟩` from `raise mt (K := n ^ (2 * j)) (pow_ne_zero (2 * j - i) hn) (by rw [← pow_add, Nat.add_sub_cancel' hi]) h h1 h1'`. Rewrite using `[← h5, ← h6]`. Conclude with `hρ _ rfl r r' h' h3 h4`. Conclude with `exists_pair mt hn hA _ _ rfl b (hK ▸ hb)`.
-/
theorem exists_torsMap : AllMatch fun {_} _ {N} {N'} {n} mt _ _ => mt.A → ∀ e, mt.Term e → ∀ j : ℕ, ∃ ρ : N.A → N'.A, TorsMap N.toNumB N'.toNumB (n ^ j) mt.c₀ ρ ∧ (∀ i, i ≤ 2 * j → ∀ p p', mt.r (n ^ i) p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b) ∧ ∀ b : N.A, b ^ (n ^ j) ^ 2 = 1 → ∃ p p', mt.r (n ^ (2 * j)) p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  intro C _ _ _ _ N N' q q' n g g' hp _ _ _ _ _ _ mt hA e hT j
  have hn : n ≠ 0 := hp.ne_zero
  have hK : (n ^ j) ^ 2 = n ^ (2 * j) := by rw [← pow_mul, mul_comm]
  obtain ⟨ρ, hρ⟩ := exists_map mt hn hA (2 * j)
  refine ⟨ρ, ⟨fun b b' hb hb' => ?_, fun b hb => ?_⟩, fun i hi p p' h h1 h1' => ?_, fun b hb => ?_⟩
  · obtain ⟨p, p', h, h1, h2, rfl⟩ := exists_pair mt hn hA _ _ hK b hb
    obtain ⟨r, r', h', h3, h4, rfl⟩ := exists_pair mt hn hA _ _ hK b' hb'
    rw [← hρ _ hK p p' h h1 h2, ← hρ _ hK r r' h' h3 h4]
    refine ⟨(hρ _ hK _ _ (mt.mul _ _ _ _ _ h h') ?_ ?_).symm, ?_⟩
    · change p.1.1 * r.1.1 = 1
      rw [h1, h3, _root_.mul_one]
    · change p'.1.1 * r'.1.1 = 1
      rw [h2, h4, _root_.mul_one]
    · rw [← N.wp_of_eq_zero p r h1 h3, ← N'.wp_of_eq_zero p' r' h2 h4]
      exact mt.wp _ _ _ _ _ h h'
  · obtain ⟨p, p', h, h1, h2, rfl⟩ := exists_pair mt hn hA _ _ hK b hb
    rw [← hρ _ hK p p' h h1 h2]
    refine ⟨by rw [N'.QT_pow_b, h2, toAdd_one, N'.c_zero], ?_⟩
    have t := hT j p p' h h1 h2 0
    rwa [map_zero, txT_zero _ _ _ h1, txT_zero _ _ _ h2] at t
  · obtain ⟨r, r', h', h3, h4, h5, h6⟩ := raise mt (K := n ^ (2 * j)) (pow_ne_zero (2 * j - i) hn)
      (by rw [← pow_add, Nat.add_sub_cancel' hi]) h h1 h1'
    rw [← h5, ← h6]
    exact hρ _ rfl r r' h' h3 h4
  · exact exists_pair mt hn hA _ _ rfl b (hK ▸ hb)

end GlobalTheory.Ex.TorsMatch
end
