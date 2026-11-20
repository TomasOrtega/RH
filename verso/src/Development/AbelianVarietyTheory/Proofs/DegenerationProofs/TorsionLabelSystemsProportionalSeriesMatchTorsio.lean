import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.LabelMatch
section
variable {O : Type} [CommRing O] {N : NumD O}

/- English proof (translation)
Take `⟨z, h1, h2⟩` from `h`. Take `⟨w, h3, h4⟩` from `h'`. Use `⟨z + w, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _`. Rewrite using `[h1, h3, smul_add]`.

Normalize the expressions using the abelian group laws. Express the relevant statement in the definitionally equal form `p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _`. Rewrite using `[h2, h4, N.io_add]`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem qEq_mul {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.QEq (p * q) (p' * q') := by
  obtain ⟨z, h1, h2⟩ := h
  obtain ⟨w, h3, h4⟩ := h'
  refine ⟨z + w, ?_, ?_⟩
  · change p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _
    rw [h1, h3, smul_add]; abel
  · change p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _
    rw [h2, h4, N.io_add]; exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Use `exists_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[a, b, c, d, toAdd_pow, toAdd_pow, mul_comm k, mul_smul, ← smul_add]`. Simplify using `only [← natCast_zsmul]`. Conclude with `and_congr_left' (smul_right_inj (Int.natCast_ne_zero.2 hk)).symm`.
-/
theorem qEq_incl {k k' : ℕ} (p p' : N.QT k) (q q' : N.QT (k * k')) (hk : k' ≠ 0)
    (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) (c : q'.1.1 = p'.1.1 ^ k') (d : q'.1.2 = p'.1.2) :
    N.QEq p p' ↔ N.QEq q q' := by
  refine exists_congr fun z => ?_
  rw [a, b, c, d, toAdd_pow, toAdd_pow, mul_comm k, mul_smul, ← smul_add]
  simp only [← natCast_zsmul]
  exact and_congr_left' (smul_right_inj (Int.natCast_ne_zero.2 hk)).symm

/- English proof (translation)
Take `⟨z, h1, h2⟩` from `h`. Conclude with `(tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2).trans ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)`.
-/
theorem tx_congr [TopologicalSpace O] {m : ℕ} (hm : Odd m) {p p' : N.QT (m ^ 2)} (h : N.QEq p p') :
    N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  exact (tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2).trans
    ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)

/- English proof (translation)
Rewrite using `[WpPairing.wp_congr_left N h, N.wp_swap q p', WpPairing.wp_congr_left N h', ← N.wp_swap]`.
-/
theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.wp p q = N.wp p' q' := by
  rw [WpPairing.wp_congr_left N h, N.wp_swap q p', WpPairing.wp_congr_left N h', ← N.wp_swap]

variable {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k}

/- English proof (translation)
Establish `E` using `N.qEq_equivalence k`. Proceed by induction on `m with`. Consider the case `zero => rw [zero_add, pow_one, one_smul]`. Conclude with `E.refl _`. Consider the case `succ m ih`.

Rewrite using `[pow_succ, succ_nsmul x (m + 1)]`. Conclude with `E.trans (qEq_mul ih (E.refl _)) (H.1 k hk _ _)`.
-/
theorem lab_pow (H : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x : La) (m : ℕ) :
    N.QEq (lab k x ^ (m + 1)) (lab k ((m + 1) • x)) := by
  have E := N.qEq_equivalence k
  induction m with
  | zero => rw [zero_add, pow_one, one_smul]; exact E.refl _
  | succ m ih =>
    rw [pow_succ, succ_nsmul x (m + 1)]
    exact E.trans (qEq_mul ih (E.refl _)) (H.1 k hk _ _)

/- English proof (translation)
Establish `hk0 : 0 < k'` using `Nat.pos_of_ne_zero hk'`. Establish `E` using `N.qEq_equivalence k`. Establish `E'` using `N.qEq_equivalence (k * k')`. Set `p₀ : N.QT k` to `⟨((lab (k * k') x).1.1, (lab (k * k') x).1.2 ^ k'), by`. Establish `h : (lab (k * k') x).1.2 ^ (k * k') = _` using `N.mem_QT.1 (lab (k * k') x).2`.

Rewrite using `[NumD.mem_QT, ← pow_mul, ← h, mul_comm k' k]⟩`. Establish `h0 : N.QEq p₀ (lab k x)` using `H.2.2.2.1 k k' hk hk0 x p₀ rfl rfl`. Establish `h1 : N.QEq (lab (k * k') x ^ k') (lab (k * k') (k' • x))`. Use `lab_pow H (Nat.mul_pos hk hk0) x (k' - 1)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hk0]`. Then use the resulting hypothesis.

Establish `h2` using `qEq_incl p₀ p (lab (k * k') x ^ k') q hk' rfl rfl a b`. Conclude with `⟨fun h => E'.trans (E'.symm h1) (h2.1 (E.trans h0 h)), fun h => E.trans (E.symm h0) (h2.2 (E'.trans h1 h))⟩`.
-/
theorem lab_incl (H : Labels N EF ζ lab) {k k' : ℕ} (hk : 0 < k) (hk' : k' ≠ 0) (x : La) (p : N.QT k)
    (q : N.QT (k * k')) (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) :
    N.QEq (lab k x) p ↔ N.QEq (lab (k * k') (k' • x)) q := by
  have hk0 : 0 < k' := Nat.pos_of_ne_zero hk'
  have E := N.qEq_equivalence k
  have E' := N.qEq_equivalence (k * k')
  let p₀ : N.QT k := ⟨((lab (k * k') x).1.1, (lab (k * k') x).1.2 ^ k'), by
    have h : (lab (k * k') x).1.2 ^ (k * k') = _ := N.mem_QT.1 (lab (k * k') x).2
    rw [NumD.mem_QT, ← pow_mul, ← h, mul_comm k' k]⟩
  have h0 : N.QEq p₀ (lab k x) := H.2.2.2.1 k k' hk hk0 x p₀ rfl rfl
  have h1 : N.QEq (lab (k * k') x ^ k') (lab (k * k') (k' • x)) := by
    have := lab_pow H (Nat.mul_pos hk hk0) x (k' - 1)
    rwa [Nat.sub_add_cancel hk0] at this
  have h2 := qEq_incl p₀ p (lab (k * k') x ^ k') q hk' rfl rfl a b
  exact ⟨fun h => E'.trans (E'.symm h1) (h2.1 (E.trans h0 h)), fun h => E.trans (E.symm h0) (h2.2 (E'.trans h1 h))⟩

/- English proof (translation)
Rewrite using `[← H.2.2.2.2 k hk, ← H.2.2.2.2 k hk]`. Conclude with `WpPairing.wp_congr_left N ((H.2.1 k hk _ _).2 ⟨e, rfl⟩) _`.
-/
theorem zeta_shift (H : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x e y : La) :
    ζ k ^ EF (x + k • e) y = ζ k ^ EF x y := by
  rw [← H.2.2.2.2 k hk, ← H.2.2.2.2 k hk]
  exact WpPairing.wp_congr_left N ((H.2.1 k hk _ _).2 ⟨e, rfl⟩) _

omit N lab in

/- English proof (translation)
Rewrite using `[map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]`.
-/
theorem zeta_tower {k k' : ℕ} (h : ζ (k * k') ^ k' = ζ k) (x y : La) :
    ζ (k * k') ^ EF (k' • x) y = ζ k ^ EF x y := by
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]
end

/- English proof (translation)
Introduce `C _ N N' La _ EF ζ ζ' lab lab' n _ hn _ H H' hζ hζ' hζn c₀ hc htx`. Establish `E` using `N.qEq_equivalence`. Establish `E'` using `N'.qEq_equivalence`. Establish `hpos : ∀ j, 0 < n ^ j` using `fun j => pow_pos hn.pos j`. Establish `tr : ∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ N'.QEq (lab' k a) (lab' k b)` using `fun k hk a b => (H.2.1 k hk a b).trans (H'.2.1 k hk a b).symm`.

Use `⟨{ r := fun k p p' => 0 < k ∧ ∃ x, N.QEq (lab k x) p ∧ N'.QEq (lab' k x) p' ∧ ∀ y, ζ' k ^ EF x y = ζ k ^ EF x y tot := fun j p => ?_ cotot := fun j p' => ?_ mul := ?_ eqv := ?_ inj := ?_ incl := ?_ wp := ?_ c₀ := c₀ c₀_ne := hc tx := ?_ }, fun j p p' => ⟨fun ⟨_, x, a, b, _⟩ => ⟨x …` and prove the remaining obligations. Take `⟨x, hx⟩` from `H.2.2.1 _ (hpos j) p`. Conclude with `⟨_, hpos j, x, hx, (E' _).refl _, fun y => by rw [hζn]⟩`. Take `⟨x, hx⟩` from `H'.2.2.1 _ (hpos j) p'`. Conclude with `⟨_, hpos j, x, (E _).refl _, hx, fun y => by rw [hζn]⟩`.

Introduce and unpack `k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', c'⟩`. Use `⟨hk, x + y, (E _).trans ((E _).symm (H.1 k hk x y)) (qEq_mul a a'), (E' _).trans ((E' _).symm (H'.1 k hk x y)) (qEq_mul b b'), fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, LinearMap.add_apply, zpow_add, zpow_add, c, c']`. Introduce and unpack `k p q p' q' ⟨hk, x, a, b, c⟩ h`. Use `⟨?_, fun h' => ⟨hk, x, (E _).trans a h, (E' _).trans b h', c⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨-, y, a', b', -⟩`. Conclude with `(E' _).trans ((E' _).symm b) ((E' _).trans ((tr k hk x y).1 ((E _).trans a ((E _).trans h ((E _).symm a')))) b')`. Introduce and unpack `k p q p' ⟨hk, x, a, b, -⟩ ⟨-, y, a', b', -⟩`. Conclude with `(E _).trans ((E _).symm a) ((E _).trans ((tr k hk x y).2 ((E' _).trans b ((E' _).symm b'))) a')`. Introduce `k k' p p' q q' hk' a b c d`.

Establish `hk0 : 0 < k'` using `Nat.pos_of_ne_zero hk'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hk, x, h1, h2, h3⟩`. Use `⟨Nat.mul_pos hk hk0, k' • x, (lab_incl H hk hk' x p q a b).1 h1, (lab_incl H' hk hk' x p' q' c d).1 h2, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0), h3]`.

Introduce and unpack `⟨hkk, y, h1, h2, h3⟩`. Establish `hk : 0 < k` using `Nat.pos_of_mul_pos_right hkk`. Take `⟨x, hx⟩` from `H.2.2.1 k hk p`. Establish `h4 : N.QEq (lab _ y) (lab (k * k') (k' • x))` using `(E _).trans h1 ((E _).symm ((lab_incl H hk hk' x p q a b).1 hx))`. Use `⟨hk, x, hx, (lab_incl H' hk hk' x p' q' c d).2 ((E' _).trans ((E' _).symm ((tr _ hkk _ _).1 h4)) h2), fun w => ?_⟩` and prove the remaining obligations.

Take `⟨e, rfl⟩` from `(H.2.1 _ hkk _ _).1 h4`. Use `h3 w` as an intermediate fact. Rewrite `this` using `[zeta_shift H hkk, zeta_shift H' hkk, zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0)]`. Then use the resulting hypothesis. Introduce and unpack `k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', -⟩`. Rewrite using `[← wp_congr a a', ← wp_congr b b', H.2.2.2.2 k hk, H'.2.2.2.2 k hk, c]`.

Introduce and unpack `j p p' ⟨-, x, a, b, -⟩`. Rewrite using `[tx_congr hn.pow a, tx_congr hn.pow b, htx]`.
-/
theorem exists_match : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), n.Prime → Odd n → (∀ (k : ℕ) (x : La), 0 < k → k • x = 0 → x = 0) → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) → (∀ k m, 0 < k → 0 < m → ζ' (k * m) ^ m = ζ' k) → (∀ j, ζ' (n ^ j) = ζ (n ^ j)) → ∀ c₀ : C, c₀ ≠ 0 → (∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x)) → ∃ mt : GlobalTheory.Ex.Match N N' n, ∀ j p p', mt.r (n ^ j) p p' ↔ ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p' := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n _ hn _ H H' hζ hζ' hζn c₀ hc htx
  have E := N.qEq_equivalence
  have E' := N'.qEq_equivalence
  have hpos : ∀ j, 0 < n ^ j := fun j => pow_pos hn.pos j
  have tr : ∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ N'.QEq (lab' k a) (lab' k b) := fun k hk a b =>
    (H.2.1 k hk a b).trans (H'.2.1 k hk a b).symm
  refine ⟨{
    r := fun k p p' => 0 < k ∧ ∃ x, N.QEq (lab k x) p ∧ N'.QEq (lab' k x) p' ∧ ∀ y, ζ' k ^ EF x y = ζ k ^ EF x y
    tot := fun j p => ?_
    cotot := fun j p' => ?_
    mul := ?_
    eqv := ?_
    inj := ?_
    incl := ?_
    wp := ?_
    c₀ := c₀
    c₀_ne := hc
    tx := ?_ }, fun j p p' => ⟨fun ⟨_, x, a, b, _⟩ => ⟨x, a, b⟩,
      fun ⟨x, a, b⟩ => ⟨hpos j, x, a, b, fun y => by rw [hζn]⟩⟩⟩
  · obtain ⟨x, hx⟩ := H.2.2.1 _ (hpos j) p
    exact ⟨_, hpos j, x, hx, (E' _).refl _, fun y => by rw [hζn]⟩
  · obtain ⟨x, hx⟩ := H'.2.2.1 _ (hpos j) p'
    exact ⟨_, hpos j, x, (E _).refl _, hx, fun y => by rw [hζn]⟩
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', c'⟩
    refine ⟨hk, x + y, (E _).trans ((E _).symm (H.1 k hk x y)) (qEq_mul a a'),
      (E' _).trans ((E' _).symm (H'.1 k hk x y)) (qEq_mul b b'), fun w => ?_⟩
    rw [map_add, LinearMap.add_apply, zpow_add, zpow_add, c, c']
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ h
    refine ⟨?_, fun h' => ⟨hk, x, (E _).trans a h, (E' _).trans b h', c⟩⟩
    rintro ⟨-, y, a', b', -⟩
    exact (E' _).trans ((E' _).symm b) ((E' _).trans
      ((tr k hk x y).1 ((E _).trans a ((E _).trans h ((E _).symm a')))) b')
  · rintro k p q p' ⟨hk, x, a, b, -⟩ ⟨-, y, a', b', -⟩
    exact (E _).trans ((E _).symm a) ((E _).trans ((tr k hk x y).2 ((E' _).trans b ((E' _).symm b'))) a')
  · intro k k' p p' q q' hk' a b c d
    have hk0 : 0 < k' := Nat.pos_of_ne_zero hk'
    constructor
    · rintro ⟨hk, x, h1, h2, h3⟩
      refine ⟨Nat.mul_pos hk hk0, k' • x, (lab_incl H hk hk' x p q a b).1 h1,
        (lab_incl H' hk hk' x p' q' c d).1 h2, fun y => ?_⟩
      rw [zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0), h3]
    · rintro ⟨hkk, y, h1, h2, h3⟩
      have hk : 0 < k := Nat.pos_of_mul_pos_right hkk
      obtain ⟨x, hx⟩ := H.2.2.1 k hk p
      have h4 : N.QEq (lab _ y) (lab (k * k') (k' • x)) :=
        (E _).trans h1 ((E _).symm ((lab_incl H hk hk' x p q a b).1 hx))
      refine ⟨hk, x, hx, (lab_incl H' hk hk' x p' q' c d).2
        ((E' _).trans ((E' _).symm ((tr _ hkk _ _).1 h4)) h2), fun w => ?_⟩
      obtain ⟨e, rfl⟩ := (H.2.1 _ hkk _ _).1 h4
      have := h3 w
      rwa [zeta_shift H hkk, zeta_shift H' hkk, zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0)] at this
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', -⟩
    rw [← wp_congr a a', ← wp_congr b b', H.2.2.2.2 k hk, H'.2.2.2.2 k hk, c]
  · rintro j p p' ⟨-, x, a, b, -⟩
    rw [tx_congr hn.pow a, tx_congr hn.pow b, htx]

end GlobalTheory.ModelData.LabelMatch
