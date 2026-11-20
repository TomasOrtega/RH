import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

def Crit (N c : ℕ) (n : ℕ → ℤ) (z : Sp E N) (v : Sp E (N + c)) : Prop :=
  (∀ l : Fin N, IntAt P (v (Fin.castAdd _ l) - Loc.atN v N * z l)) ∧
    ∀ i : Fin c, IntAt P ((((Ideal.absNorm P.asIdeal : ℕ) : E) ^ n i.1)⁻¹ * v (Fin.natAdd _ i))

/- English proof (translation)
Distinguish the cases in `h : l.1 < N`. Conclude with `Or.inl ⟨⟨l.1, h⟩, Fin.ext rfl⟩`. Conclude with `Or.inr ⟨⟨l.1 - N, by omega⟩, Fin.ext (by simp; omega)⟩`.
-/
theorem fin_split {N c : ℕ} (l : Fin (N + c)) :
    (∃ l' : Fin N, l = Fin.castAdd c l') ∨ ∃ i : Fin c, l = Fin.natAdd N i := by
  by_cases h : l.1 < N
  · exact Or.inl ⟨⟨l.1, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨l.1 - N, by omega⟩, Fin.ext (by simp; omega)⟩

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hm`. Rewrite using `[zpow_natCast]`. Conclude with `intAt_pow P (intAt_natCast P _) _`.
-/
theorem intAt_zpow (m : ℤ) (hm : 0 ≤ m) : IntAt P (qE P ^ m) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]; exact intAt_pow P (intAt_natCast P _) _

/- English proof (translation)
Establish `hq0` using `qE_ne_zero P hp`. Establish `h1 : qE P ^ m ≠ 0` using `zpow_ne_zero m hq0`. Establish `: qE P ^ j * a = qE P ^ ((j : ℤ) + m) * ((qE P ^ m)⁻¹ * a)`. Rewrite using `[zpow_add₀ hq0, zpow_natCast, mul_assoc (qE P ^ j), ← mul_assoc (qE P ^ m), mul_inv_cancel₀ h1, one_mul]`. Rewrite using `[this]; exact intAt_mul P (intAt_zpow P _ (by omega)) ha`.
-/
theorem intAt_scale (hp : (Ideal.absNorm P.asIdeal).Prime) {j : ℕ} {m : ℤ} (hm : -(j : ℤ) ≤ m) {a : E}
    (ha : IntAt P ((qE P ^ m)⁻¹ * a)) : IntAt P (qE P ^ j * a) := by
  have hq0 := qE_ne_zero P hp
  have h1 : qE P ^ m ≠ 0 := zpow_ne_zero m hq0
  have : qE P ^ j * a = qE P ^ ((j : ℤ) + m) * ((qE P ^ m)⁻¹ * a) := by
    rw [zpow_add₀ hq0, zpow_natCast, mul_assoc (qE P ^ j), ← mul_assoc (qE P ^ m), mul_inv_cancel₀ h1, one_mul]
  rw [this]; exact intAt_mul P (intAt_zpow P _ (by omega)) ha

/- English proof (translation)
Rewrite `hz` using `[mem_stdAt]`. Introduce `x hx`. Rewrite `hx` using `[mem_lam]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hc]`.

Use `⟨fun l => intAt_sub P (hx _) (intAt_mul P ?_ (hz l)), fun i => intAt_mul P ?_ (hx _)⟩` and prove the remaining obligations. Unfold `Loc.atN`. Use `split_ifs`. Conclude with `hx _`. Conclude with `intAt_zero P`.

Rewrite using `[← zpow_neg]; exact intAt_zpow P _ (by have := (hn i.1).2; omega)`. Establish `hv : Crit P N c n z (h x)`. Rewrite using `[← hc]`. Rewrite using `[LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, mem_lam]`. Conclude with `hx`.

Establish `hN : IntAt P (qE P ^ j * Loc.atN (h x) N)`. Unfold `Loc.atN`. Use `split_ifs with hN`. Use `hv.2 ⟨0, by omega⟩` as an intermediate fact. Conclude with `intAt_scale P hp (hn 0).1 this`.

Simplify using `using intAt_zero P`. Rewrite using `[mem_lam]`. Introduce `l`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Break down `fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩` into its components or cases.

Establish `e : qE P ^ j * h x (Fin.castAdd c l') = qE P ^ j * (h x (Fin.castAdd c l') - Loc.atN (h x) N * z l') + qE P ^ j * Loc.atN (h x) N * z l'` using `by ring`. Rewrite using `[e]`. Conclude with `intAt_add P (intAt_mul P (intAt_pow P (intAt_natCast P _) _) (hv.1 l')) (intAt_mul P hN (hz l'))`. Conclude with `intAt_scale P hp (hn i.1).1 (hv.2 i)`.
-/
theorem bdd_of_nf (hp : (Ideal.absNorm P.asIdeal).Prime) {N c j : ℕ} (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))
    (n : ℕ → ℤ) (z : Sp E N) (hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) (hz : z ∈ stdAt E N P)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) : Bdd P N c j h := by
  rw [mem_stdAt] at hz
  intro x hx
  rw [mem_lam] at hx
  constructor
  · rw [hc]
    refine ⟨fun l => intAt_sub P (hx _) (intAt_mul P ?_ (hz l)), fun i => intAt_mul P ?_ (hx _)⟩
    · unfold Loc.atN; split_ifs
      · exact hx _
      · exact intAt_zero P
    · rw [← zpow_neg]; exact intAt_zpow P _ (by have := (hn i.1).2; omega)
  · have hv : Crit P N c n z (h x) := by
      rw [← hc]; rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, mem_lam]; exact hx
    have hN : IntAt P (qE P ^ j * Loc.atN (h x) N) := by
      unfold Loc.atN; split_ifs with hN
      · have := hv.2 ⟨0, by omega⟩
        exact intAt_scale P hp (hn 0).1 this
      · simpa using intAt_zero P
    rw [mem_lam]
    intro l
    rw [Pi.smul_apply, smul_eq_mul]
    rcases fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩
    · have e : qE P ^ j * h x (Fin.castAdd c l') = qE P ^ j * (h x (Fin.castAdd c l') - Loc.atN (h x) N * z l') +
          qE P ^ j * Loc.atN (h x) N * z l' := by ring
      rw [e]
      exact intAt_add P (intAt_mul P (intAt_pow P (intAt_natCast P _) _) (hv.1 l')) (intAt_mul P hN (hz l'))
    · exact intAt_scale P hp (hn i.1).1 (hv.2 i)

/- English proof (translation)
Introduce and unpack `g ⟨r, hr, hg⟩`. Establish `hJ` using `(Subgroup.mem_comap.1 hr.2).1`. Establish `lamEq : ∀ w, w ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ w ∈ stdAt E (N + c) P`. Introduce `w`. Rewrite using `[mem_lam, mem_stdAt]`.

Establish `hstab : ∀ v, h⁻¹ (r v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0`. Introduce `v`. Use `hJ (h⁻¹ v)` as an intermediate fact. Rewrite using `[lamEq, lamEq, ← this]`. Simplify using `[MulAut.conj_apply, LinearEquiv.mul_apply]`.

Establish `hX : ∀ x : Sp E N, h⁻¹ (Loc.inX E N c x) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ x ∈ stdAt E N P`. Introduce `x`. Rewrite using `[hc, mem_stdAt]`. Establish `h1 : ∀ l : Fin N, Loc.inX E N c x (Fin.castAdd c l) = x l` using `fun l => by simp [Loc.inX]`. Establish `h2 : ∀ i : Fin c, Loc.inX E N c x (Fin.natAdd N i) = 0` using `fun i => by simp [Loc.inX]`.

Establish `h3 : Loc.atN (Loc.inX E N c x) N = 0` using `by simp [Loc.atN, Loc.inX]`. Simplify using `only [Crit, h1, h2, h3, zero_mul, sub_zero, mul_zero]`. Conclude with `⟨fun H => H.1, fun H => ⟨H, fun _ => intAt_zero P⟩⟩`. Use `show ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P`. Introduce `x`.

Rewrite using `[← hX, ← hX, ← hg x, hstab]`.
-/
theorem prX_le_of_nf {N c : ℕ} (kj : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) (n : ℕ → ℤ) (z : Sp E N)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) :
    Loc.prX (Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h) ≤ GLint E N P := by
  rintro g ⟨r, hr, hg⟩
  have hJ := (Subgroup.mem_comap.1 hr.2).1
  have lamEq : ∀ w, w ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ w ∈ stdAt E (N + c) P := by
    intro w; rw [mem_lam, mem_stdAt]
  have hstab : ∀ v, h⁻¹ (r v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := by
    intro v
    have := hJ (h⁻¹ v)
    rw [lamEq, lamEq, ← this]
    simp [MulAut.conj_apply, LinearEquiv.mul_apply]
  have hX : ∀ x : Sp E N, h⁻¹ (Loc.inX E N c x) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ x ∈ stdAt E N P := by
    intro x
    rw [hc, mem_stdAt]
    have h1 : ∀ l : Fin N, Loc.inX E N c x (Fin.castAdd c l) = x l := fun l => by simp [Loc.inX]
    have h2 : ∀ i : Fin c, Loc.inX E N c x (Fin.natAdd N i) = 0 := fun i => by simp [Loc.inX]
    have h3 : Loc.atN (Loc.inX E N c x) N = 0 := by simp [Loc.atN, Loc.inX]
    simp only [Crit, h1, h2, h3, zero_mul, sub_zero, mul_zero]
    exact ⟨fun H => H.1, fun H => ⟨H, fun _ => intAt_zero P⟩⟩
  show ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P
  intro x
  rw [← hX, ← hX, ← hg x, hstab]

end PI.TwNormLat.W
