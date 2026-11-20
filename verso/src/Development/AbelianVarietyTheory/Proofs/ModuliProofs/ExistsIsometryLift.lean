import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LevelActionTransitions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IsoLift

open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

/- English proof (translation)
Take `⟨x, y, hxy⟩` from `hnr`. Take `⟨hc, hB⟩` from `hf`. Use `⟨(y * r) • f + (x * n) • LinearMap.id, ⟨isCoprime_one_left, fun a b => ?_⟩, fun a => ⟨x • (a - f a), ?_⟩⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `hB a b`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_zsmul, smul_eq_mul]`.

Use `⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b + D.EF a b) * hxy`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Establish `h : y * (r : ℤ) = 1 - n * x` using `by linear_combination hxy`.

Rewrite using `[h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem step_coprime_one {n r : ℕ} (hnr : IsCoprime (n : ℤ) (r : ℤ)) {f : D.La →ₗ[𝓞 E] D.La}
    (hf : IsSimMod D n f 1) :
    ∃ f', IsSimMod D (n * r) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
  obtain ⟨x, y, hxy⟩ := hnr
  obtain ⟨hc, hB⟩ := hf
  refine ⟨(y * r) • f + (x * n) • LinearMap.id, ⟨isCoprime_one_left, fun a b => ?_⟩,
    fun a => ⟨x • (a - f a), ?_⟩⟩
  · obtain ⟨B, hB⟩ := hB a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_zsmul,
      smul_eq_mul]
    refine ⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩
    push_cast
    linear_combination (y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b + D.EF a b) * hxy
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h : y * (r : ℤ) = 1 - n * x := by linear_combination hxy
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]; abel

/- English proof (translation)
Proceed by induction on `m using induction_on_primes with`. Consider the case `zero => intro h`. Conclude with `absurd h (lt_irrefl 0)`. Consider the case `one`. Introduce `_ n _ f hf`.

Conclude with `⟨f, by simpa using hf, fun a => ⟨0, by simp⟩⟩`. Consider the case `prime_mul p a hp ih`. Introduce `hpa n hn f hf`. Establish `ha : 0 < a` using `Nat.pos_of_mul_pos_left hpa`. Establish `h1 : ∃ f', IsSimMod D (n * p) f' 1 ∧ (∀ a, D.ModN n (f' a - f a))`.

Distinguish the cases in `hpn : p ∣ n`. Take `⟨f', h1, h2⟩` from `step_sq D hn hf`. Conclude with `⟨f', h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2⟩`. Conclude with `step_coprime_one D (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf`. Take `⟨f₁, h1, h2⟩` from `h1`.

Take `⟨f₂, h4, h5⟩` from `ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ h1`. Conclude with `⟨f₂, by rwa [← Nat.mul_assoc], fun x => modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x)⟩`.
-/
theorem step_one (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La), IsSimMod D n f 1 →
    ∃ f', IsSimMod D (n * m) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f hf
    exact ⟨f, by simpa using hf, fun a => ⟨0, by simp⟩⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f', IsSimMod D (n * p) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2⟩
      · exact step_coprime_one D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, h1, h2⟩ := h1
    obtain ⟨f₂, h4, h5⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ h1
    exact ⟨f₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x)⟩

/- English proof (translation)
Set `T : ℕ → Type` to `fun k => {x : (D.La →ₗ[𝓞 E] D.La) // IsSimMod D (N * k.factorial) x 1}`. Establish `hstep : ∀ k (x : T k), ∃ y : T (k + 1), (∀ a, D.ModN (N * k.factorial) (y.1 a - x.1 a))`. Introduce `k x`. Take `⟨f', h1, h2⟩` from `step_one D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ x.2`. Use `⟨⟨f', ?_⟩, h2⟩` and prove the remaining obligations.

Rewrite using `[Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]` and apply the resulting hypothesis. Use `choose nx hnx using hstep`. Set `s : ∀ k, T k` to `fun k => Nat.rec (⟨f, by`. Rewrite using `[Nat.factorial_zero, Nat.mul_one]`. Conclude with `hf⟩ : T 0) nx k`.

Use `⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k j hkj => ?_⟩` and prove the remaining obligations. Proceed by induction on `j, hkj using Nat.le_induction with`. Consider the case `base => exact fun a => ⟨0, by simp⟩`. Consider the case `succ j hkj ih`. Establish `hd : N * k.factorial ∣ N * j.factorial` using `Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)`.

Conclude with `fun a => modN_trans D (modN_of_dvd_modulus D hd (hnx j (s j) a)) (ih a)`.
-/
theorem exists_tower {N : ℕ} (hN : 0 < N) {f : D.La →ₗ[𝓞 E] D.La} (hf : IsSimMod D N f 1) :
    ∃ s : ℕ → (D.La →ₗ[𝓞 E] D.La), s 0 = f ∧ (∀ k, IsSimMod D (N * k.factorial) (s k) 1) ∧
      ∀ k j, k ≤ j → ∀ a, D.ModN (N * k.factorial) (s j a - s k a) := by
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) // IsSimMod D (N * k.factorial) x 1}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1 a - x.1 a)) := by
    intro k x
    obtain ⟨f', h1, h2⟩ := step_one D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ x.2
    refine ⟨⟨f', ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨f, by
    rw [Nat.factorial_zero, Nat.mul_one]; exact hf⟩ : T 0) nx k
  refine ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k j hkj => ?_⟩
  induction j, hkj using Nat.le_induction with
  | base => exact fun a => ⟨0, by simp⟩
  | succ j hkj ih =>
    have hd : N * k.factorial ∣ N * j.factorial :=
      Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
    exact fun a => modN_trans D (modN_of_dvd_modulus D hd (hnx j (s j) a)) (ih a)

/- English proof (translation)
Rewrite using `[Submodule.Quotient.eq, mem_nLa]`. Both sides reduce to the same expression.
-/
theorem cls_eq_iff_modN {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ D.ModN n (a - b) := by
  rw [Submodule.Quotient.eq, mem_nLa]
  rfl

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_inv D n.pos hf`. Establish `hle : ∀ u : D.La →ₗ[𝓞 E] D.La, nLa D n ≤ (nLa D n).comap u`. Introduce `u x hx`. Take `⟨y, rfl⟩` from `(mem_nLa D).mp hx`. Conclude with `(mem_nLa D).mpr ⟨u y, map_nsmul u _ y⟩`.

Use `⟨LinearEquiv.ofLinear ((nLa D n).mapQ _ f (hle f)) ((nLa D n).mapQ _ g (hle g)) ?_ ?_, fun a => rfl⟩` and prove the remaining obligations. Use `LinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Conclude with `(cls_eq_iff_modN D).mpr (hg a).2`. Use `LinearMap.ext fun q => ?_` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Conclude with `(cls_eq_iff_modN D).mpr (hg a).1`.
-/
theorem exists_equiv (n : ℕ+) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ e : LaMod D n ≃ₗ[𝓞 E] LaMod D n, ∀ a, e (cls D n a) = cls D n (f a) := by
  obtain ⟨g, hg⟩ := exists_inv D n.pos hf
  have hle : ∀ u : D.La →ₗ[𝓞 E] D.La, nLa D n ≤ (nLa D n).comap u := by
    intro u x hx
    obtain ⟨y, rfl⟩ := (mem_nLa D).mp hx
    exact (mem_nLa D).mpr ⟨u y, map_nsmul u _ y⟩
  refine ⟨LinearEquiv.ofLinear ((nLa D n).mapQ _ f (hle f)) ((nLa D n).mapQ _ g (hle g)) ?_ ?_,
    fun a => rfl⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (cls_eq_iff_modN D).mpr (hg a).2
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (cls_eq_iff_modN D).mpr (hg a).1

end GlobalTheory.IsoLift

namespace GlobalTheory

open SimLift IsoLift IndefiniteRowSideFullHecke.LevelActionTransitions

end GlobalTheory
