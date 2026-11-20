import Mathlib
open NumberField

namespace GlobalTheory

open Submodule

/- English proof (translation)
Establish `hlt : w0 ^ 2 < w0` using `by simpa using Ideal.pow_succ_lt_pow hne 1`. Take `⟨c0, hc0, hc02⟩` from `SetLike.exists_of_lt hlt`. Establish `hdvd : w0 ∣ Ideal.span {c0}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)`. Take `⟨b, hb⟩` from `hdvd`. Establish `hbw : ¬ b ≤ w0`.

Introduce `hle`. Apply `hc02` to reduce the goal to its premises. Establish `: Ideal.span {c0} ≤ w0 ^ 2` using `by rw [hb, pow_two]; exact Ideal.mul_mono_right hle`. Conclude with `this (Ideal.subset_span rfl)`. Establish `hbtop : b ⊔ w0 = ⊤`.

Assume the negation of the conclusion as `h`. Conclude with `hbw (le_sup_left.trans (hmax.eq_of_le h le_sup_right).symm.le)`. Establish `hcop : ∀ n : ℕ, b ⊔ w0 ^ n = ⊤`. Introduce `n`. Rewrite using `[← Ideal.isCoprime_iff_sup_eq]`.

Conclude with `(Ideal.isCoprime_iff_sup_eq.mpr hbtop).pow_right`. Establish `hc0ne : c0 ≠ 0` using `by rintro rfl; exact hc02 (zero_mem _)`. Set `Tj` to `torsionBySet R M ((w0 ^ j : Ideal R) : Set R)`. Set `Tj1` to `torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)`. Set `T1` to `torsionBySet R M ((w0 : Ideal R) : Set R)`.

Establish `hmapsto : ∀ x ∈ Tj1, c0 • x ∈ Tj`. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_torsionBySet_iff]`. Introduce and unpack `⟨a, ha⟩`. Establish `: a * c0 ∈ w0 ^ (j + 1)` using `by rw [pow_succ]; exact Ideal.mul_mem_mul ha hc0`.

Simplify `hx ⟨_, this⟩` using `[smul_smul]`. Set `φ : Tj1 →ₗ[R] Tj` to `{ toFun := fun x => ⟨c0 • (x : M), hmapsto x x.2⟩ map_add' := fun x y => by ext; simp map_smul' := fun r x => by ext; simp [smul_comm c0 r] }`. Establish `hsurj : Function.Surjective φ`. Introduce and unpack `⟨g, hg⟩`. Take `⟨g', hg'⟩` from `hdiv c0 hc0ne g`.

Simplify using `only at hg'`. Establish `h1 : (1 : R) ∈ b ⊔ w0 ^ (j + 1)` using `by rw [hcop]; trivial`. Take `⟨v, hv, u, hu, huv⟩` from `Submodule.mem_sup.mp h1`. Establish `hmem : v • g' ∈ Tj1`. Rewrite using `[mem_torsionBySet_iff]`.

Introduce and unpack `⟨a, ha⟩`. Establish `hav : a * v ∈ w0 ^ j * Ideal.span {c0}`. Rewrite using `[hb, ← mul_assoc, ← pow_succ]`. Conclude with `Ideal.mul_mem_mul ha hv`. Take `⟨z, hz, hzc⟩` from `(Submodule.mem_mul_span_singleton).mp hav`.

Simplify using `only`. Rewrite using `[smul_smul, ← hzc, ← smul_smul, hg']`. Conclude with `(mem_torsionBySet_iff _ _).mp hg ⟨z, hz⟩`. Use `⟨⟨v • g', hmem⟩, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `only [φ, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[smul_comm, hg']`. Establish `hug : u • g = 0`. Establish `: u ∈ w0 ^ j` using `Ideal.pow_le_pow_right (Nat.le_succ j) hu`. Conclude with `(mem_torsionBySet_iff _ _).mp hg ⟨u, this⟩`.

Establish `: v = 1 - u` using `by rw [← huv]; ring`. Rewrite using `[this, sub_smul, one_smul, hug, sub_zero]`. Establish `hsub : T1 ≤ Tj1` using `torsionBySet_le_torsionBySet_of_subset (by`. Introduce `a ha`. Conclude with `Ideal.pow_le_self (Nat.succ_ne_zero j) ha)`.

Establish `hker : ∀ x : Tj1, x ∈ LinearMap.ker φ ↔ (x : M) ∈ T1`. Introduce `x`. Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hx' : c0 • (x : M) = 0`. Use `congrArg Subtype.val hx` as an intermediate fact. Simplify `this` using `[φ]`. Rewrite using `[mem_torsionBySet_iff]`. Introduce and unpack `⟨a, ha⟩`.

Establish `hw : w0 ≤ Ideal.span {c0} ⊔ w0 ^ (j + 1)`. Establish `e : w0 * (b ⊔ w0 ^ j) = Ideal.span {c0} ⊔ w0 ^ (j + 1)`. Rewrite using `[Ideal.mul_sup, ← hb, ← pow_succ']`. Rewrite `e` using `[hcop, Ideal.mul_top]`. Conclude with `e.le`.

Take `⟨s, hs, t, ht, hst⟩` from `Submodule.mem_sup.mp (hw ha)`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hs`. Establish `key : (r * c0 + t) • (x : M) = 0`. Rewrite using `[add_smul, mul_smul, hx', smul_zero, zero_add]`. Conclude with `(mem_torsionBySet_iff _ _).mp x.2 ⟨t, ht⟩`.

Rewrite `key` using `[hst]`. Then use the resulting hypothesis. Introduce `hx`. Use `ext`. Simplify using `only [φ, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero]`. Conclude with `(mem_torsionBySet_iff _ _).mp hx ⟨c0, hc0⟩`.

Establish `e1 : Nat.card (Tj1 ⧸ LinearMap.ker φ) = Nat.card Tj` using `Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv`. Establish `e2 : Nat.card (LinearMap.ker φ) = Nat.card T1` using `Nat.card_congr { toFun := fun x => ⟨(x.1 : M), (hker x.1).mp x.2⟩ invFun := fun y => ⟨⟨y.1, hsub y.2⟩, (hker _).mpr y.2⟩ left_inv := fun x => rfl right_inv := fun y => rfl }`. Rewrite using `[Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ), e1, e2, mul_comm]`.
-/
theorem torsion_pow_card_succ {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] (w0 : Ideal R) (hmax : w0.IsMaximal) (hne : w0 ≠ ⊥)
    (hdiv : ∀ c : R, c ≠ 0 → Function.Surjective (fun g : M => c • g)) (j : ℕ) :
    Nat.card (torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)) =
      Nat.card (torsionBySet R M ((w0 ^ j : Ideal R) : Set R)) *
        Nat.card (torsionBySet R M ((w0 : Ideal R) : Set R)) := by
  have hlt : w0 ^ 2 < w0 := by simpa using Ideal.pow_succ_lt_pow hne 1
  obtain ⟨c0, hc0, hc02⟩ := SetLike.exists_of_lt hlt
  have hdvd : w0 ∣ Ideal.span {c0} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨b, hb⟩ := hdvd
  have hbw : ¬ b ≤ w0 := by
    intro hle
    apply hc02
    have : Ideal.span {c0} ≤ w0 ^ 2 := by rw [hb, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.subset_span rfl)
  have hbtop : b ⊔ w0 = ⊤ := by
    by_contra h
    exact hbw (le_sup_left.trans (hmax.eq_of_le h le_sup_right).symm.le)
  have hcop : ∀ n : ℕ, b ⊔ w0 ^ n = ⊤ := by
    intro n
    rw [← Ideal.isCoprime_iff_sup_eq]
    exact (Ideal.isCoprime_iff_sup_eq.mpr hbtop).pow_right
  have hc0ne : c0 ≠ 0 := by rintro rfl; exact hc02 (zero_mem _)

  let Tj := torsionBySet R M ((w0 ^ j : Ideal R) : Set R)
  let Tj1 := torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)
  let T1 := torsionBySet R M ((w0 : Ideal R) : Set R)
  have hmapsto : ∀ x ∈ Tj1, c0 • x ∈ Tj := by
    intro x hx
    rw [mem_torsionBySet_iff] at hx ⊢
    rintro ⟨a, ha⟩
    have : a * c0 ∈ w0 ^ (j + 1) := by rw [pow_succ]; exact Ideal.mul_mem_mul ha hc0
    simpa [smul_smul] using hx ⟨_, this⟩
  let φ : Tj1 →ₗ[R] Tj :=
    { toFun := fun x => ⟨c0 • (x : M), hmapsto x x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp [smul_comm c0 r] }
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨g', hg'⟩ := hdiv c0 hc0ne g
    simp only at hg'
    have h1 : (1 : R) ∈ b ⊔ w0 ^ (j + 1) := by rw [hcop]; trivial
    obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.mp h1
    have hmem : v • g' ∈ Tj1 := by
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hav : a * v ∈ w0 ^ j * Ideal.span {c0} := by
        rw [hb, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha hv
      obtain ⟨z, hz, hzc⟩ := (Submodule.mem_mul_span_singleton).mp hav
      simp only
      rw [smul_smul, ← hzc, ← smul_smul, hg']
      exact (mem_torsionBySet_iff _ _).mp hg ⟨z, hz⟩
    refine ⟨⟨v • g', hmem⟩, ?_⟩
    ext
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_comm, hg']
    have hug : u • g = 0 := by
      have : u ∈ w0 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j) hu
      exact (mem_torsionBySet_iff _ _).mp hg ⟨u, this⟩
    have : v = 1 - u := by rw [← huv]; ring
    rw [this, sub_smul, one_smul, hug, sub_zero]
  have hsub : T1 ≤ Tj1 := torsionBySet_le_torsionBySet_of_subset (by
    intro a ha
    exact Ideal.pow_le_self (Nat.succ_ne_zero j) ha)
  have hker : ∀ x : Tj1, x ∈ LinearMap.ker φ ↔ (x : M) ∈ T1 := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      have hx' : c0 • (x : M) = 0 := by
        have := congrArg Subtype.val hx
        simpa [φ] using this
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hw : w0 ≤ Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
        have e : w0 * (b ⊔ w0 ^ j) = Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
          rw [Ideal.mul_sup, ← hb, ← pow_succ']
        rw [hcop, Ideal.mul_top] at e
        exact e.le
      obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hw ha)
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      have key : (r * c0 + t) • (x : M) = 0 := by
        rw [add_smul, mul_smul, hx', smul_zero, zero_add]
        exact (mem_torsionBySet_iff _ _).mp x.2 ⟨t, ht⟩
      rwa [hst] at key
    · intro hx
      ext
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero]
      exact (mem_torsionBySet_iff _ _).mp hx ⟨c0, hc0⟩
  have e1 : Nat.card (Tj1 ⧸ LinearMap.ker φ) = Nat.card Tj :=
    Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv
  have e2 : Nat.card (LinearMap.ker φ) = Nat.card T1 :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), (hker x.1).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, hsub y.2⟩, (hker _).mpr y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ), e1, e2, mul_comm]

/- English proof (translation)
Introduce `hmax hne hdiv h1 j`. Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [pow_zero, zero_mul]`. Establish `: torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[mem_torsionBySet_iff]`. Simplify using `using hx ⟨1, trivial⟩`. Rewrite using `[Ideal.one_eq_top, this]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[torsion_pow_card_succ M w0 hmax hne hdiv n, ih, h1, ← pow_add]`. Put the polynomial expressions in normal form.
-/
theorem torsion_pow_card (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ) :
    w0.IsMaximal → w0 ≠ ⊥ → (∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g)) →
    Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h →
    ∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w0) ^ (j * h) := by
  intro hmax hne hdiv h1 j
  induction j with
  | zero =>
    simp only [pow_zero, zero_mul]
    have : torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_torsionBySet_iff] at hx
      simpa using hx ⟨1, trivial⟩
    rw [Ideal.one_eq_top, this]
    simp
  | succ n ih =>
    rw [torsion_pow_card_succ M w0 hmax hne hdiv n, ih, h1, ← pow_add]
    ring_nf

end GlobalTheory
