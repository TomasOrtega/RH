import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.NormFormGauss

/- English proof (translation)
Set `T : k →+ k` to `s.toAddMonoidHom - AddMonoidHom.id k`. Establish `hT : ∀ x, T x = s x - x` using `fun x => rfl`. Establish `h1 : Nat.card k = Nat.card (k ⧸ T.ker) * Nat.card T.ker` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _`. Establish `h2 : Nat.card (k ⧸ T.ker) = Nat.card T.range` using `Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv`. Establish `h3 : Nat.card T.ker = (Finset.univ.filter (fun x : k => s x = x)).card`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[AddMonoidHom.mem_ker, hT, sub_eq_zero]`. Establish `hθ : s (s r - r) = -(s r - r)` using `by rw [map_sub, hs]; ring`.

Establish `h4 : Nat.card T.range = Nat.card T.ker`. Use `symm`. Use `Nat.card_congr (Equiv.ofBijective (fun u : T.ker => (⟨(s r - r) * u, ⟨r * u, ?_⟩⟩ : T.range)) ⟨?_, ?_⟩)` and prove the remaining obligations. Establish `hu : s u = u`. Use `u.2` as an intermediate fact.

Rewrite `this` using `[AddMonoidHom.mem_ker, hT, sub_eq_zero]`. Conclude with `this`. Rewrite using `[hT, map_mul, hu]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u v huv`.

Use `congrArg Subtype.val huv` as an intermediate fact. Conclude with `Subtype.ext (mul_left_cancel₀ hr this)`. Introduce and unpack `⟨_, t, rfl⟩`. Use `⟨⟨(s t - t) / (s r - r), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.mem_ker, hT, sub_eq_zero, map_div₀, hθ, map_sub, hs]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hT]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← Nat.card_eq_fintype_card, h1, h2, h4, h3, sq]`.
-/
theorem card_eq_sq {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    Fintype.card k = (Finset.univ.filter (fun x : k => s x = x)).card ^ 2 := by
  let T : k →+ k := s.toAddMonoidHom - AddMonoidHom.id k
  have hT : ∀ x, T x = s x - x := fun x => rfl
  have h1 : Nat.card k = Nat.card (k ⧸ T.ker) * Nat.card T.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (k ⧸ T.ker) = Nat.card T.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv
  have h3 : Nat.card T.ker = (Finset.univ.filter (fun x : k => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [AddMonoidHom.mem_ker, hT, sub_eq_zero]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have h4 : Nat.card T.range = Nat.card T.ker := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : T.ker => (⟨(s r - r) * u, ⟨r * u, ?_⟩⟩ : T.range)) ⟨?_, ?_⟩)
    · have hu : s u = u := by
        have := u.2
        rw [AddMonoidHom.mem_ker, hT, sub_eq_zero] at this
        exact this
      rw [hT, map_mul, hu]; ring
    · intro u v huv
      have := congrArg Subtype.val huv
      exact Subtype.ext (mul_left_cancel₀ hr this)
    · rintro ⟨_, t, rfl⟩
      refine ⟨⟨(s t - t) / (s r - r), ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, hT, sub_eq_zero, map_div₀, hθ, map_sub, hs]
        field_simp
        ring
      · apply Subtype.ext
        simp only [hT]
        field_simp
  rw [← Nat.card_eq_fintype_card, h1, h2, h4, h3, sq]

/- English proof (translation)
Set `S : kˣ →* kˣ` to `Units.map s.toMonoidHom`. Establish `hS : ∀ x : kˣ, ((S x : kˣ) : k) = s x` using `fun x => rfl`. Set `N : kˣ →* kˣ` to `MonoidHom.id _ * S`. Set `D : kˣ →* kˣ` to `MonoidHom.id _ / S`. Establish `hN : ∀ x : kˣ, ((N x : kˣ) : k) = x * s x` using `fun x => rfl`.

Establish `hD : ∀ x : kˣ, ((D x : kˣ) : k) = x / s x` using `fun x => by`. Simplify using `[D, hS]`. Establish `hθ : s (s r - r) = -(s r - r)` using `by rw [map_sub, hs]; ring`. Establish `hne : ∀ x : kˣ, s x ≠ 0` using `fun x => by simp`. Establish `hDk : ∀ x : kˣ, x ∈ D.ker ↔ s x = x` using `fun x => by`.

Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, hD, Units.val_one, div_eq_one_iff_eq (hne x), eq_comm]`. Establish `hker : N.ker = D.range`. Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Distinguish the cases in `h : (1 + x : k) = 0`. Use `⟨Units.mk0 _ hr, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hD, Units.val_mk0, hθ, div_neg, div_self hr]`. Take the linear combination `-h`.

Use `⟨Units.mk0 _ h, Units.ext ?_⟩` and prove the remaining obligations. Establish `h'` using `hne (Units.mk0 _ h)`. Rewrite using `[hD, div_eq_iff h', Units.val_mk0, map_add, map_one]`. Take the linear combination `-hx`. Introduce and unpack `⟨y, rfl⟩`.

Rewrite using `[hD, map_div₀, hs]`. Use `hne y` as an intermediate fact. Use `y.ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `c1 : Nat.card kˣ = Nat.card N.range * Nat.card N.ker`.

Rewrite using `[Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker, Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]`. Establish `c2 : Nat.card kˣ = Nat.card D.range * Nat.card D.ker`. Rewrite using `[Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker, Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv]`. Establish `c3 : Nat.card N.range = Nat.card D.ker`. Rewrite `c2` using `[← hker, c1, mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_left Nat.card_pos c2`. Establish `hle : N.range ≤ D.ker`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[hDk, hN, map_mul, hs, mul_comm]`. Establish `hr' : N.range = D.ker` using `Subgroup.eq_of_le_of_card_ge hle c3.ge`.

Establish `c4 : Nat.card D.ker = (Finset.univ.filter (fun x : kˣ => s x = x)).card`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, hDk]`.

Use `⟨Nat.card N.ker, ?_, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.card_eq_fintype_card, c1, c3, c4, mul_comm]`. Establish `himg : Finset.univ.image N = Finset.univ.filter (fun x : kˣ => s x = x)`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, ← hDk, ← hr', Finset.mem_image, Finset.mem_univ, true_and]`.

Both sides reduce to the same expression. Use `Finset.sum_comp (s := Finset.univ) (fun y : kˣ => f y) N` as an intermediate fact. Simplify using `only [hN] at this`. Rewrite using `[this, ← himg, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[nsmul_eq_mul]`. Use `congr 2`. Establish `hy' : y ∈ Set.range N` using `by simpa using hy`. Rewrite using `[MonoidHom.card_fiber_eq_of_mem_range N hy' (⟨1, map_one N⟩ : (1 : kˣ) ∈ Set.range N), Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `[MonoidHom.mem_ker]`.
-/
theorem sum_norm_units {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    ∃ m : ℕ, Fintype.card kˣ = m * (Finset.univ.filter (fun x : kˣ => s x = x)).card ∧
      ∀ f : k → ℂ, ∑ x : kˣ, f (x * s x) =
        m * ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y := by
  let S : kˣ →* kˣ := Units.map s.toMonoidHom
  have hS : ∀ x : kˣ, ((S x : kˣ) : k) = s x := fun x => rfl
  let N : kˣ →* kˣ := MonoidHom.id _ * S
  let D : kˣ →* kˣ := MonoidHom.id _ / S
  have hN : ∀ x : kˣ, ((N x : kˣ) : k) = x * s x := fun x => rfl
  have hD : ∀ x : kˣ, ((D x : kˣ) : k) = x / s x := fun x => by
    simp [D, hS]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have hne : ∀ x : kˣ, s x ≠ 0 := fun x => by simp
  have hDk : ∀ x : kˣ, x ∈ D.ker ↔ s x = x := fun x => by
    rw [MonoidHom.mem_ker, Units.ext_iff, hD, Units.val_one, div_eq_one_iff_eq (hne x), eq_comm]
  have hker : N.ker = D.range := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one]
    constructor
    · intro hx
      by_cases h : (1 + x : k) = 0
      · refine ⟨Units.mk0 _ hr, Units.ext ?_⟩
        rw [hD, Units.val_mk0, hθ, div_neg, div_self hr]
        linear_combination -h
      · refine ⟨Units.mk0 _ h, Units.ext ?_⟩
        have h' := hne (Units.mk0 _ h)
        rw [hD, div_eq_iff h', Units.val_mk0, map_add, map_one]
        linear_combination -hx
    · rintro ⟨y, rfl⟩
      rw [hD, map_div₀, hs]
      have := hne y
      have := y.ne_zero
      field_simp
  have c1 : Nat.card kˣ = Nat.card N.range * Nat.card N.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]
  have c2 : Nat.card kˣ = Nat.card D.range * Nat.card D.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv]
  have c3 : Nat.card N.range = Nat.card D.ker := by
    rw [← hker, c1, mul_comm] at c2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos c2
  have hle : N.range ≤ D.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hDk, hN, map_mul, hs, mul_comm]
  have hr' : N.range = D.ker := Subgroup.eq_of_le_of_card_ge hle c3.ge
  have c4 : Nat.card D.ker = (Finset.univ.filter (fun x : kˣ => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, hDk]
  refine ⟨Nat.card N.ker, ?_, fun f => ?_⟩
  · rw [← Nat.card_eq_fintype_card, c1, c3, c4, mul_comm]
  · have himg : Finset.univ.image N = Finset.univ.filter (fun x : kˣ => s x = x) := by
      ext x
      simp only [Finset.mem_filter, ← hDk, ← hr', Finset.mem_image, Finset.mem_univ, true_and]
      rfl
    have := Finset.sum_comp (s := Finset.univ) (fun y : kˣ => f y) N
    simp only [hN] at this
    rw [this, ← himg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [nsmul_eq_mul]
    congr 2
    have hy' : y ∈ Set.range N := by simpa using hy
    rw [MonoidHom.card_fiber_eq_of_mem_range N hy' (⟨1, map_one N⟩ : (1 : kˣ) ∈ Set.range N),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [MonoidHom.mem_ker]

/- English proof (translation)
Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]`. Use `congr 1`. Use `symm`. Use `Finset.sum_bij (fun x _ => (x : k)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`.

Simplify using the standard rewrite rules. Introduce `a _ b _ h`. Conclude with `Units.ext h`. Introduce `b hb`. Conclude with `⟨Units.mk0 b (by simpa using hb), by simp, rfl⟩`.

Introduce `a _`. Both sides reduce to the same expression.
-/
theorem sum_eq_zero_add_units {k : Type} [Field k] [Fintype k] {M : Type} [AddCommMonoid M]
    (g : k → M) : ∑ x : k, g x = g 0 + ∑ x : kˣ, g x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
  congr 1
  symm
  refine Finset.sum_bij (fun x _ => (x : k)) ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro b hb
    exact ⟨Units.mk0 b (by simpa using hb), by simp, rfl⟩
  · intro a _; rfl

/- English proof (translation)
Take `⟨m, hm, hsum⟩` from `sum_norm_units s hs r hr`. Establish `hq` using `card_eq_sq s hs r hr`. Use `set q := (Finset.univ.filter (fun x : k => s x = x)).card with hqdef`. Use `set a := (Finset.univ.filter (fun x : kˣ => s x = x)).card with hadef`. Establish `hqa : q = 1 + a`.

Use `sum_eq_zero_add_units (fun x : k => if s x = x then (1 : ℕ) else 0)` as an intermediate fact. Rewrite using `[hqdef, hadef, Finset.card_filter, Finset.card_filter, this, if_pos (map_zero s)]`. Establish `ha : 0 < a` using `Finset.card_pos.2 ⟨1, by simp⟩`. Establish `hcard : Fintype.card k = 1 + Fintype.card kˣ`. Use `sum_eq_zero_add_units (fun _ : k => (1 : ℕ))` as an intermediate fact.

Simplify using `using this`. Establish `hmq : m = q + 1`. Apply `Nat.eq_of_mul_eq_mul_right ha` to reduce the goal to its premises. Rewrite `hcard` using `[hm, hq, hqa]`. Rewrite using `[hqa]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hz : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0`. Establish `h1 : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f (u + y) = ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y`. Use `Finset.sum_equiv (Equiv.addLeft u) ?_ ?_` and prove the remaining obligations. Introduce `i`.

Simplify using `[hu]`. Introduce `i _`. Both sides reduce to the same expression. Simplify using `only [hadd, ← Finset.mul_sum] at h1`. Establish `h2 : (f u - 1) * ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0`.

Take the linear combination `h1`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hfu)`. Establish `hu1 : ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y = -1`. Use `sum_eq_zero_add_units (fun x : k => if s x = x then f x else 0)` as an intermediate fact. Rewrite `this` using `[← Finset.sum_filter, hz, ← Finset.sum_filter]`.

Simplify using `only [map_zero, if_true, h0] at this`. Take the linear combination `-this`. Rewrite using `[sum_eq_zero_add_units, hsum, hu1, hq, hmq]`. Use `push_cast`. Rewrite using `[Real.sqrt_sq (Nat.cast_nonneg q)]`.

Simplify using `[h0]`.
-/
theorem gauss_field {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) (f : k → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b) (h0 : f 0 = 1)
    (u : k) (hu : s u = u) (hfu : f u ≠ 1) :
    ∑ x : k, f (x * s x) = -(Real.sqrt (Fintype.card k) : ℂ) := by
  obtain ⟨m, hm, hsum⟩ := sum_norm_units s hs r hr
  have hq := card_eq_sq s hs r hr
  set q := (Finset.univ.filter (fun x : k => s x = x)).card with hqdef
  set a := (Finset.univ.filter (fun x : kˣ => s x = x)).card with hadef
  have hqa : q = 1 + a := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then (1 : ℕ) else 0)
    rw [hqdef, hadef, Finset.card_filter, Finset.card_filter, this, if_pos (map_zero s)]
  have ha : 0 < a := Finset.card_pos.2 ⟨1, by simp⟩
  have hcard : Fintype.card k = 1 + Fintype.card kˣ := by
    have := sum_eq_zero_add_units (fun _ : k => (1 : ℕ))
    simpa using this
  have hmq : m = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_right ha
    rw [hm, hq, hqa] at hcard
    rw [hqa]
    nlinarith
  have hz : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f (u + y) =
        ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y := by
      refine Finset.sum_equiv (Equiv.addLeft u) ?_ ?_
      · intro i; simp [hu]
      · intro i _; rfl
    simp only [hadd, ← Finset.mul_sum] at h1
    have h2 : (f u - 1) * ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hfu)
  have hu1 : ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y = -1 := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then f x else 0)
    rw [← Finset.sum_filter, hz, ← Finset.sum_filter] at this
    simp only [map_zero, if_true, h0] at this
    linear_combination -this
  rw [sum_eq_zero_add_units, hsum, hu1, hq, hmq]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg q)]
  simp [h0]

/- English proof (translation)
Introduce `R _ σ w hσ hw P hP hfin hst ⟨r, hr⟩ χ hadd h0 hχP hχσ ⟨t, ht⟩`. Use `letI : Field (R ⧸ P) := Ideal.Quotient.field P`. Use `letI : Fintype (R ⧸ P) := Fintype.ofFinite _`. Set `s : R ⧸ P →+* R ⧸ P` to `Ideal.quotientMap P σ (fun r hr => hst r hr)`. Establish `hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x)` using `fun x => rfl`.

Establish `hout : ∀ q : R ⧸ P, Ideal.Quotient.mk P (Quotient.out q) = q` using `fun q => Quotient.out_eq q`. Establish `hcongr : ∀ a b : R, Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → χ a = χ b`. Introduce `a b h`. Establish `h1` using `hχP _ (Ideal.Quotient.eq.1 h)`. Establish `h2` using `hadd (a - b) b`.

Rewrite `h2` using `[h1, one_mul, sub_add_cancel]`. Conclude with `h2`. Set `f : R ⧸ P → ℂ` to `fun q => χ (w * Quotient.out q)`. Establish `hf : ∀ a : R, f (Ideal.Quotient.mk P a) = χ (w * a)` using `fun a => hcongr _ _ (by rw [map_mul, map_mul, hout])`. Establish `key` using `gauss_field s (fun x => by`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hs, hs, hσ])`. Use the proof step `(Ideal.Quotient.mk P r)`. Use the proof step `(by`. Rewrite using `[hs, ← map_sub]`.

Conclude with `fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h))`. Use `f`. Use the proof step `(fun a b => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Rewrite using `[← map_add, hf, hf, hf, mul_add, hadd])`. Use the proof step `(by rw [← map_zero (Ideal.Quotient.mk P), hf, mul_zero, h0])`. Use the proof step `(Ideal.Quotient.mk P (t + σ t))`. Use the proof step `(by rw [hs, map_add σ, hσ, add_comm])`. Use the proof step `(by`.

Rewrite using `[hf, mul_add, hadd, ← hχσ (w * σ t), map_mul, hσ, ← hadd, ← add_mul, hw, one_mul]`. Conclude with `ht)`. Rewrite using `[finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← key]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← hout q]`.

Rewrite using `[hs, ← map_mul, hf, mul_assoc]`.
-/
theorem gauss_quotient : ∀ {R : Type} [CommRing R] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r ∈ P, σ r ∈ P) → (∃ r, σ r - r ∉ P) → ∀ χ : R → ℂ, (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → (∀ r ∈ P, χ r = 1) → (∀ t, χ (σ t) = χ t) → (∃ t, χ t ≠ 1) → (∑ᶠ q : R ⧸ P, χ (w * (Quotient.out q : R) * σ (Quotient.out q : R))) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) := by
  intro R _ σ w hσ hw P hP hfin hst ⟨r, hr⟩ χ hadd h0 hχP hχσ ⟨t, ht⟩
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ (fun r hr => hst r hr)
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
  have hout : ∀ q : R ⧸ P, Ideal.Quotient.mk P (Quotient.out q) = q := fun q => Quotient.out_eq q
  have hcongr : ∀ a b : R, Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → χ a = χ b := by
    intro a b h
    have h1 := hχP _ (Ideal.Quotient.eq.1 h)
    have h2 := hadd (a - b) b
    rw [h1, one_mul, sub_add_cancel] at h2
    exact h2
  let f : R ⧸ P → ℂ := fun q => χ (w * Quotient.out q)
  have hf : ∀ a : R, f (Ideal.Quotient.mk P a) = χ (w * a) := fun a =>
    hcongr _ _ (by rw [map_mul, map_mul, hout])
  have key := gauss_field s
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, hσ])
    (Ideal.Quotient.mk P r)
    (by
      rw [hs, ← map_sub]
      exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h))
    f
    (fun a b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_add, hf, hf, hf, mul_add, hadd])
    (by rw [← map_zero (Ideal.Quotient.mk P), hf, mul_zero, h0])
    (Ideal.Quotient.mk P (t + σ t))
    (by rw [hs, map_add σ, hσ, add_comm])
    (by
      rw [hf, mul_add, hadd, ← hχσ (w * σ t), map_mul, hσ, ← hadd, ← add_mul, hw, one_mul]
      exact ht)
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← key]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [← hout q]
  rw [hs, ← map_mul, hf, mul_assoc]

end GlobalTheory.NormFormGauss
