import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit

variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

/- English proof (translation)
Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[h.card]`. Use `h.one_lt` as an intermediate fact. Conclude with `pow_ne_zero 2 (by omega)`.
-/
theorem finite_of_resAlg (h : ResAlg E τ q ε) : Finite E := by
  apply Nat.finite_of_card_ne_zero
  rw [h.card]
  have := h.one_lt
  exact pow_ne_zero 2 (by omega)

/- English proof (translation)
Use `finite_of_resAlg h` as an intermediate fact. Rewrite using `[← Finite.one_lt_card_iff_nontrivial, h.card]`. Use `h.one_lt` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nontrivial_of_resAlg (h : ResAlg E τ q ε) : Nontrivial E := by
  have := finite_of_resAlg h
  rw [← Finite.one_lt_card_iff_nontrivial, h.card]
  have := h.one_lt
  nlinarith

/- English proof (translation)
Use `finite_of_resAlg h` as an intermediate fact. Take `⟨u, hu, hb⟩` from `h.basis`. Establish `hbij : Function.Bijective (fun p : {x : E // τ x = x} × {x : E // τ x = x} => (p.1 : E) + p.2 * u)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy`.

Simplify using `only at hxy`. Establish `h2` using `congrArg τ hxy`. Simplify using `only [map_add, map_mul, hx, hy, hx', hy'] at h2`. Establish `hyy : y = y'`. Establish `h3 : (y - y') * (u - τ u) = 0` using `by linear_combination hxy - h2`.

Rewrite `h3` using `[hu.mul_left_eq_zero, sub_eq_zero]`. Conclude with `h3`. Substitute `hyy` using the available equality. Establish `hxx : x = x'` using `by linear_combination hxy`. Substitute `hxx` using the available equality.

Both sides reduce to the same expression. Introduce `a`. Take `⟨x, y, hx, hy, rfl⟩` from `hb a`. Conclude with `⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩`. Establish `hc` using `Nat.card_congr (Equiv.ofBijective _ hbij)`.

Rewrite `hc` using `[Nat.card_prod, h.card]`. Establish `h4 : Nat.card {x : E // τ x = x} ^ 2 = q ^ 2` using `by rw [sq]; exact hc`. Conclude with `Nat.pow_left_injective (by norm_num) h4`.
-/
theorem card_fixed (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x} = q := by
  have := finite_of_resAlg h
  obtain ⟨u, hu, hb⟩ := h.basis
  have hbij : Function.Bijective
      (fun p : {x : E // τ x = x} × {x : E // τ x = x} => (p.1 : E) + p.2 * u) := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      simp only at hxy
      have h2 := congrArg τ hxy
      simp only [map_add, map_mul, hx, hy, hx', hy'] at h2
      have hyy : y = y' := by
        have h3 : (y - y') * (u - τ u) = 0 := by linear_combination hxy - h2
        rw [hu.mul_left_eq_zero, sub_eq_zero] at h3
        exact h3
      subst hyy
      have hxx : x = x' := by linear_combination hxy
      subst hxx
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, h.card] at hc
  have h4 : Nat.card {x : E // τ x = x} ^ 2 = q ^ 2 := by rw [sq]; exact hc
  exact Nat.pow_left_injective (by norm_num) h4

/- English proof (translation)
Use `finite_of_resAlg h` as an intermediate fact. Establish `e1 : Nat.card {x : E // τ x = x ∧ x ≠ 0} = Nat.card {y : {x : E // τ x = x} // y ≠ ⟨0, map_zero τ⟩}` using `Nat.card_congr { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h0 => x.2.2 (congrArg Subtype.val h0)⟩ invFun := fun y => ⟨y.1.1, y.1.2, fun h0 => y.2 (Subtype.ext h0)⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `e2` using `Nat.card_congr (Equiv.optionSubtypeNe (⟨0, map_zero τ⟩ : {x : E // τ x = x}))`. Rewrite `e2` using `[Finite.card_option, card_fixed h]`. Rewrite using `[e1, ← e2, Nat.add_sub_cancel]`.
-/
theorem card_fixed_ne (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x ∧ x ≠ 0} = q - 1 := by
  classical
  have := finite_of_resAlg h
  have e1 : Nat.card {x : E // τ x = x ∧ x ≠ 0} =
      Nat.card {y : {x : E // τ x = x} // y ≠ ⟨0, map_zero τ⟩} := Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h0 => x.2.2 (congrArg Subtype.val h0)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, fun h0 => y.2 (Subtype.ext h0)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (⟨0, map_zero τ⟩ : {x : E // τ x = x}))
  rw [Finite.card_option, card_fixed h] at e2
  rw [e1, ← e2, Nat.add_sub_cancel]

/- English proof (translation)
Establish `h2 : s * τ v = 1`. Establish `h3` using `congrArg τ hv`. Rewrite `h3` using `[map_mul, map_one, hs]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fixed_inv {s v : E} (hs : τ s = s) (hv : s * v = 1) : τ v = v := by
  have h2 : s * τ v = 1 := by
    have h3 := congrArg τ hv
    rwa [map_mul, map_one, hs] at h3
  calc τ v = (v * s) * τ v := by rw [mul_comm v s, hv, one_mul]
    _ = v := by rw [mul_assoc, h2, mul_one]

/- English proof (translation)
Use `nontrivial_of_resAlg h` as an intermediate fact. Take `⟨u, hu, -⟩` from `h.basis`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hnf ⟨exists_pair_ne E, mul_comm, fun {a} ha => by`. Take `⟨b, hb⟩` from `(hc a ha).exists_right_inv`. Conclude with `⟨b, hb⟩⟩`. Establish `haτ : a * τ a = 0`. Assume the negation of the conclusion as `hne`.

Apply `hau` to reduce the goal to its premises. Establish `hfix : τ (a * τ a) = a * τ a` using `by rw [map_mul, h.inv, mul_comm]`. Conclude with `isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne)`. Establish `hw : ∃ w : E, a * w + τ (a * w) ≠ 0`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `h1` using `hc 1`. Establish `h2` using `hc u`. Rewrite `h1` using `[mul_one]`. Apply `ha0` to reduce the goal to its premises.

Establish `h3 : a * (u - τ u) = 0`. Rewrite `h2` using `[map_mul]`. Take the linear combination `h2 - τ u * h1`. Conclude with `hu.mul_left_eq_zero.1 h3`. Take `⟨w, hw⟩` from `hw`.

Establish `hTfix : τ (a * w + τ (a * w)) = a * w + τ (a * w)` using `by rw [map_add, h.inv, add_comm]`. Take `⟨s, hs⟩` from `(h.fixedUnit _ hTfix hw).exists_right_inv`. Establish `hsf : τ s = s` using `fixed_inv hTfix hs`. Use `⟨a * w * s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hsf]`.

Take the linear combination `hs`. Rewrite using `[map_mul, hsf, map_mul]`. Take the linear combination `(w * τ w * s * s) * haτ`.
-/
theorem exists_idem (h : ResAlg E τ q ε) (hnf : ¬ IsField E) :
    ∃ e : E, e + τ e = 1 ∧ e * τ e = 0 := by
  have := nontrivial_of_resAlg h
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push Not at hc
    exact hnf ⟨exists_pair_ne E, mul_comm, fun {a} ha => by
      obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
      exact ⟨b, hb⟩⟩
  have haτ : a * τ a = 0 := by
    by_contra hne
    apply hau
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne)
  have hw : ∃ w : E, a * w + τ (a * w) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 := hc 1
    have h2 := hc u
    rw [mul_one] at h1
    apply ha0
    have h3 : a * (u - τ u) = 0 := by
      rw [map_mul] at h2
      linear_combination h2 - τ u * h1
    exact hu.mul_left_eq_zero.1 h3
  obtain ⟨w, hw⟩ := hw
  have hTfix : τ (a * w + τ (a * w)) = a * w + τ (a * w) := by rw [map_add, h.inv, add_comm]
  obtain ⟨s, hs⟩ := (h.fixedUnit _ hTfix hw).exists_right_inv
  have hsf : τ s = s := fixed_inv hTfix hs
  refine ⟨a * w * s, ?_, ?_⟩
  · rw [map_mul, hsf]
    linear_combination hs
  · rw [map_mul, hsf, map_mul]
    linear_combination (w * τ w * s * s) * haτ

/- English proof (translation)
Take `⟨e, he1, he0⟩` from `exists_idem h hnf`. Establish `hτe : τ (τ e) = e` using `h.inv e`. Establish `hee : e * e = e` using `by linear_combination e * he1 - he0`. Establish `hff : τ e * τ e = τ e` using `by linear_combination τ e * he1 - he0`. Establish `hiso : ∀ α : E, ∃ s : E, τ α = α → α ≠ 0 → α * s = 1 ∧ τ s = s`.

Introduce `α`. Distinguish the cases in `hc : τ α = α ∧ α ≠ 0`. Take `⟨s, hs⟩` from `(h.fixedUnit α hc.1 hc.2).exists_right_inv`. Conclude with `⟨s, fun _ _ => ⟨hs, fixed_inv hc.1 hs⟩⟩`. Conclude with `⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩`.

Use `choose s hs using hiso`. Establish `hfixA : ∀ a : E, τ (a * e + τ a * τ e) = a * e + τ a * τ e`. Introduce `a`. Simplify using `only [map_add, map_mul, h.inv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hneA : ∀ a : E, a * τ a = t → a * e + τ a * τ e ≠ 0`. Introduce `a ha hα`. Apply `t0` to reduce the goal to its premises. Establish `h1 : a * e = 0` using `by linear_combination e * hα - a * hee - τ a * he0`. Establish `h2 : τ a * τ e = 0` using `by linear_combination τ e * hα - τ a * hff - a * he0`.

Take the linear combination `-ha + τ a * h1 + a * h2 - a * τ a * he1`. Rewrite using `[← card_fixed_ne h]`. Conclude with `Nat.card_congr { toFun := fun a => ⟨a.1 * e + τ a.1 * τ e, hfixA a.1, hneA a.1 a.2⟩ invFun := fun x => ⟨x.1 * e + t * s x.1 * τ e, by`. Take `⟨hs1, hs2⟩` from `hs x.1 x.2.1 x.2.2`. Simplify using `only [map_add, map_mul, x.2.1, ht, hs2, hτe]`.

Take the linear combination `(x.1 ^ 2 + t ^ 2 * s x.1 ^ 2) * he0 + x.1 * t * s x.1 * hee + x.1 * t * s x.1 * hff + x.1 * t * s x.1 * he1 + t * hs1⟩`. Use `left_inv := fun a => by`. Take `⟨hs1, -⟩` from `hs _ (hfixA a.1) (hneA a.1 a.2)`. Establish `ha` using `a.2`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only`. Take the linear combination `a.1 * hee + (τ a.1 - a.1 ^ 2 * s (a.1 * e + τ a.1 * τ e)) * he0 + a.1 * he1 - s (a.1 * e + τ a.1 * τ e) * τ e * ha + a.1 * τ e * hs1 - a.1 * τ a.1 * s (a.1 * e + τ a.1 * τ e) * hff`. Use `right_inv := fun x => by`. Take `⟨-, hs2⟩` from `hs x.1 x.2.1 x.2.2`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only`. Simplify using `only [map_add, map_mul, x.2.1, ht, hs2, hτe]`. Take the linear combination `x.1 * hee + 2 * t * s x.1 * he0 + x.1 * hff + x.1 * he1 }`.
-/
theorem card_fibre_split (h : ResAlg E τ q ε) (hnf : ¬ IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q - 1 := by
  obtain ⟨e, he1, he0⟩ := exists_idem h hnf
  have hτe : τ (τ e) = e := h.inv e
  have hee : e * e = e := by linear_combination e * he1 - he0
  have hff : τ e * τ e = τ e := by linear_combination τ e * he1 - he0
  have hiso : ∀ α : E, ∃ s : E, τ α = α → α ≠ 0 → α * s = 1 ∧ τ s = s := by
    intro α
    by_cases hc : τ α = α ∧ α ≠ 0
    · obtain ⟨s, hs⟩ := (h.fixedUnit α hc.1 hc.2).exists_right_inv
      exact ⟨s, fun _ _ => ⟨hs, fixed_inv hc.1 hs⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hiso
  have hfixA : ∀ a : E, τ (a * e + τ a * τ e) = a * e + τ a * τ e := by
    intro a
    simp only [map_add, map_mul, h.inv]
    ring
  have hneA : ∀ a : E, a * τ a = t → a * e + τ a * τ e ≠ 0 := by
    intro a ha hα
    apply t0
    have h1 : a * e = 0 := by linear_combination e * hα - a * hee - τ a * he0
    have h2 : τ a * τ e = 0 := by linear_combination τ e * hα - τ a * hff - a * he0
    linear_combination -ha + τ a * h1 + a * h2 - a * τ a * he1
  rw [← card_fixed_ne h]
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1 * e + τ a.1 * τ e, hfixA a.1, hneA a.1 a.2⟩
      invFun := fun x => ⟨x.1 * e + t * s x.1 * τ e, by
        obtain ⟨hs1, hs2⟩ := hs x.1 x.2.1 x.2.2
        simp only [map_add, map_mul, x.2.1, ht, hs2, hτe]
        linear_combination (x.1 ^ 2 + t ^ 2 * s x.1 ^ 2) * he0 + x.1 * t * s x.1 * hee +
          x.1 * t * s x.1 * hff + x.1 * t * s x.1 * he1 + t * hs1⟩
      left_inv := fun a => by
        obtain ⟨hs1, -⟩ := hs _ (hfixA a.1) (hneA a.1 a.2)
        have ha := a.2
        apply Subtype.ext
        dsimp only
        linear_combination a.1 * hee + (τ a.1 - a.1 ^ 2 * s (a.1 * e + τ a.1 * τ e)) * he0 + a.1 * he1 -
          s (a.1 * e + τ a.1 * τ e) * τ e * ha + a.1 * τ e * hs1 -
          a.1 * τ a.1 * s (a.1 * e + τ a.1 * τ e) * hff
      right_inv := fun x => by
        obtain ⟨-, hs2⟩ := hs x.1 x.2.1 x.2.2
        apply Subtype.ext
        dsimp only
        simp only [map_add, map_mul, x.2.1, ht, hs2, hτe]
        linear_combination x.1 * hee + 2 * t * s x.1 * he0 + x.1 * hff + x.1 * he1 }

/- English proof (translation)
Take `⟨b, hb⟩` from `hf.mul_inv_cancel ha`. Conclude with `IsUnit.of_mul_eq_one b hb`.
-/
theorem isUnit_of_ne (hf : IsField E) {a : E} (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel ha
  exact IsUnit.of_mul_eq_one b hb

/- English proof (translation)
Use `finite_of_resAlg h` as an intermediate fact. Use `nontrivial_of_resAlg h` as an intermediate fact. Establish `e1 : Nat.card Eˣ = Nat.card {a : E // a ≠ 0}` using `Nat.card_congr { toFun := fun u => ⟨u, u.ne_zero⟩ invFun := fun a => (isUnit_of_ne hf a.2).unit left_inv := fun u => Units.ext rfl right_inv := fun a => rfl }`. Establish `e2` using `Nat.card_congr (Equiv.optionSubtypeNe (0 : E))`. Rewrite `e2` using `[Finite.card_option, h.card]`.

Rewrite using `[e1, ← e2, Nat.add_sub_cancel]`.
-/
theorem card_units (h : ResAlg E τ q ε) (hf : IsField E) : Nat.card Eˣ = q ^ 2 - 1 := by
  classical
  have := finite_of_resAlg h
  have := nontrivial_of_resAlg h
  have e1 : Nat.card Eˣ = Nat.card {a : E // a ≠ 0} := Nat.card_congr
    { toFun := fun u => ⟨u, u.ne_zero⟩
      invFun := fun a => (isUnit_of_ne hf a.2).unit
      left_inv := fun u => Units.ext rfl
      right_inv := fun a => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (0 : E))
  rw [Finite.card_option, h.card] at e2
  rw [e1, ← e2, Nat.add_sub_cancel]

def tauU (τ : E →+* E) : Eˣ →* Eˣ := Units.map (τ : E →* E)

def ratioU (τ : E →+* E) : Eˣ →* Eˣ := MonoidHom.id _ / tauU τ

def normU (τ : E →+* E) : Eˣ →* Eˣ := MonoidHom.id _ * tauU τ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratioU_apply (b : Eˣ) : ratioU τ b = b / tauU τ b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normU_apply (b : Eˣ) : normU τ b = b * tauU τ b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_tauU (b : Eˣ) : ((tauU τ b : Eˣ) : E) = τ b := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_tauU, coe_tauU, h.inv]`.
-/
theorem tauU_tauU (h : ResAlg E τ q ε) (b : Eˣ) : tauU τ (tauU τ b) = b := by
  apply Units.ext
  rw [coe_tauU, coe_tauU, h.inv]

/- English proof (translation)
Rewrite using `[ratioU_apply, div_eq_iff_eq_mul, Units.ext_iff, Units.val_mul, coe_tauU]`.
-/
theorem ratioU_eq_iff {c a : Eˣ} : ratioU τ c = a ↔ (c : E) = a * τ c := by
  rw [ratioU_apply, div_eq_iff_eq_mul, Units.ext_iff, Units.val_mul, coe_tauU]

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker, normU_apply, Units.ext_iff, Units.val_mul, coe_tauU, Units.val_one]`.
-/
theorem mem_ker_normU {k : Eˣ} : k ∈ (normU τ).ker ↔ (k : E) * τ k = 1 := by
  rw [MonoidHom.mem_ker, normU_apply, Units.ext_iff, Units.val_mul, coe_tauU, Units.val_one]

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker, ratioU_eq_iff, Units.val_one, one_mul]`.
-/
theorem mem_ker_ratioU {k : Eˣ} : k ∈ (ratioU τ).ker ↔ (k : E) = τ k := by
  rw [MonoidHom.mem_ker, ratioU_eq_iff, Units.val_one, one_mul]

/- English proof (translation)
Use `nontrivial_of_resAlg h` as an intermediate fact. Rewrite using `[← card_fixed_ne h]`. Conclude with `Nat.card_congr { toFun := fun k => ⟨((k : Eˣ) : E), (mem_ker_ratioU.1 k.2).symm, (k : Eˣ).ne_zero⟩ invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, mem_ker_ratioU.2 x.2.1.symm⟩ left_inv := fun k => Subtype.ext (Units.ext rfl) right_inv := fun x => rfl }`.
-/
theorem card_ker_ratioU (h : ResAlg E τ q ε) : Nat.card (ratioU τ).ker = q - 1 := by
  have := nontrivial_of_resAlg h
  rw [← card_fixed_ne h]
  exact Nat.card_congr
    { toFun := fun k => ⟨((k : Eˣ) : E), (mem_ker_ratioU.1 k.2).symm, (k : Eˣ).ne_zero⟩
      invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, mem_ker_ratioU.2 x.2.1.symm⟩
      left_inv := fun k => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }

/- English proof (translation)
Use `nontrivial_of_resAlg h` as an intermediate fact. Use extensionality with `k`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Take `⟨c, rfl⟩` from `MonoidHom.mem_range.1 hk`.

Rewrite using `[MonoidHom.mem_ker, normU_apply, ratioU_apply, map_div, tauU_tauU h]`. Simplify using `[div_eq_mul_inv, mul_assoc]`. Introduce `hk`. Rewrite `hk` using `[mem_ker_normU]`. Take `⟨u, hu, -⟩` from `h.basis`.

Establish `key : ∀ x : E, x + k * τ x = k * τ (x + k * τ x)`. Introduce `x`. Rewrite using `[map_add, map_mul, h.inv]`. Take the linear combination `(-x) * hk`. Establish `hx : ∃ x : E, x + k * τ x ≠ 0`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1` using `hc 1`. Establish `h2` using `hc u`. Rewrite `h1` using `[map_one, mul_one]`.

Apply `hu.ne_zero` to reduce the goal to its premises. Take the linear combination `h2 - τ u * h1`. Take `⟨x, hx⟩` from `hx`. Conclude with `MonoidHom.mem_range.2 ⟨(isUnit_of_ne hf hx).unit, ratioU_eq_iff.2 (key x)⟩`.
-/
theorem range_ratioU (h : ResAlg E τ q ε) (hf : IsField E) :
    (ratioU τ).range = (normU τ).ker := by
  have := nontrivial_of_resAlg h
  ext k
  constructor
  · intro hk
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hk
    rw [MonoidHom.mem_ker, normU_apply, ratioU_apply, map_div, tauU_tauU h]
    simp [div_eq_mul_inv, mul_assoc]
  · intro hk
    rw [mem_ker_normU] at hk
    obtain ⟨u, hu, -⟩ := h.basis
    have key : ∀ x : E, x + k * τ x = k * τ (x + k * τ x) := by
      intro x
      rw [map_add, map_mul, h.inv]
      linear_combination (-x) * hk
    have hx : ∃ x : E, x + k * τ x ≠ 0 := by
      by_contra hc
      push Not at hc
      have h1 := hc 1
      have h2 := hc u
      rw [map_one, mul_one] at h1
      apply hu.ne_zero
      linear_combination h2 - τ u * h1
    obtain ⟨x, hx⟩ := hx
    exact MonoidHom.mem_range.2 ⟨(isUnit_of_ne hf hx).unit, ratioU_eq_iff.2 (key x)⟩

/- English proof (translation)
Take `⟨r, rfl⟩ : ∃ r, q = r + 1` from `⟨q - 1, by omega⟩`. Establish `h2 : (r + 1) ^ 2 = r * (r + 1 + 1) + 1` using `by ring`. Rewrite using `[h2, Nat.add_sub_cancel, Nat.add_sub_cancel]`.
-/
theorem sq_sub_one (hq : 1 < q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h2 : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
  rw [h2, Nat.add_sub_cancel, Nat.add_sub_cancel]

/- English proof (translation)
Use `finite_of_resAlg h` as an intermediate fact. Use `nontrivial_of_resAlg h` as an intermediate fact. Establish `hq` using `h.one_lt`. Establish `hU : Nat.card Eˣ = q ^ 2 - 1` using `card_units h hf`. Establish `hsq` using `sq_sub_one hq`.

Establish `lag : ∀ f : Eˣ →* Eˣ, Nat.card Eˣ = Nat.card f.range * Nat.card f.ker` using `fun f => by`. Rewrite using `[Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]`. Establish `hR : Nat.card (ratioU τ).range = q + 1`. Establish `e` using `lag (ratioU τ)`. Rewrite `e` using `[card_ker_ratioU h, hU, hsq, mul_comm (q - 1)]`.

Conclude with `(Nat.eq_of_mul_eq_mul_right (by omega) e).symm`. Establish `hK : Nat.card (normU τ).ker = q + 1`. Rewrite using `[← range_ratioU h hf]`. Conclude with `hR`. Establish `hN : Nat.card (normU τ).range = q - 1`.

Establish `e` using `lag (normU τ)`. Rewrite `e` using `[hK, hU, hsq]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (by omega) e).symm`. Set `S : Set Eˣ` to `{k | τ (k : E) = k}`. Establish `hS : Nat.card S = q - 1`.

Rewrite using `[← card_fixed_ne h]`. Conclude with `Nat.card_congr { toFun := fun k => ⟨((k.1 : Eˣ) : E), k.2, k.1.ne_zero⟩ invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, x.2.1⟩ left_inv := fun k => Subtype.ext (Units.ext rfl) right_inv := fun x => rfl }`. Establish `hsub : ((normU τ).range : Set Eˣ) ⊆ S`. Introduce `k hk`. Take `⟨b, rfl⟩` from `MonoidHom.mem_range.1 hk`.

Use `show τ ((normU τ b : Eˣ) : E) = normU τ b`. Rewrite using `[normU_apply, Units.val_mul, coe_tauU, map_mul, h.inv, mul_comm]`. Establish `heq : ((normU τ).range : Set Eˣ) = S`. Use `Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite S)` and prove the remaining obligations. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hS]`.

Conclude with `hN.ge`. Establish `htu : IsUnit t` using `isUnit_of_ne hf t0`. Establish `hmem : htu.unit ∈ (normU τ).range`. Rewrite using `[← SetLike.mem_coe, heq]`. Conclude with `ht`.

Take `⟨a₀, ha₀⟩` from `MonoidHom.mem_range.1 hmem`. Establish `hn : ∀ b : Eˣ, (b : E) * τ b = t → normU τ b = htu.unit` using `fun b hb => Units.ext (by rw [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec]; exact hb)`. Establish `hna : (a₀ : E) * τ a₀ = t`. Establish `h5` using `congrArg Units.val ha₀`. Rewrite `h5` using `[normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec]`. Then use the resulting hypothesis.

Establish `hau : ∀ a : {a : E // a * τ a = t}, IsUnit a.1` using `fun a => isUnit_of_mul_isUnit_left (show IsUnit (a.1 * τ a.1) by rw [a.2]; exact htu)`. Establish `hna' : ∀ a : {a : E // a * τ a = t}, normU τ (hau a).unit = htu.unit` using `fun a => hn _ (by rw [IsUnit.unit_spec]; exact a.2)`. Rewrite using `[← hK]`. Use `symm`. Conclude with `Nat.card_congr { toFun := fun k => ⟨(((k : Eˣ) * a₀ : Eˣ) : E), by`.

Establish `hk` using `mem_ker_normU.1 k.2`. Rewrite using `[Units.val_mul, map_mul]`. Take the linear combination `((a₀ : E) * τ (a₀ : E)) * hk + hna⟩`. Use `invFun := fun a => ⟨(hau a).unit * a₀⁻¹, by`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, ha₀, hna' a, mul_inv_cancel]⟩`.

Use `left_inv := fun k => Subtype.ext (Units.ext (by simp [mul_assoc]))`. Use `right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }`.
-/
theorem card_fibre_field (h : ResAlg E τ q ε) (hf : IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q + 1 := by
  have := finite_of_resAlg h
  have := nontrivial_of_resAlg h
  have hq := h.one_lt
  have hU : Nat.card Eˣ = q ^ 2 - 1 := card_units h hf
  have hsq := sq_sub_one hq
  have lag : ∀ f : Eˣ →* Eˣ, Nat.card Eˣ = Nat.card f.range * Nat.card f.ker := fun f => by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hR : Nat.card (ratioU τ).range = q + 1 := by
    have e := lag (ratioU τ)
    rw [card_ker_ratioU h, hU, hsq, mul_comm (q - 1)] at e
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e).symm
  have hK : Nat.card (normU τ).ker = q + 1 := by
    rw [← range_ratioU h hf]
    exact hR
  have hN : Nat.card (normU τ).range = q - 1 := by
    have e := lag (normU τ)
    rw [hK, hU, hsq] at e
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e).symm
  let S : Set Eˣ := {k | τ (k : E) = k}
  have hS : Nat.card S = q - 1 := by
    rw [← card_fixed_ne h]
    exact Nat.card_congr
      { toFun := fun k => ⟨((k.1 : Eˣ) : E), k.2, k.1.ne_zero⟩
        invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, x.2.1⟩
        left_inv := fun k => Subtype.ext (Units.ext rfl)
        right_inv := fun x => rfl }
  have hsub : ((normU τ).range : Set Eˣ) ⊆ S := by
    intro k hk
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hk
    show τ ((normU τ b : Eˣ) : E) = normU τ b
    rw [normU_apply, Units.val_mul, coe_tauU, map_mul, h.inv, mul_comm]
  have heq : ((normU τ).range : Set Eˣ) = S := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite S)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hS]
    exact hN.ge
  have htu : IsUnit t := isUnit_of_ne hf t0
  have hmem : htu.unit ∈ (normU τ).range := by
    rw [← SetLike.mem_coe, heq]
    exact ht
  obtain ⟨a₀, ha₀⟩ := MonoidHom.mem_range.1 hmem
  have hn : ∀ b : Eˣ, (b : E) * τ b = t → normU τ b = htu.unit := fun b hb =>
    Units.ext (by rw [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec]; exact hb)
  have hna : (a₀ : E) * τ a₀ = t := by
    have h5 := congrArg Units.val ha₀
    rwa [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec] at h5
  have hau : ∀ a : {a : E // a * τ a = t}, IsUnit a.1 := fun a =>
    isUnit_of_mul_isUnit_left (show IsUnit (a.1 * τ a.1) by rw [a.2]; exact htu)
  have hna' : ∀ a : {a : E // a * τ a = t}, normU τ (hau a).unit = htu.unit := fun a =>
    hn _ (by rw [IsUnit.unit_spec]; exact a.2)
  rw [← hK]
  symm
  exact Nat.card_congr
    { toFun := fun k => ⟨(((k : Eˣ) * a₀ : Eˣ) : E), by
        have hk := mem_ker_normU.1 k.2
        rw [Units.val_mul, map_mul]
        linear_combination ((a₀ : E) * τ (a₀ : E)) * hk + hna⟩
      invFun := fun a => ⟨(hau a).unit * a₀⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ha₀, hna' a, mul_inv_cancel]⟩
      left_inv := fun k => Subtype.ext (Units.ext (by simp [mul_assoc]))
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }

/- English proof (translation)
Introduce `E _ τ q ε h t ht t0`. Establish `hq` using `h.one_lt`. Break down `h.eps with ⟨rfl, hf⟩ | ⟨rfl, hnf⟩` into its components or cases. Rewrite using `[card_fibre_field h hf ht t0]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[card_fibre_split h hnf ht t0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_fibre : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by
  intro E _ τ q ε h t ht t0
  have hq := h.one_lt
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hnf⟩
  · rw [card_fibre_field h hf ht t0]
    omega
  · rw [card_fibre_split h hnf ht t0]
    omega

end GlobalTheory.CompanionTheory.UnrDens.NormUnit
