import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard

/- English proof (translation)
Set `TB` to `{x : B // ∀ a ∈ I, a • x = 0}`. Set `TA` to `{x : A // ∀ a ∈ I, a • x = 0}`. Set `TC` to `{x : C // ∀ a ∈ I, a • x = 0}`. Set `h : TB → TC` to `fun b => ⟨g b.1, fun a ha => by rw [← map_smul, b.2 a ha, map_zero]⟩`. Set `s : TC → TB` to `fun c => if hc : ∃ b, h b = c then hc.choose else ⟨0, fun a _ => smul_zero a⟩`.

Establish `hs : ∀ b : TB, h (s (h b)) = h b`. Introduce `b`. Establish `hc : ∃ b', h b' = h b` using `⟨b, rfl⟩`. Simplify using `only [s, dif_pos hc]`. Conclude with `hc.choose_spec`.

Establish `hk : ∀ b : TB, ∃ a, f a = b.1 - (s (h b)).1`. Introduce `b`. Apply `hfg` to reduce the goal to its premises. Use `congrArg Subtype.val (hs b)` as an intermediate fact. Simplify using `only [h] at this`.

Rewrite using `[map_sub, this, sub_self]`. Set `k : TB → A` to `fun b => (hk b).choose`. Establish `hkf : ∀ b, f (k b) = b.1 - (s (h b)).1` using `fun b => (hk b).choose_spec`. Establish `hkt : ∀ b, ∀ a ∈ I, a • k b = 0`. Introduce `b a ha`.

Apply `hf` to reduce the goal to its premises. Rewrite using `[map_smul, hkf, map_zero, smul_sub, b.2 a ha, (s (h b)).2 a ha, sub_zero]`. Set `Φ : TB → TA × TC` to `fun b => (⟨k b, hkt b⟩, h b)`. Establish `hΦ : Function.Injective Φ`. Introduce `b b' e`.

Establish `e1 : k b = k b'` using `congrArg (fun z : TA × TC => z.1.1) e`. Establish `e2 : h b = h b'` using `congrArg (fun z : TA × TC => z.2) e`. Establish `e3` using `hkf b`. Rewrite `e3` using `[e1, hkf b', e2]`. Conclude with `Subtype.ext (sub_left_injective e3).symm`.

Use `⟨Finite.of_injective Φ hΦ, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem torsion_exact_bound {R A B C : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] (I : Ideal R)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : ∀ b, g b = 0 → ∃ a, f a = b)
    [Finite {x : A // ∀ a ∈ I, a • x = 0}] [Finite {x : C // ∀ a ∈ I, a • x = 0}] :
    Finite {x : B // ∀ a ∈ I, a • x = 0} ∧
      Nat.card {x : B // ∀ a ∈ I, a • x = 0} ≤
        Nat.card {x : A // ∀ a ∈ I, a • x = 0} * Nat.card {x : C // ∀ a ∈ I, a • x = 0} := by
  classical
  let TB := {x : B // ∀ a ∈ I, a • x = 0}
  let TA := {x : A // ∀ a ∈ I, a • x = 0}
  let TC := {x : C // ∀ a ∈ I, a • x = 0}
  let h : TB → TC := fun b => ⟨g b.1, fun a ha => by rw [← map_smul, b.2 a ha, map_zero]⟩

  let s : TC → TB := fun c => if hc : ∃ b, h b = c then hc.choose else ⟨0, fun a _ => smul_zero a⟩
  have hs : ∀ b : TB, h (s (h b)) = h b := by
    intro b
    have hc : ∃ b', h b' = h b := ⟨b, rfl⟩
    simp only [s, dif_pos hc]
    exact hc.choose_spec
  have hk : ∀ b : TB, ∃ a, f a = b.1 - (s (h b)).1 := by
    intro b
    apply hfg
    have := congrArg Subtype.val (hs b)
    simp only [h] at this
    rw [map_sub, this, sub_self]
  let k : TB → A := fun b => (hk b).choose
  have hkf : ∀ b, f (k b) = b.1 - (s (h b)).1 := fun b => (hk b).choose_spec
  have hkt : ∀ b, ∀ a ∈ I, a • k b = 0 := by
    intro b a ha
    apply hf
    rw [map_smul, hkf, map_zero, smul_sub, b.2 a ha, (s (h b)).2 a ha, sub_zero]
  let Φ : TB → TA × TC := fun b => (⟨k b, hkt b⟩, h b)
  have hΦ : Function.Injective Φ := by
    intro b b' e
    have e1 : k b = k b' := congrArg (fun z : TA × TC => z.1.1) e
    have e2 : h b = h b' := congrArg (fun z : TA × TC => z.2) e
    have e3 := hkf b
    rw [e1, hkf b', e2] at e3
    exact Subtype.ext (sub_left_injective e3).symm
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card TB ≤ Nat.card (TA × TC) := Nat.card_le_card_of_injective Φ hΦ
    _ = _ := Nat.card_prod _ _

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (L : Set (Fin m → K))` using `by rw [hL.2]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, hty⟩` from `hy`. Use `⟨s * t, mul_ne_zero hs ht, ?_⟩` and prove the remaining obligations. Establish `e : (s * t) • (x + y) = t • (s • x) + s • (t • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm t s]`.

Rewrite using `[e]`. Conclude with `L.add_mem (L.smul_mem _ hsx) (L.smul_mem _ hty)`. Consider the case `smul c x _ hx`. Take `⟨t, ht, htx⟩` from `hx`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) c`.

Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbK : algebraMap (𝓞 K) K b ≠ 0`. Simplify using `using hb0`. Use `⟨b * t, mul_ne_zero hb0 ht, ?_⟩` and prove the remaining obligations. Establish `e : (b * t) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • x) = a • (t • x)`.

Use extensionality with `i`. Express the relevant statement in the definitionally equal form `(b * t) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) * x i) = a • (t • x i)`. Simplify using `only [Algebra.smul_def, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `L.smul_mem _ htx`.
-/
theorem exists_smul_mem {m : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} (hL : IsLat L)
    (v : Fin m → K) : ∃ t : 𝓞 K, t ≠ 0 ∧ t • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set (Fin m → K)) := by rw [hL.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact L.add_mem (L.smul_mem _ hsx) (L.smul_mem _ hty)
  | smul c x _ hx =>
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
      simpa using hb0
    refine ⟨b * t, mul_ne_zero hb0 ht, ?_⟩
    have e : (b * t) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • x) = a • (t • x) := by
      ext i
      change (b * t) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) * x i) = a • (t • x i)
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ htx

/- English proof (translation)
Take `⟨d, hd, hdi⟩` from `FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hfg`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Take `⟨a₀, ha₀, ha₀0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h𝔞`. Take `⟨c₀, hc₀, hc₀0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`. Use `set e : 𝓞 K := d * a₀ with he`.

Establish `he0 : e ≠ 0` using `mul_ne_zero hd0 ha₀0`. Establish `heK : algebraMap (𝓞 K) K e ≠ 0` using `by simpa using he0`. Set `J : Ideal (𝓞 K)` to `{ carrier := {o | ∀ a ∈ 𝔞, a • (algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e) ∈ 𝔠} add_mem' := by`. Introduce `x y hx hy a ha`. Use `𝔠.add_mem (hx a ha) (hy a ha)` as an intermediate fact.

Rewrite using `[map_add, add_div, smul_add]`. Conclude with `this`. Use the proof step `zero_mem' := by`. Introduce `a _`. Simplify using the standard rewrite rules.

Use the proof step `smul_mem' := by`. Introduce `c x hx a ha`. Use `𝔠.smul_mem c (hx a ha)` as an intermediate fact. Establish `e1 : a • (algebraMap (𝓞 K) K (c • x) / algebraMap (𝓞 K) K e) = c • a • (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K e)`. Rewrite using `[smul_eq_mul]`.

Simplify using `only [Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `this }`. Establish `hJmem : ∀ o, o ∈ J ↔ ∀ a ∈ 𝔞, a • (algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e) ∈ 𝔠` using `fun _ => Iff.rfl`.

Establish `hJ0 : J ≠ ⊥`. Take `⟨o, ho⟩` from `hdi c₀ hc₀`. Establish `ho' : algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K d * c₀`. Rewrite using `[ho, Algebra.smul_def]`. Establish `hdK : algebraMap (𝓞 K) K d ≠ 0` using `by simpa using hd0`.

Establish `ho0 : o ≠ 0`. Introduce `h`. Rewrite `ho'` using `[h, map_zero]`. Conclude with `mul_ne_zero hdK hc₀0 ho'.symm`. Introduce `hbot`.

Establish `hmem : e * o ∈ J`. Introduce `a _`. Establish `e1 : a • (algebraMap (𝓞 K) K (e * o) / algebraMap (𝓞 K) K e) = (a * d) • c₀`. Rewrite using `[map_mul, mul_div_cancel_left₀ _ heK, ho', Algebra.smul_def, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Conclude with `𝔠.smul_mem _ hc₀`. Rewrite `hmem` using `[hbot, Ideal.mem_bot]`. Conclude with `mul_ne_zero he0 ho0 hmem`. Establish `hmulmem : ∀ z ∈ 𝔞 * J, algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K e ∈ 𝔠`.

Introduce `z hz`. Use `Submodule.mul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `a ha j hj`. Use `hj a ha` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`.

Rewrite using `[map_mul, mul_div_assoc]`. Conclude with `this`. Introduce `x y hx hy`. Rewrite using `[map_add, add_div]`. Conclude with `𝔠.add_mem hx hy`.

Establish `hle : (𝔞 * J) ≤ J` using `Ideal.mul_le_right`. Establish `hleA : (𝔞 * J).toAddSubgroup ≤ J.toAddSubgroup` using `hle`. Establish `hNJ : Ideal.absNorm J ≠ 0`. Simplify `hJ0` using `[Ideal.absNorm_eq_zero_iff]`. Establish `hN𝔞 : Ideal.absNorm 𝔞 ≠ 0`.

Simplify `h𝔞` using `[Ideal.absNorm_eq_zero_iff]`. Establish `hidx : (𝔞 * J).toAddSubgroup.relIndex J.toAddSubgroup = Ideal.absNorm 𝔞`. Establish `h1` using `AddSubgroup.relIndex_mul_index hleA`. Establish `h2 : ∀ I : Ideal (𝓞 K), I.toAddSubgroup.index = Ideal.absNorm I`. Introduce `I`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2, h2, map_mul]`. Conclude with `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) h1`. Set `Q` to `↥J.toAddSubgroup ⧸ (𝔞 * J).toAddSubgroup.addSubgroupOf J.toAddSubgroup`.

Establish `hQfin : Finite Q`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Establish `: Nat.card Q = Ideal.absNorm 𝔞` using `hidx`. Rewrite using `[this]`. Conclude with `hN𝔞`.

Establish `hQcard : Nat.card Q = Ideal.absNorm 𝔞` using `hidx`. Establish `hrep : ∀ t : {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0}, ∃ o : ↥J.toAddSubgroup, Submodule.Quotient.mk (algebraMap (𝓞 K) K o.1 / algebraMap (𝓞 K) K e) = t.1`. Introduce and unpack `⟨t, ht⟩`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`. Establish `hx : ∀ a ∈ 𝔞, a • x ∈ 𝔠`.

Introduce `a ha`. Use `ht a ha` as an intermediate fact. Rewrite `this` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Take `⟨o, ho⟩` from `hdi _ (hx a₀ ha₀)`. Establish `ho' : algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e = x`.

Establish `hda : algebraMap (𝓞 K) K d * algebraMap (𝓞 K) K a₀ ≠ 0`. Rewrite using `[← map_mul]`. Conclude with `heK`. Rewrite using `[ho, he, Algebra.smul_def, Algebra.smul_def, map_mul, ← mul_assoc]`. Conclude with `mul_div_cancel_left₀ x hda`.

Use `⟨⟨o, ?_⟩, by simp only [ho']⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[ho']`. Conclude with `hx a ha`. Use `choose r hr using hrep`.

Set `ψ : {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} → Q` to `fun t => QuotientAddGroup.mk (r t)`. Establish `hψ : Function.Injective ψ`. Introduce `t t' h`. Establish `h1` using `QuotientAddGroup.eq.mp h`. Rewrite `h1` using `[AddSubgroup.mem_addSubgroupOf]`.

Establish `h2` using `hmulmem _ h1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hr t, ← hr t']`. Rewrite using `[Submodule.Quotient.eq]`. Establish `h3` using `𝔠.neg_mem h2`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `⟨Finite.of_injective ψ hψ, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_one (𝔠 : Submodule (𝓞 K) K) (hfg : 𝔠.FG) (h0 : 𝔠 ≠ ⊥)
    (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    Finite {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} ∧
      Nat.card {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 := by
  classical
  obtain ⟨d, hd, hdi⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a₀, ha₀, ha₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  obtain ⟨c₀, hc₀, hc₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  set e : 𝓞 K := d * a₀ with he
  have he0 : e ≠ 0 := mul_ne_zero hd0 ha₀0
  have heK : algebraMap (𝓞 K) K e ≠ 0 := by simpa using he0
  let J : Ideal (𝓞 K) :=
    { carrier := {o | ∀ a ∈ 𝔞, a • (algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e) ∈ 𝔠}
      add_mem' := by
        intro x y hx hy a ha
        have := 𝔠.add_mem (hx a ha) (hy a ha)
        rw [map_add, add_div, smul_add]
        exact this
      zero_mem' := by
        intro a _
        simp
      smul_mem' := by
        intro c x hx a ha
        have := 𝔠.smul_mem c (hx a ha)
        have e1 : a • (algebraMap (𝓞 K) K (c • x) / algebraMap (𝓞 K) K e) =
            c • a • (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K e) := by
          rw [smul_eq_mul]
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [e1]
        exact this }
  have hJmem : ∀ o, o ∈ J ↔ ∀ a ∈ 𝔞, a • (algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e) ∈ 𝔠 :=
    fun _ => Iff.rfl
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨o, ho⟩ := hdi c₀ hc₀
    have ho' : algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K d * c₀ := by
      rw [ho, Algebra.smul_def]
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
    have ho0 : o ≠ 0 := by
      intro h
      rw [h, map_zero] at ho'
      exact mul_ne_zero hdK hc₀0 ho'.symm
    intro hbot
    have hmem : e * o ∈ J := by
      intro a _
      have e1 : a • (algebraMap (𝓞 K) K (e * o) / algebraMap (𝓞 K) K e) = (a * d) • c₀ := by
        rw [map_mul, mul_div_cancel_left₀ _ heK, ho', Algebra.smul_def, Algebra.smul_def, map_mul]
        ring
      rw [e1]
      exact 𝔠.smul_mem _ hc₀
    rw [hbot, Ideal.mem_bot] at hmem
    exact mul_ne_zero he0 ho0 hmem
  have hmulmem : ∀ z ∈ 𝔞 * J, algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K e ∈ 𝔠 := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro a ha j hj
      have := hj a ha
      rw [Algebra.smul_def] at this
      rw [map_mul, mul_div_assoc]
      exact this
    · intro x y hx hy
      rw [map_add, add_div]
      exact 𝔠.add_mem hx hy

  have hle : (𝔞 * J) ≤ J := Ideal.mul_le_right
  have hleA : (𝔞 * J).toAddSubgroup ≤ J.toAddSubgroup := hle
  have hNJ : Ideal.absNorm J ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using hJ0
  have hN𝔞 : Ideal.absNorm 𝔞 ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using h𝔞
  have hidx : (𝔞 * J).toAddSubgroup.relIndex J.toAddSubgroup = Ideal.absNorm 𝔞 := by
    have h1 := AddSubgroup.relIndex_mul_index hleA
    have h2 : ∀ I : Ideal (𝓞 K), I.toAddSubgroup.index = Ideal.absNorm I := by
      intro I
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [h2, h2, map_mul] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) h1
  let Q := ↥J.toAddSubgroup ⧸ (𝔞 * J).toAddSubgroup.addSubgroupOf J.toAddSubgroup
  have hQfin : Finite Q := by
    apply Nat.finite_of_card_ne_zero
    have : Nat.card Q = Ideal.absNorm 𝔞 := hidx
    rw [this]
    exact hN𝔞
  have hQcard : Nat.card Q = Ideal.absNorm 𝔞 := hidx

  have hrep : ∀ t : {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0}, ∃ o : ↥J.toAddSubgroup,
      Submodule.Quotient.mk (algebraMap (𝓞 K) K o.1 / algebraMap (𝓞 K) K e) = t.1 := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    have hx : ∀ a ∈ 𝔞, a • x ∈ 𝔠 := by
      intro a ha
      have := ht a ha
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨o, ho⟩ := hdi _ (hx a₀ ha₀)
    have ho' : algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e = x := by
      have hda : algebraMap (𝓞 K) K d * algebraMap (𝓞 K) K a₀ ≠ 0 := by
        rw [← map_mul]
        exact heK
      rw [ho, he, Algebra.smul_def, Algebra.smul_def, map_mul, ← mul_assoc]
      exact mul_div_cancel_left₀ x hda
    refine ⟨⟨o, ?_⟩, by simp only [ho']⟩
    intro a ha
    rw [ho']
    exact hx a ha
  choose r hr using hrep
  let ψ : {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} → Q := fun t => QuotientAddGroup.mk (r t)
  have hψ : Function.Injective ψ := by
    intro t t' h
    have h1 := QuotientAddGroup.eq.mp h
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    have h2 := hmulmem _ h1
    apply Subtype.ext
    rw [← hr t, ← hr t']
    rw [Submodule.Quotient.eq]
    have h3 := 𝔠.neg_mem h2
    convert h3 using 1
    simp
    ring
  refine ⟨Finite.of_injective ψ hψ, ?_⟩
  calc _ ≤ Nat.card Q := Nat.card_le_card_of_injective ψ hψ
    _ = _ := hQcard

def ins (K : Type) [Field K] [NumberField K] (m : ℕ) :
    (Fin m → K) →ₗ[𝓞 K] (Fin (m + 1) → K) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def hd (K : Type) [Field K] [NumberField K] (m : ℕ) : (Fin (m + 1) → K) →ₗ[𝓞 K] K :=
  LinearMap.proj 0

/- English proof (translation)
Introduce `x y h`. Use extensionality with `j`. Conclude with `congrFun h j.succ`.
-/
theorem ins_injective (m : ℕ) : Function.Injective (ins K m) := by
  intro x y h
  ext j
  exact congrFun h j.succ

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.1`. Establish `h1 : (L.comap (ins K m)).map (ins K m) ≤ L` using `Submodule.map_comap_le _ _`. Conclude with `Submodule.fg_of_fg_map_injective _ (ins_injective m) (isNoetherian_submodule.mp this _ h1)`. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Take `⟨t, ht, htv⟩` from `exists_smul_mem hL (ins K m v)`. Establish `hmem : t • v ∈ L.comap (ins K m)`. Rewrite using `[Submodule.mem_comap, map_smul]`. Conclude with `htv`.

Establish `htK : algebraMap (𝓞 K) K t ≠ 0` using `by simpa using ht`. Establish `e : v = (algebraMap (𝓞 K) K t)⁻¹ • (t • v)`. Use extensionality with `i`. Express the relevant statement in the definitionally equal form `v i = (algebraMap (𝓞 K) K t)⁻¹ * (t • v i)`. Rewrite using `[Algebra.smul_def]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem isLat_comap_ins {m : ℕ} {L : Submodule (𝓞 K) (Fin (m + 1) → K)} (hL : IsLat L) :
    IsLat (L.comap (ins K m)) := by
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.1
    have h1 : (L.comap (ins K m)).map (ins K m) ≤ L := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective _ (ins_injective m) (isNoetherian_submodule.mp this _ h1)
  · rw [eq_top_iff]
    intro v _
    obtain ⟨t, ht, htv⟩ := exists_smul_mem hL (ins K m v)
    have hmem : t • v ∈ L.comap (ins K m) := by
      rw [Submodule.mem_comap, map_smul]
      exact htv
    have htK : algebraMap (𝓞 K) K t ≠ 0 := by simpa using ht
    have e : v = (algebraMap (𝓞 K) K t)⁻¹ • (t • v) := by
      ext i
      change v i = (algebraMap (𝓞 K) K t)⁻¹ * (t • v i)
      rw [Algebra.smul_def]
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Take `⟨t, ht, htv⟩` from `exists_smul_mem hL (Pi.single 0 1)`. Introduce `h`. Establish `h1 : hd K m (t • Pi.single 0 1) ∈ L.map (hd K m)` using `Submodule.mem_map_of_mem htv`. Rewrite `h1` using `[h, Submodule.mem_bot]`. Establish `h2 : algebraMap (𝓞 K) K t = 0`.

Establish `h3 : hd K m (t • Pi.single 0 1) = t • (1 : K)`. Simplify using `[hd]`. Rewrite `h1` using `[h3, Algebra.smul_def, mul_one]`. Conclude with `h1`. Conclude with `ht (by simpa using h2)`.
-/
theorem map_hd_ne_bot {m : ℕ} {L : Submodule (𝓞 K) (Fin (m + 1) → K)} (hL : IsLat L) :
    L.map (hd K m) ≠ ⊥ := by
  obtain ⟨t, ht, htv⟩ := exists_smul_mem hL (Pi.single 0 1)
  intro h
  have h1 : hd K m (t • Pi.single 0 1) ∈ L.map (hd K m) := Submodule.mem_map_of_mem htv
  rw [h, Submodule.mem_bot] at h1
  have h2 : algebraMap (𝓞 K) K t = 0 := by
    have h3 : hd K m (t • Pi.single 0 1) = t • (1 : K) := by
      simp [hd]
    rw [h3, Algebra.smul_def, mul_one] at h1
    exact h1
  exact ht (by simpa using h2)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `L _`. Establish `hs : Subsingleton {x : (Fin 0 → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0}`. Use `⟨fun x y => Subtype.ext ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ x.1`. Take `⟨b, hb⟩` from `Submodule.Quotient.mk_surjective _ y.1`. Rewrite using `[← ha, ← hb, Subsingleton.elim a b]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Simplify using `using Finite.card_le_one_iff_subsingleton.mpr hs`.

Consider the case `succ m ih`. Introduce `L hL`. Take `⟨fA, cA⟩` from `ih _ (isLat_comap_ins hL)`. Take `⟨fC, cC⟩` from `rank_one (L.map (hd K m)) (hL.1.map _) (map_hd_ne_bot hL) 𝔞 h𝔞`. Set `f` to `(L.comap (ins K m)).mapQ L (ins K m) le_rfl`.

Set `g` to `L.mapQ (L.map (hd K m)) (hd K m) (Submodule.le_comap_map _ _)`. Establish `hf : Function.Injective f`. Use `(injective_iff_map_eq_zero f).2 ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Establish `h1 : Submodule.Quotient.mk (p` using `L) (ins K m a) = 0 := hx`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Establish `hfg : ∀ b, g b = 0 → ∃ a, f a = b`. Introduce `b hb`.

Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Establish `h1 : Submodule.Quotient.mk (p` using `L.map (hd K m)) (hd K m b) = 0 := hb`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨l, hl, hle⟩` from `Submodule.mem_map.mp h1`. Use `⟨Submodule.Quotient.mk (Fin.tail (b - l)), ?_⟩` and prove the remaining obligations.

Establish `h2 : ins K m (Fin.tail (b - l)) = b - l`. Use extensionality with `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Establish `h3 : l 0 = b 0` using `hle`. Simplify using `[ins, h3]`.

Simplify using `[ins, Fin.tail]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (p := L) (ins K m (Fin.tail (b - l))) = _`. Rewrite using `[h2, Submodule.Quotient.eq]`. Use `L.neg_mem hl` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Take `⟨fB, cB⟩` from `torsion_exact_bound 𝔞 f g hf hfg`. Use `⟨fB, cB.trans ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Nat.mul_le_mul cA cC`.
-/
theorem torsion_card_le_by_rank (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (m : ℕ) :
    ∀ L : Submodule (𝓞 K) (Fin m → K), IsLat L →
      Finite {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ∧
        Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 ^ m := by
  induction m with
  | zero =>
    intro L _
    have hs : Subsingleton {x : (Fin 0 → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ x.1
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ y.1
      rw [← ha, ← hb, Subsingleton.elim a b]
    refine ⟨inferInstance, ?_⟩
    simpa using Finite.card_le_one_iff_subsingleton.mpr hs
  | succ m ih =>
    intro L hL
    obtain ⟨fA, cA⟩ := ih _ (isLat_comap_ins hL)
    obtain ⟨fC, cC⟩ := rank_one (L.map (hd K m)) (hL.1.map _) (map_hd_ne_bot hL) 𝔞 h𝔞
    let f := (L.comap (ins K m)).mapQ L (ins K m) le_rfl
    let g := L.mapQ (L.map (hd K m)) (hd K m) (Submodule.le_comap_map _ _)
    have hf : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).2 ?_
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      have h1 : Submodule.Quotient.mk (p := L) (ins K m a) = 0 := hx
      rwa [Submodule.Quotient.mk_eq_zero] at h1
    have hfg : ∀ b, g b = 0 → ∃ a, f a = b := by
      intro b hb
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have h1 : Submodule.Quotient.mk (p := L.map (hd K m)) (hd K m b) = 0 := hb
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨l, hl, hle⟩ := Submodule.mem_map.mp h1
      refine ⟨Submodule.Quotient.mk (Fin.tail (b - l)), ?_⟩
      have h2 : ins K m (Fin.tail (b - l)) = b - l := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have h3 : l 0 = b 0 := hle
          simp [ins, h3]
        · simp [ins, Fin.tail]
      change Submodule.Quotient.mk (p := L) (ins K m (Fin.tail (b - l))) = _
      rw [h2, Submodule.Quotient.eq]
      have := L.neg_mem hl
      convert this using 1
      abel
    obtain ⟨fB, cB⟩ := torsion_exact_bound 𝔞 f g hf hfg
    refine ⟨fB, cB.trans ?_⟩
    rw [pow_succ]
    exact Nat.mul_le_mul cA cC

/- English proof (translation)
Introduce `_ _ _ m L hL 𝔞 h𝔞` and use `torsion_card_le_by_rank 𝔞 h𝔞 m L hL`.
-/
theorem tor_card : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ →
      Finite {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ∧
        Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 ^ m :=
  fun _ _ _ m L hL 𝔞 h𝔞 => torsion_card_le_by_rank 𝔞 h𝔞 m L hL

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard
