import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

/- English proof (translation)
Introduce `Q _ g r N e b T hN he _hs hb hT hcard`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `e0 : e 0 = 1`. Establish `h` using `he 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_left_cancel (a := e 0) (h.symm.trans (_root_.mul_one _).symm)`. Establish `esub : ∀ v w, e (v - w) = e v * (e w)⁻¹`. Introduce `v w`. Establish `h` using `he (v - w) w`. Rewrite `h` using `[sub_add_cancel]`.

Conclude with `eq_mul_inv_of_mul_eq h.symm`. Establish `ensmul : ∀ (n : ℕ) v, e (n • v) = e v ^ n`. Introduce `n v`. Proceed by induction on `n with`. Consider the case `zero => simp [e0]`.

Consider the case `succ n ih => rw [succ_nsmul, he, ih, pow_succ]`. Use `set ψ : (Fin r → ℤ) → Q := fun a => e ((N : ℂ)⁻¹ • ∑ j, a j • b j) with hψ`. Establish `hdiff : ∀ a a' : Fin r → ℤ, (N : ℂ)⁻¹ • ∑ j, a j • b j - (N : ℂ)⁻¹ • ∑ j, a' j • b j = (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j`. Introduce `a a'`. Rewrite using `[← smul_sub, ← Finset.sum_sub_distrib]`.

Simplify using `[sub_smul]`. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hdvd : ∀ (c m : Fin r → ℤ), (N : ℂ)⁻¹ • ∑ j, c j • b j = ∑ j, m j • b j → ∀ j, c j = N * m j`. Introduce `c m h`. Establish `h2 : ∑ j, c j • b j = (N : ℂ) • ∑ j, m j • b j`.

Rewrite using `[← h, smul_smul, mul_inv_cancel₀ hN0, one_smul]`. Establish `h3 : ∑ j, ((c j : ℝ) - (N : ℝ) * (m j : ℝ)) • b j = 0`. Simplify using `only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, Int.cast_smul_eq_zsmul]`. Rewrite using `[h2, Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℝ, sub_self]`. Establish `h4` using `Fintype.linearIndependent_iff.1 hb.1 _ h3`.

Introduce `j`. Use `h4 j` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`. Conclude with `this` after adjusting the coercions. Establish `key : ∀ a a' : Fin r → ℤ, ψ a = ψ a' ↔ ∀ j, (a j : ZMod N) = a' j`.

Introduce `a a'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : e ((N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j) = 1`. Rewrite using `[← hdiff, esub]`.

Conclude with `mul_inv_eq_one.2 h`. Take `⟨m, hm⟩` from `(hb.2 _).1 h1`. Use `hdvd (fun j => a j - a' j) m hm` as an intermediate fact. Introduce `j`. Rewrite using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`.

Conclude with `⟨-m j, by have := this j; push_cast at this ⊢; linarith⟩`. Introduce `h`. Establish `hk : ∀ j, ∃ k : ℤ, a j - a' j = N * k` using `fun j => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h j).symm |>.imp fun k hk => by linarith`. Use `choose k hk using hk`. Establish `h1 : e (∑ j, k j • b j) = 1` using `(hb.2 _).2 ⟨k, rfl⟩`.

Establish `h2 : (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j = ∑ j, k j • b j`. Repeatedly rewrite using `[hk, mul_smul, ← Finset.smul_sum]`. Rewrite using `[Nat.cast_smul_eq_nsmul ℤ]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]`. Establish `h3` using `hdiff a a'`.

Rewrite `h3` using `[h2]`. Establish `h4 : (N : ℂ)⁻¹ • ∑ j, a j • b j = (N : ℂ)⁻¹ • ∑ j, a' j • b j + ∑ j, k j • b j`. Rewrite using `[← h3]`. Normalize the expressions using the abelian group laws. Simplify using `only [hψ, h4, he, h1, _root_.mul_one]`.

Establish `hpow : ∀ a, ψ a ^ N = 1`. Introduce `a`. Use `show e _ ^ N = 1`. Rewrite using `[← ensmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]`. Conclude with `(hb.2 _).2 ⟨a, rfl⟩`.

Establish `hsurj : ∀ p : Q, p ^ N = 1 → ∃ a, ψ a = p`. Introduce `p hp`. Take `⟨u, rfl⟩` from `_hs p`. Establish `h1 : e (N • u) = 1` using `by rw [ensmul, hp]`. Take `⟨m, hm⟩` from `(hb.2 _).1 h1`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Use `show e _ = e u`. Rewrite using `[← hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]`. Set `F : (Fin r → ZMod N) → Q` to `fun s => ψ (fun j => ((s j).val : ℤ))`. Establish `hFval : ∀ a : Fin r → ℤ, F (fun j => (a j : ZMod N)) = ψ a`.

Introduce `a`. Conclude with `(key _ _).2 fun j => by simp`. Establish `hFinj : Function.Injective F`. Introduce `s s' h`. Use function extensionality and compare the values at `j`.

Establish `h1` using `(key _ _).1 h j`. Simplify using `using h1`. Establish `hR : Nat.card {p : Q // p ^ N = 1} = N ^ r`. Establish `hbij : Function.Bijective (fun s => (⟨F s, hpow _⟩ : {p : Q // p ^ N = 1}))`. Use `⟨fun s s' h => hFinj (congrArg Subtype.val h), fun p => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `hsurj p.1 p.2`. Conclude with `⟨fun j => (a j : ZMod N), Subtype.ext (by show F _ = _; rw [hFval, ha])⟩`. Rewrite using `[← Nat.card_eq_of_bijective _ hbij]`. Simplify using `[Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]`. Use `⟨{s | F s ∈ T}, ?_, ?_⟩` and prove the remaining obligations.

Establish `hS : Nat.card {s | F s ∈ T} = Nat.card T`. Establish `hbij : Function.Bijective (fun s : {s | F s ∈ T} => (⟨F s.1, s.2⟩ : T))`. Use `⟨fun s s' h => Subtype.ext (hFinj (congrArg Subtype.val h)), fun τ => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hsurj τ.1 (hT _ τ.2)`. Use `⟨⟨fun j => (a j : ZMod N), ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show F _ ∈ T`. Rewrite using `[hFval, ha]`. Conclude with `τ.2`. Use `show F _ = _`. Rewrite using `[hFval, ha]`.

Conclude with `Nat.card_eq_of_bijective _ hbij`. Rewrite using `[hS, ← hR, hcard]`. Introduce `a ha show ψ a ∈ T`. Rewrite using `[← hFval]`. Conclude with `ha`.
-/
theorem exp_lattice_torsion_count : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  intro Q _ g r N e b T hN he _hs hb hT hcard
  haveI : NeZero N := ⟨hN.ne'⟩
  have e0 : e 0 = 1 := by
    have h := he 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := e 0) (h.symm.trans (_root_.mul_one _).symm)
  have esub : ∀ v w, e (v - w) = e v * (e w)⁻¹ := by
    intro v w
    have h := he (v - w) w
    rw [sub_add_cancel] at h
    exact eq_mul_inv_of_mul_eq h.symm
  have ensmul : ∀ (n : ℕ) v, e (n • v) = e v ^ n := by
    intro n v
    induction n with
    | zero => simp [e0]
    | succ n ih => rw [succ_nsmul, he, ih, pow_succ]
  set ψ : (Fin r → ℤ) → Q := fun a => e ((N : ℂ)⁻¹ • ∑ j, a j • b j) with hψ
  have hdiff : ∀ a a' : Fin r → ℤ, (N : ℂ)⁻¹ • ∑ j, a j • b j - (N : ℂ)⁻¹ • ∑ j, a' j • b j
      = (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j := by
    intro a a'
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    simp [sub_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hdvd : ∀ (c m : Fin r → ℤ), (N : ℂ)⁻¹ • ∑ j, c j • b j = ∑ j, m j • b j → ∀ j, c j = N * m j := by
    intro c m h
    have h2 : ∑ j, c j • b j = (N : ℂ) • ∑ j, m j • b j := by
      rw [← h, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    have h3 : ∑ j, ((c j : ℝ) - (N : ℝ) * (m j : ℝ)) • b j = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, Int.cast_smul_eq_zsmul]
      rw [h2, Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℝ, sub_self]
    have h4 := Fintype.linearIndependent_iff.1 hb.1 _ h3
    intro j
    have := h4 j
    rw [sub_eq_zero] at this
    exact_mod_cast this
  have key : ∀ a a' : Fin r → ℤ, ψ a = ψ a' ↔ ∀ j, (a j : ZMod N) = a' j := by
    intro a a'
    constructor
    · intro h
      have h1 : e ((N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j) = 1 := by
        rw [← hdiff, esub]
        exact mul_inv_eq_one.2 h
      obtain ⟨m, hm⟩ := (hb.2 _).1 h1
      have := hdvd (fun j => a j - a' j) m hm
      intro j
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-m j, by have := this j; push_cast at this ⊢; linarith⟩
    · intro h
      have hk : ∀ j, ∃ k : ℤ, a j - a' j = N * k := fun j =>
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h j).symm |>.imp fun k hk => by linarith
      choose k hk using hk
      have h1 : e (∑ j, k j • b j) = 1 := (hb.2 _).2 ⟨k, rfl⟩
      have h2 : (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j = ∑ j, k j • b j := by
        simp_rw [hk, mul_smul, ← Finset.smul_sum]
        rw [Nat.cast_smul_eq_nsmul ℤ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      have h3 := hdiff a a'
      rw [h2] at h3
      have h4 : (N : ℂ)⁻¹ • ∑ j, a j • b j = (N : ℂ)⁻¹ • ∑ j, a' j • b j + ∑ j, k j • b j := by
        rw [← h3]; abel
      simp only [hψ, h4, he, h1, _root_.mul_one]
  have hpow : ∀ a, ψ a ^ N = 1 := by
    intro a
    show e _ ^ N = 1
    rw [← ensmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (hb.2 _).2 ⟨a, rfl⟩
  have hsurj : ∀ p : Q, p ^ N = 1 → ∃ a, ψ a = p := by
    intro p hp
    obtain ⟨u, rfl⟩ := _hs p
    have h1 : e (N • u) = 1 := by rw [ensmul, hp]
    obtain ⟨m, hm⟩ := (hb.2 _).1 h1
    refine ⟨m, ?_⟩
    show e _ = e u
    rw [← hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let F : (Fin r → ZMod N) → Q := fun s => ψ (fun j => ((s j).val : ℤ))
  have hFval : ∀ a : Fin r → ℤ, F (fun j => (a j : ZMod N)) = ψ a := by
    intro a
    exact (key _ _).2 fun j => by simp
  have hFinj : Function.Injective F := by
    intro s s' h
    funext j
    have h1 := (key _ _).1 h j
    simpa using h1
  have hR : Nat.card {p : Q // p ^ N = 1} = N ^ r := by
    have hbij : Function.Bijective (fun s => (⟨F s, hpow _⟩ : {p : Q // p ^ N = 1})) := by
      refine ⟨fun s s' h => hFinj (congrArg Subtype.val h), fun p => ?_⟩
      obtain ⟨a, ha⟩ := hsurj p.1 p.2
      exact ⟨fun j => (a j : ZMod N), Subtype.ext (by show F _ = _; rw [hFval, ha])⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  refine ⟨{s | F s ∈ T}, ?_, ?_⟩
  · have hS : Nat.card {s | F s ∈ T} = Nat.card T := by
      have hbij : Function.Bijective (fun s : {s | F s ∈ T} => (⟨F s.1, s.2⟩ : T)) := by
        refine ⟨fun s s' h => Subtype.ext (hFinj (congrArg Subtype.val h)), fun τ => ?_⟩
        obtain ⟨a, ha⟩ := hsurj τ.1 (hT _ τ.2)
        refine ⟨⟨fun j => (a j : ZMod N), ?_⟩, Subtype.ext ?_⟩
        · show F _ ∈ T
          rw [hFval, ha]
          exact τ.2
        · show F _ = _
          rw [hFval, ha]
      exact Nat.card_eq_of_bijective _ hbij
    rw [hS, ← hR, hcard]
  · intro a ha
    show ψ a ∈ T
    rw [← hFval]
    exact ha

end GlobalTheory.ShFam.Hor.LogCh
