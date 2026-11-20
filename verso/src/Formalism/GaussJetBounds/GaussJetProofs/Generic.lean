import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementM
import Formalism.GaussJetBounds.GaussJetProofs.FrameA
import Formalism.GaussJetBounds.GaussJetProofs.Special

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
Establish `hprod : ∀ σ : Equiv.Perm (Fin n), (∏ i, (Matrix.of fun (r c : Fin n) => (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)) (σ i) i) = MvPolynomial.monomial (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) 1`. Introduce `σ`. Rewrite using `[MvPolynomial.monomial_sum_one]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `[MvPolynomial.X_pow_eq_monomial]`.

Establish `hval : ∀ (f : Fin n → ZMod d) (g : Fin n → ℕ) (i : Fin n), (∑ j, Finsupp.single (f j, z, γ j) (g j)) (f i, z, γ i) = g i`. Introduce `f g i`. Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)`. Simplify using the standard rewrite rules. Establish `hval2 : ∀ (i : Fin n) (u : ZMod d), (∑ j, Finsupp.single (t j, z, γ j) (L j)) (u, z, γ i) = if t i = u then L i else 0`.

Introduce `i u`. Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single i]`. Rewrite using `[Finsupp.single_apply]`. Distinguish the cases in `h : t i = u`. Simplify using `[h]`.

Rewrite using `[if_neg, if_neg h]`. Introduce `h'`. Conclude with `h (Prod.ext_iff.mp h').1`. Introduce `j _ hj`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)`. Simplify using the standard rewrite rules. Establish `key : ∀ σ : Equiv.Perm (Fin n), (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) = ∑ i, Finsupp.single (t i, z, γ i) (L i) → σ = 1`. Introduce `σ h`.

Use extensionality with `i`. Establish `h1 : (∑ j, Finsupp.single (t (σ j), z, γ j) (L (σ j))) (t (σ i), z, γ i) = (∑ j, Finsupp.single (t j, z, γ j) (L j)) (t (σ i), z, γ i)` using `by rw [h]`. Rewrite `h1` using `[hval (fun j => t (σ j)) (fun j => L (σ j)) i, hval2]`. Distinguish the cases in `ht : t i = t (σ i)`. Rewrite `h1` using `[if_pos ht]`.

Establish `: σ i = i` using `hinj (Prod.ext ht.symm h1)`. Simplify using `[this]`. Rewrite `h1` using `[if_neg ht]`. Conclude with `absurd h1 (hL (σ i))`. Introduce `hdet`.

Establish `hc` using `congrArg (MvPolynomial.coeff (∑ i, Finsupp.single (t i, z, γ i) (L i))) hdet`. Rewrite `hc` using `[Matrix.det_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Rewrite `hc` using `[hprod]`. Simplify using `at hc`. Introduce `σ _ hσ`.

Rewrite using `[hprod, Units.smul_def, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_neg]`. Simplify using the standard rewrite rules. Conclude with `fun h => hσ (key σ h)`. Simplify using the standard rewrite rules.
-/
theorem generic_mono_det {R : Type*} [CommRing R] [Nontrivial R] {d N0 n : ℕ} (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (γ : Fin n → Fin N0) (hγ : Function.Injective γ)
    (hL : ∀ i, L i ≠ 0) (hinj : Function.Injective fun i => (t i, L i)) :
    (Matrix.of fun (r c : Fin n) =>
      (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)).det ≠ 0 := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, (Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)) (σ i) i)
        = MvPolynomial.monomial (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) 1 := by
    intro σ
    rw [MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [MvPolynomial.X_pow_eq_monomial]
  have hval : ∀ (f : Fin n → ZMod d) (g : Fin n → ℕ) (i : Fin n),
      (∑ j, Finsupp.single (f j, z, γ j) (g j)) (f i, z, γ i) = g i := by
    intro f g i
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have hval2 : ∀ (i : Fin n) (u : ZMod d),
      (∑ j, Finsupp.single (t j, z, γ j) (L j)) (u, z, γ i) = if t i = u then L i else 0 := by
    intro i u
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · rw [Finsupp.single_apply]
      by_cases h : t i = u
      · simp [h]
      · rw [if_neg, if_neg h]
        intro h'
        exact h (Prod.ext_iff.mp h').1
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have key : ∀ σ : Equiv.Perm (Fin n),
      (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) = ∑ i, Finsupp.single (t i, z, γ i) (L i) → σ = 1 := by
    intro σ h
    ext i
    have h1 : (∑ j, Finsupp.single (t (σ j), z, γ j) (L (σ j))) (t (σ i), z, γ i)
        = (∑ j, Finsupp.single (t j, z, γ j) (L j)) (t (σ i), z, γ i) := by rw [h]
    rw [hval (fun j => t (σ j)) (fun j => L (σ j)) i, hval2] at h1
    by_cases ht : t i = t (σ i)
    · rw [if_pos ht] at h1
      have : σ i = i := hinj (Prod.ext ht.symm h1)
      simp [this]
    · rw [if_neg ht] at h1
      exact absurd h1 (hL (σ i))
  intro hdet
  have hc := congrArg (MvPolynomial.coeff (∑ i, Finsupp.single (t i, z, γ i) (L i))) hdet
  rw [Matrix.det_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))] at hc
  · rw [hprod] at hc
    simp at hc
  · intro σ _ hσ
    rw [hprod, Units.smul_def, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_neg]
    · simp
    · exact fun h => hσ (key σ h)
  · simp

/- English proof (translation)
Use `haveI : Fact (1 < l) := ⟨hl.one_lt⟩`. Use `set P : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℤ := (Matrix.of fun (i i' : Fin n) => ∑ a, MvPolynomial.X (t i, z, a) ^ (L i) * MvPolynomial.X (s, e i', a)).det with hP`. Establish `hev : MvPolynomial.aeval Y P = (Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det`. Rewrite using `[hP, AlgHom.map_det]`. Use `congr 1`.

Use extensionality with `i i'`. Simplify using the standard rewrite rules. Rewrite using `[← hev]`. Use `hY P ?_` and prove the remaining obligations. Introduce `h0`.

Establish `hmap : MvPolynomial.map (Int.castRingHom (ZMod l)) P = (Matrix.of fun (i i' : Fin n) => ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i) * MvPolynomial.X (s, e i', a)).det`. Rewrite using `[hP, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i i'`. Simplify using the standard rewrite rules.

Rewrite `h0` using `[hmap]`. Set `f : ZMod d × Fin N0 × Fin N0 → MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)` to `fun v => if v.1 = s then (if v.2.1 = v.2.2 then 1 else 0) else MvPolynomial.X v`. Establish `h1` using `congrArg (MvPolynomial.bind₁ f) h0`. Rewrite `h1` using `[map_zero, AlgHom.map_det]`. Establish `h2 : (MvPolynomial.bind₁ f).mapMatrix (Matrix.of fun (i i' : Fin n) => ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i) * MvPolynomial.X (s, e i', a)) = Matrix.of fun (r c : Fin n) => (MvPolynomial.X (t r, z, e c) : MvPolynomial (ZMod d …`.

Use extensionality with `i i'`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_pow, MvPolynomial.bind₁_X_right, f, if_neg (hts i), if_true]`. Rewrite using `[Finset.sum_eq_single (e i')]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg (Ne.symm hb), mul_zero]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`. Conclude with `generic_mono_det z t L e he hL hinj h1`.
-/
theorem generic_minor_norm {K : Type u} [NormedField K] {l d N0 n : ℕ} (hl : l.Prime)
    (Y : ZMod d × Fin N0 × Fin N0 → K) (hY : IsGeneric l Y) (s : ZMod d) (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (e : Fin n → Fin N0) (he : Function.Injective e)
    (hn : n ≤ N0) (hts : ∀ i, t i ≠ s) (hL : ∀ i, L i ≠ 0)
    (hinj : Function.Injective fun i => (t i, L i)) :
    ‖(Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det‖ = 1 := by
  classical
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  set P : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℤ := (Matrix.of fun (i i' : Fin n) =>
    ∑ a, MvPolynomial.X (t i, z, a) ^ (L i) * MvPolynomial.X (s, e i', a)).det with hP
  have hev : MvPolynomial.aeval Y P
      = (Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det := by
    rw [hP, AlgHom.map_det]
    congr 1
    ext i i'
    simp
  rw [← hev]
  refine hY P ?_
  intro h0
  have hmap : MvPolynomial.map (Int.castRingHom (ZMod l)) P = (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a)).det := by
    rw [hP, RingHom.map_det]
    congr 1
    ext i i'
    simp
  rw [hmap] at h0
  let f : ZMod d × Fin N0 × Fin N0 → MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l) :=
    fun v => if v.1 = s then (if v.2.1 = v.2.2 then 1 else 0) else MvPolynomial.X v
  have h1 := congrArg (MvPolynomial.bind₁ f) h0
  rw [map_zero, AlgHom.map_det] at h1
  have h2 : (MvPolynomial.bind₁ f).mapMatrix (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a))
      = Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, e c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L r) := by
    ext i i'
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_pow,
      MvPolynomial.bind₁_X_right, f, if_neg (hts i), if_true]
    rw [Finset.sum_eq_single (e i')]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · simp
  rw [h2] at h1
  exact generic_mono_det z t L e he hL hinj h1

/- English proof (translation)
Use `haveI : Fact (1 < l) := ⟨hl.one_lt⟩`. Establish `h` using `hY (MvPolynomial.X y) (by`. Rewrite using `[MvPolynomial.map_X]`. Conclude with `MvPolynomial.X_ne_zero y)`. Simplify using `using h`.
-/
theorem generic_norm_one {K : Type u} [NormedField K] {σ : Type} {l : ℕ} (hl : l.Prime)
    (Y : σ → K) (hY : IsGeneric l Y) (y : σ) : ‖Y y‖ = 1 := by
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  have h := hY (MvPolynomial.X y) (by
    rw [MvPolynomial.map_X]
    exact MvPolynomial.X_ne_zero y)
  simpa using h

/- English proof (translation)
Introduce `K _ _ _ l d N0 N1 _ hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I Y hY nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab hJ m hm`. Establish `hYn : ∀ y, ‖Y y‖ = 1` using `generic_norm_one hl Y hY`. Establish `hxg : ∀ y, ‖genFrame TT l m Y y‖ ≤ 1`. Introduce `y`. Simplify using `only [genFrame]`.

Apply the tactic sequence `split_ifs <;> simp [norm_pow, hYn]`. Establish `hw : ∀ s (i : Fin (J s)), (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧ s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d)`. Introduce `s i`. Use `(hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩` as an intermediate fact. Conclude with `⟨this.1, this.2.1, this.2.2.1⟩`.

Establish `hxg0 : ∀ s0 ∈ TT, ∀ a, genFrame TT l m Y (s0, ⟨0, h0⟩, a) = Y (s0, ⟨0, h0⟩, a) ^ l ^ m`. Introduce `s0 hs0 a`. Simplify using `[genFrame, hs0]`. Set `E : (s : ZMod d) → Fin (J s) → ℕ` to `fun s i => ((m : ℤ) + (lab s i).2).toNat`. Set `lam : (s : ZMod d) → Fin (J s) → Fin N0 → K` to `fun s i a => Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ E s i`.

Establish `hlam1 : ∀ s i a, ‖lam s i a‖ ≤ 1`. Introduce `s i a`. Simplify using `[lam, norm_pow, hYn]`. Establish `hpos : ∀ s i a, 0 < (lab s i).2 → lam s i a = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ (lab s i).2.toNat`. Introduce `s i a hj`.

Rewrite using `[hxg0 _ (hw s i).1, ← pow_mul, ← pow_add]`. Simplify using `only [lam, E]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `hneg : ∀ s i a, (lab s i).2 < 0 → lam s i a ^ l ^ (-(lab s i).2).toNat = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a)`.

Introduce `s i a hj`. Establish `hmm` using `hm s i`. Rewrite using `[hxg0 _ (hw s i).1]`. Simplify using `only [lam, E]`. Rewrite using `[← pow_mul, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Set `e : (s : ZMod d) → Fin (J s) → Fin N0` to `fun s i => ⟨i + (if s ∈ TT then 1 else 0), by`. Establish `h` using `hJ s`. Establish `hi` using `i.isLt`.

Apply the tactic sequence `split_ifs at h ⊢ <;> omega⟩`. Establish `he_inj : ∀ s, Function.Injective (e s)`. Introduce `s i i' h`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Fin.val h`.

Simplify using `only [e] at h'`. Use linear arithmetic over natural numbers and integers. Establish `he0 : ∀ s i, ¬(s ∈ TT ∧ ((e s i : Fin N0) : ℕ) = 0)`. Introduce `s i h`. Take `⟨hs, hz0⟩` from `h`.

Simplify using `[e, hs] at hz0`. Establish `hdet : ∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) => ∑ a : Fin N0, lam s i a * genFrame TT l m Y (s, e s i', a)).det‖ = 1`. Introduce `s`. Establish `hx : ∀ i' a, genFrame TT l m Y (s, e s i', a) = Y (s, e s i', a)`. Introduce `i' a`.

Simplify using `only [genFrame]`. Rewrite using `[if_neg (he0 s i')]`. Simplify using `only [hx]`. Establish `hts : ∀ i, (lab s i).1 ≠ s`. Introduce `i h`.

Take `⟨_, hodd, hss⟩` from `hw s i`. Rewrite `hss` using `[h]`. Establish `hx0 : (((lab s i).2 : ℤ) : ZMod d) = 0` using `by simpa using hss`. Establish `hdvd` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0`. Establish `hev : Even ((d : ℕ) : ℤ)` using `(Int.even_coe_nat d).mpr he`.

Take `⟨k, hk⟩` from `hdvd`. Establish `: Even (lab s i).2`. Rewrite using `[hk]`. Conclude with `hev.mul_right k`. Conclude with `(Int.not_even_iff_odd.mpr hodd) this`.

Establish `hLn : ∀ i, l ^ E s i ≠ 0` using `fun i => pow_ne_zero _ hl.ne_zero`. Establish `hinj' : Function.Injective fun i => ((lab s i).1, l ^ E s i)`. Introduce `i i' h`. Simplify using `only [Prod.mk.injEq] at h`. Take `⟨ha1, ha2⟩` from `h`.

Establish `hE` using `Nat.pow_right_injective hl.two_le ha2`. Simplify using `only [E] at hE`. Establish `hm1` using `hm s i`. Establish `hm2` using `hm s i'`. Establish `ho1` using `(hw s i).2.1`.

Establish `ho2` using `(hw s i').2.1`. Establish `hn1 : (lab s i).2 ≠ 0` using `fun h => by rw [h] at ho1; exact absurd ho1 (by decide)`. Establish `hn2 : (lab s i').2 ≠ 0` using `fun h => by rw [h] at ho2; exact absurd ho2 (by decide)`. Establish `hj : (lab s i).2 = (lab s i').2` using `by omega`. Conclude with `hinj s (Prod.ext ha1 hj)`.

Establish `hn : J s ≤ N0`. Establish `h` using `hJ s`. Apply the tactic sequence `split_ifs at h <;> omega`. Conclude with `generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (fun i => l ^ E s i) (e s) (he_inj s) hn hts hLn hinj'`. Conclude with `theorem_A_frame K l d N0 N1 hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I (genFrame TT l m Y) hxg nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab lam hlam1 hpos hneg e he_inj he0 hdet`.
-/
theorem theorem_A_generic : ThmAGeneric.{u} := by
  intro K _ _ _ l d N0 N1 _ hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I Y hY nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab hJ m hm
  classical
  have hYn : ∀ y, ‖Y y‖ = 1 := generic_norm_one hl Y hY
  have hxg : ∀ y, ‖genFrame TT l m Y y‖ ≤ 1 := by
    intro y
    simp only [genFrame]
    split_ifs <;> simp [norm_pow, hYn]
  have hw : ∀ s (i : Fin (J s)), (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧
      s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d) := by
    intro s i
    have := (hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hxg0 : ∀ s0 ∈ TT, ∀ a, genFrame TT l m Y (s0, ⟨0, h0⟩, a) = Y (s0, ⟨0, h0⟩, a) ^ l ^ m := by
    intro s0 hs0 a
    simp [genFrame, hs0]
  let E : (s : ZMod d) → Fin (J s) → ℕ := fun s i => ((m : ℤ) + (lab s i).2).toNat
  let lam : (s : ZMod d) → Fin (J s) → Fin N0 → K := fun s i a => Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ E s i
  have hlam1 : ∀ s i a, ‖lam s i a‖ ≤ 1 := by
    intro s i a
    simp [lam, norm_pow, hYn]
  have hpos : ∀ s i a, 0 < (lab s i).2 →
      lam s i a = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ (lab s i).2.toNat := by
    intro s i a hj
    rw [hxg0 _ (hw s i).1, ← pow_mul, ← pow_add]
    simp only [lam, E]
    congr 2
    omega
  have hneg : ∀ s i a, (lab s i).2 < 0 →
      lam s i a ^ l ^ (-(lab s i).2).toNat = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) := by
    intro s i a hj
    have hmm := hm s i
    rw [hxg0 _ (hw s i).1]
    simp only [lam, E]
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  let e : (s : ZMod d) → Fin (J s) → Fin N0 := fun s i =>
    ⟨i + (if s ∈ TT then 1 else 0), by
      have h := hJ s
      have hi := i.isLt
      split_ifs at h ⊢ <;> omega⟩
  have he_inj : ∀ s, Function.Injective (e s) := by
    intro s i i' h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [e] at h'
    omega
  have he0 : ∀ s i, ¬(s ∈ TT ∧ ((e s i : Fin N0) : ℕ) = 0) := by
    intro s i h
    obtain ⟨hs, hz0⟩ := h
    simp [e, hs] at hz0
  have hdet : ∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) =>
      ∑ a : Fin N0, lam s i a * genFrame TT l m Y (s, e s i', a)).det‖ = 1 := by
    intro s
    have hx : ∀ i' a, genFrame TT l m Y (s, e s i', a) = Y (s, e s i', a) := by
      intro i' a
      simp only [genFrame]
      rw [if_neg (he0 s i')]
    simp only [hx]
    have hts : ∀ i, (lab s i).1 ≠ s := by
      intro i h
      obtain ⟨_, hodd, hss⟩ := hw s i
      rw [h] at hss
      have hx0 : (((lab s i).2 : ℤ) : ZMod d) = 0 := by simpa using hss
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
      have hev : Even ((d : ℕ) : ℤ) := (Int.even_coe_nat d).mpr he
      obtain ⟨k, hk⟩ := hdvd
      have : Even (lab s i).2 := by
        rw [hk]
        exact hev.mul_right k
      exact (Int.not_even_iff_odd.mpr hodd) this
    have hLn : ∀ i, l ^ E s i ≠ 0 := fun i => pow_ne_zero _ hl.ne_zero
    have hinj' : Function.Injective fun i => ((lab s i).1, l ^ E s i) := by
      intro i i' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨ha1, ha2⟩ := h
      have hE := Nat.pow_right_injective hl.two_le ha2
      simp only [E] at hE
      have hm1 := hm s i
      have hm2 := hm s i'
      have ho1 := (hw s i).2.1
      have ho2 := (hw s i').2.1
      have hn1 : (lab s i).2 ≠ 0 := fun h => by rw [h] at ho1; exact absurd ho1 (by decide)
      have hn2 : (lab s i').2 ≠ 0 := fun h => by rw [h] at ho2; exact absurd ho2 (by decide)
      have hj : (lab s i).2 = (lab s i').2 := by omega
      exact hinj s (Prod.ext ha1 hj)
    have hn : J s ≤ N0 := by
      have h := hJ s
      split_ifs at h <;> omega
    exact generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (fun i => l ^ E s i) (e s)
      (he_inj s) hn hts hLn hinj'
  exact theorem_A_frame K l d N0 N1 hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I
    (genFrame TT l m Y) hxg nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab lam hlam1 hpos hneg e he_inj he0 hdet

end Formalism.DworkPowerSeriesWeights
