import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumNormNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqCocycleSum

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleSign

/- English proof (translation)
Use `choose g hg using hs`. Set `a : (B ⧸ A.addSubgroupOf B) → ι → R` to `fun q => g _ (Quotient.out q : B).2`. Establish `ha : ∀ q, ((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C` using `fun q => hg _ _`. Set `e : (B ⧸ A.addSubgroupOf B) → (ι → R ⧸ P)` to `fun q i => Ideal.Quotient.mk P (a q i)`. Establish `hinj : Function.Injective e`.

Introduce `q q' h`. Establish `h1 : f (a q' - a q) ∈ A` using `(hk _).2 fun i => by`. Use `congrFun h i` as an intermediate fact. Conclude with `Ideal.Quotient.eq.1 this.symm`. Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Establish `h2` using `A.add_mem (A.sub_mem (ha q').1 (ha q).1) h1`. Rewrite `h2` using `[map_sub]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Normalize the expressions using the abelian group laws.

Establish `hsurj : Function.Surjective e`. Introduce `t`. Set `b : ι → R` to `fun i => Quotient.out (t i)`. Set `q : B ⧸ A.addSubgroupOf B` to `QuotientAddGroup.mk ⟨f b, hB b⟩`. Establish `h1 : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B) = QuotientAddGroup.mk ⟨f b, hB b⟩` using `QuotientAddGroup.out_eq' q`.

Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Establish `h2 : f (b - a q) ∈ A`. Use `A.add_mem h1 (ha q).1` as an intermediate fact. Rewrite using `[map_sub]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Normalize the expressions using the abelian group laws. Use `⟨q, funext fun i => ?_⟩` and prove the remaining obligations. Establish `h3` using `Ideal.Quotient.eq.2 ((hk _).1 h2 i)`. Rewrite using `[← Ideal.Quotient.mk_out (t i)]`.

Conclude with `h3.symm`. Conclude with `⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, a, fun q => ⟨ha q, fun i => rfl⟩⟩`.
-/
theorem exists_coords {V R ι : Type} [AddCommGroup V] [CommRing R] (P : Ideal R) (A B C : AddSubgroup V)
    (f : (ι → R) →+ V) (hB : ∀ a, f a ∈ B) (hk : ∀ a, f a ∈ A ↔ ∀ i, a i ∈ P)
    (hs : ∀ z ∈ B, ∃ a, z - f a ∈ A ∧ z - f a ∈ C) :
    ∃ (e : (B ⧸ A.addSubgroupOf B) ≃ (ι → R ⧸ P)) (a : (B ⧸ A.addSubgroupOf B) → ι → R),
      ∀ q, (((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C) ∧
        ∀ i, Ideal.Quotient.mk P (a q i) = e q i := by
  choose g hg using hs
  let a : (B ⧸ A.addSubgroupOf B) → ι → R := fun q => g _ (Quotient.out q : B).2
  have ha : ∀ q, ((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C :=
    fun q => hg _ _
  let e : (B ⧸ A.addSubgroupOf B) → (ι → R ⧸ P) := fun q i => Ideal.Quotient.mk P (a q i)
  have hinj : Function.Injective e := by
    intro q q' h
    have h1 : f (a q' - a q) ∈ A := (hk _).2 fun i => by
      have := congrFun h i
      exact Ideal.Quotient.eq.1 this.symm
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    have h2 := A.add_mem (A.sub_mem (ha q').1 (ha q).1) h1
    rw [map_sub] at h2
    convert h2 using 1
    push_cast; abel
  have hsurj : Function.Surjective e := by
    intro t
    let b : ι → R := fun i => Quotient.out (t i)
    let q : B ⧸ A.addSubgroupOf B := QuotientAddGroup.mk ⟨f b, hB b⟩
    have h1 : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B) = QuotientAddGroup.mk ⟨f b, hB b⟩ :=
      QuotientAddGroup.out_eq' q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : f (b - a q) ∈ A := by
      have := A.add_mem h1 (ha q).1
      rw [map_sub]
      convert this using 1
      push_cast; abel
    refine ⟨q, funext fun i => ?_⟩
    have h3 := Ideal.Quotient.eq.2 ((hk _).1 h2 i)
    rw [← Ideal.Quotient.mk_out (t i)]
    exact h3.symm
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, a, fun q => ⟨ha q, fun i => rfl⟩⟩

def ch (D : D7) (s : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Real.sqrt D.host.d * s.re + s.im : ℝ) : ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bc_eq (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y = ch D (Hf D T x y) := rfl

/- English proof (translation)
Rewrite using `[ch, ch, ch, ← Complex.exp_add, Complex.add_re, Complex.add_im]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ch_add (D : D7) (s t : ℂ) : ch D (s + t) = ch D s * ch D t := by
  rw [ch, ch, ch, ← Complex.exp_add, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

/- English proof (translation)
Simplify using `[ch]`.
-/
theorem ch_zero (D : D7) : ch D 0 = 1 := by simp [ch]

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem ch_ne_zero (D : D7) (s : ℂ) : ch D s ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [bc_zero_left]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_left, ih]`.
-/
theorem bc_sum_left (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type} (s : Finset ι) (x : ι → VC D N N') (y : VC D N N') :
    bc D T (∑ i ∈ s, x i) y = ∏ i ∈ s, bc D T (x i) y := by
  induction s using Finset.induction_on with
  | empty => simp [bc_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_left, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [bc_zero_right]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_right, ih]`.
-/
theorem bc_sum_right (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type} (s : Finset ι) (x : VC D N N') (y : ι → VC D N N') :
    bc D T x (∑ i ∈ s, y i) = ∏ i ∈ s, bc D T x (y i) := by
  induction s using Finset.induction_on with
  | empty => simp [bc_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_right, ih]

def sumHom {V R ι : Type} [Fintype ι] [AddCommGroup V] [CommRing R] (X : ι → R →+ V) : (ι → R) →+ V where
  toFun a := ∑ i, X i (a i)
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sumHom_apply {V R ι : Type} [Fintype ι] [AddCommGroup V] [CommRing R] (X : ι → R →+ V) (a : ι → R) :
    sumHom X a = ∑ i, X i (a i) := rfl

/- English proof (translation)
Establish `hr : (r₀ : ℂ) ≠ 0` using `by exact_mod_cast h0.ne'`. Establish `h1 : μ = (-1) ^ r * ((m / r₀ : ℝ) : ℂ)` using `by push_cast; field_simp; exact h`. Establish `h2 : (m / r₀) ^ 8 = 1`. Rewrite `h8` using `[h1, mul_pow, ← pow_mul, mul_comm r 8, pow_mul]`. Evaluate the numerical expressions using `at h8`.

Conclude with `h8` after adjusting the coercions. Establish `h3 : m / r₀ = 1` using `(pow_eq_one_iff_of_nonneg (div_pos hm h0).le (by norm_num)).1 h2`. Rewrite using `[h1, h3]`. Simplify using the standard rewrite rules.
-/
theorem sign_of_pow {μ : ℂ} {r : ℕ} {r₀ m : ℝ} (h0 : 0 < r₀) (hm : 0 < m) (h8 : μ ^ 8 = 1)
    (h : μ * (r₀ : ℂ) = (-1) ^ r * (m : ℂ)) : μ = (-1) ^ r := by
  have hr : (r₀ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : μ = (-1) ^ r * ((m / r₀ : ℝ) : ℂ) := by
    push_cast; field_simp; exact h
  have h2 : (m / r₀) ^ 8 = 1 := by
    rw [h1, mul_pow, ← pow_mul, mul_comm r 8, pow_mul] at h8
    norm_num at h8
    exact_mod_cast h8
  have h3 : m / r₀ = 1 := (pow_eq_one_iff_of_nonneg (div_pos hm h0).le (by norm_num)).1 h2
  rw [h1, h3]; simp

/- English proof (translation)
Introduce `D T N N' A₁ A₂ A₃ e μ hT P r hP hσ hne hD`. Take `⟨r₀, hr₀, hμ⟩` from `GlobalTheory.TripleConstant.mu_form D T N N' A₁ A₂ A₃ e μ hT`. Take `⟨n₁, n₂, n₃, -, -, -, -, -, h8, -⟩` from `hT`. Take `⟨X, Y, φ, hH, hm, hp, s₂, s₃, k₁, k₂⟩` from `hD`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)`.

Establish `: Finite (𝓞 D.host.E ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Set `_ : Fintype (𝓞 D.host.E ⧸ P)` to `Fintype.ofFinite _`. Set `χ : Fin r → 𝓞 D.host.E → ℂ` to `fun i s => ch D (φ i s)`. Establish `χadd : ∀ i a b, χ i (a + b) = χ i a * χ i b` using `fun i a b => by simp only [χ, map_add, ch_add]`. Establish `hYX : ∀ i a a', bc D T (Y i a') (X i a) = χ i (a' * sgO D a)` using `fun i a a' => by`.

Rewrite using `[bc_eq, hH, if_pos rfl]`. Establish `hYX' : ∀ i j a a', i ≠ j → bc D T (Y i a') (X j a) = 1` using `fun i j a a' h => by`. Rewrite using `[bc_eq, hH, if_neg h, ch_zero]`. Establish `hXY' : ∀ i j a a', i ≠ j → bc D T (X j a) (Y i a') = 1` using `fun i j a a' h => by`. Rewrite using `[bc_eq, ← Hf_conj, hH, if_neg h, map_zero, ch_zero]`.

Establish `χP : ∀ i, ∀ a ∈ P, χ i a = 1` using `fun i a ha => by`. Use `hYX i 1 a` as an intermediate fact. Rewrite `this` using `[map_one (sgO D), mul_one]`. Rewrite using `[← this]`. Conclude with `n₂.2.1 _ (hp i a ha).2.2 _ (hm i 1).1`.

Establish `χne : ∀ i, ∃ a, χ i (a + sgO D a) ≠ 1` using `fun i => by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `c1 : ∀ j a, bc D T (X i 1) (Y j a) = bc D T (Y j a) (X i 1)` using `fun j a => by`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Establish `e1` using `n₁.2.1 _ (hm j 1).2.2 _ (hm j a).2.2`. Rewrite `e1` using `[bc_add_left, bc_add_right, bc_add_right, n₂.2.1 _ (hm j 1).1 _ (hm j a).1, n₃.2.1 _ (hm j 1).2.1 _ (hm j a).2.1, hYX, one_mul, one_mul, mul_one]`. Establish `e2` using `hc a`. Rewrite `e2` using `[χadd]`.

Rewrite using `[hYX, map_one (sgO D), mul_one]`. Conclude with `mul_right_cancel₀ (ch_ne_zero D _) (e1.trans e2.symm)`. Rewrite using `[hYX' j i _ _ h, hXY' j i _ _ h]`. Establish `c2 : X i 1 ∈ A₃` using `n₃.2.2 _ fun y hy => by`. Take `⟨a, ha⟩` from `s₃ y hy`.

Establish `hy' : y = (y - ∑ j, Y j (a j)) + ∑ j, Y j (a j)` using `by abel`. Rewrite using `[hy', bc_add_left, bc_add_right, n₂.2.1 _ ha.2 _ (hm i 1).1, n₂.2.1 _ (hm i 1).1 _ ha.2, bc_sum_left, bc_sum_right]`. Simplify using `only [c1]`. Take `⟨a, ha⟩` from `s₃ _ c2`. Establish `c3 : ∑ j, Y j (a j) ∈ A₂`.

Use `A₂.sub_mem (hm i 1).1 ha.2` as an intermediate fact. Simplify using `using this`. Establish `c4 : ∑ j, Y j (a j) ∈ A₁` using `A₁.sum_mem fun j _ => (hp j _ (k₂ a c3 j)).2.1`. Establish `c5 : X i 1 ∈ A₁`. Use `A₁.add_mem ha.1 c4` as an intermediate fact.

Simplify using `using this`. Establish `c6 : ∑ j, X j ((Pi.single i 1 : Fin r → 𝓞 D.host.E) j) = X i 1`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Rewrite using `[Pi.single_eq_of_ne hj, map_zero]`. Simplify using the standard rewrite rules. Establish `c7` using `k₁ (Pi.single i 1) (c6 ▸ c5) i`. Rewrite `c7` using `[Pi.single_eq_same]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).2 c7)`.

Establish `hG : ∀ i, ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : 𝓞 D.host.E ⧸ P, χ i (Quotient.out q * sgO D (Quotient.out q)) = -(m : ℂ)` using `fun i => GlobalTheory.NormGauss.finsum_norm_neg _ (sgO D) P (sgO_sgO D) hσ hne (χ i) (χadd i) (χP i) (χne i)`. Use `choose m hm0 hmG using hG`. Establish `kX : ∀ a, sumHom X a ∈ A₁ ↔ ∀ i, a i ∈ P` using `fun a => ⟨k₁ a, fun h => by rw [sumHom_apply]; exact A₁.sum_mem fun i _ => (hp i _ (h i)).1.1⟩`. Establish `kY : ∀ a, sumHom Y a ∈ A₂ ↔ ∀ i, a i ∈ P` using `fun a => ⟨k₂ a, fun h => by rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hp i _ (h i)).2.2⟩`. Establish `mX : ∀ a, sumHom X a ∈ A₂` using `fun a => by`.

Rewrite using `[sumHom_apply]`. Conclude with `A₂.sum_mem fun i _ => (hm i _).1`. Establish `mY : ∀ a, sumHom Y a ∈ A₃` using `fun a => by`. Rewrite using `[sumHom_apply]`. Conclude with `A₃.sum_mem fun i _ => (hm i _).2.1`.

Establish `mXY : ∀ a, sumHom X a + sumHom Y a ∈ A₁` using `fun a => by`. Rewrite using `[sumHom_apply, sumHom_apply, ← Finset.sum_add_distrib]`. Conclude with `A₁.sum_mem fun i _ => (hm i _).2.2`. Take `⟨e₂, a₂, h₂⟩` from `exists_coords P A₁ A₂ A₃ (sumHom X) mX kX (fun z hz => (s₂ z hz).imp fun a ha => ⟨ha.1, ha.2⟩)`. Take `⟨e₃, a₃, h₃⟩` from `exists_coords P A₂ A₃ A₁ (sumHom Y) mY kY (fun z hz => (s₃ z hz).imp fun a ha => ⟨ha.2, ha.1⟩)`.

Set `F : (Fin r → 𝓞 D.host.E ⧸ P) × (Fin r → 𝓞 D.host.E ⧸ P) → ℂ` to `fun p => if p.1 = p.2 then ∏ i, χ i (Quotient.out (p.2 i) * sgO D (Quotient.out (p.2 i))) else 0`. Establish `key : ∀ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) = F (Equiv.prodCongr e₃ e₂ p …`. Introduce and unpack `⟨q₃, q₂⟩`. Take `⟨⟨u1, u3⟩, u⟩` from `h₂ q₂`. Take `⟨⟨v2, v1⟩, v⟩` from `h₃ q₃`.

Establish `x2` using `(Quotient.out q₂ : A₂).2`. Establish `y3` using `(Quotient.out q₃ : A₃).2`. Simplify using `only [F, Equiv.prodCongr_apply, Prod.map]`. Generalize the expression as in `((Quotient.out q₂ : A₂) : VC D N N') = x at *`. Generalize the expression as in `((Quotient.out q₃ : A₃) : VC D N N') = y at *`.

Establish `hiff : y + x ∈ A₁ ↔ e₃ q₃ = e₂ q₂`. Establish `w : y + x = sumHom X (a₂ q₂ - a₃ q₃) + ((x - sumHom X (a₂ q₂)) + (y - sumHom Y (a₃ q₃)) + (sumHom X (a₃ q₃) + sumHom Y (a₃ q₃)))` using `by rw [map_sub]; abel`. Rewrite using `[w, A₁.add_mem_cancel_right (A₁.add_mem (A₁.add_mem u1 v1) (mXY _)), kX, funext_iff]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[← u, ← v, eq_comm, Ideal.Quotient.eq, Pi.sub_apply]`.

Distinguish the cases in `h : e₃ q₃ = e₂ q₂`. Rewrite using `[if_pos (hiff.2 h), if_pos h]`. Establish `wx : x = sumHom X (a₂ q₂) + (x - sumHom X (a₂ q₂))` using `by abel`. Establish `wy : y = sumHom Y (a₃ q₃) + (y - sumHom Y (a₃ q₃))` using `by abel`. Rewrite using `[wy, bc_add_left, n₂.2.1 _ v2 _ x2, mul_one, wx, bc_add_right, n₃.2.1 _ (mY _) _ u3, mul_one, sumHom_apply, sumHom_apply, bc_sum_left]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[bc_sum_right, Finset.prod_eq_single i (fun j _ hj => hYX' i j _ _ hj.symm) (by simp), hYX]`. Use `set t := Quotient.out (e₂ q₂ i) with ht`. Establish `t2 : a₂ q₂ i - t ∈ P` using `Ideal.Quotient.eq.1 (by rw [u, ht, Ideal.Quotient.mk_out])`. Establish `t3 : a₃ q₃ i - t ∈ P` using `Ideal.Quotient.eq.1 (by rw [v, h, ht, Ideal.Quotient.mk_out])`.

Establish `w : a₃ q₃ i * sgO D (a₂ q₂ i) = t * sgO D t + ((a₃ q₃ i - t) * sgO D (a₂ q₂ i) + t * sgO D (a₂ q₂ i - t))` using `by rw [map_sub]; ring`. Rewrite using `[w, χadd, χP i _ (P.add_mem (P.mul_mem_right _ t3) (P.mul_mem_left _ (hσ _ t2))), mul_one]`. Rewrite using `[if_neg (mt hiff.1 h), if_neg h]`. Rewrite `hμ` using `[finsum_congr key, finsum_comp_equiv (Equiv.prodCongr e₃ e₂) (f := F), finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right]`. Simplify using `only [F, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hμ`.

Simplify using `only [finsum_eq_sum_of_fintype] at hmG`. Rewrite `hμ` using `[← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun i (t : 𝓞 D.host.E ⧸ P) => χ i (Quotient.out t * sgO D (Quotient.out t)))]`. Simplify using `only [hmG] at hμ`. Use `sign_of_pow hr₀ (Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hm0 i) h8 ?_` and prove the remaining obligations. Rewrite using `[hμ, Finset.prod_neg]`.

Simplify using the standard rewrite rules.
-/
theorem mu_eq_sign : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ),
    Trip D T A₁ A₂ A₃ e μ → ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) →
    (∃ a, a - sgO D a ∉ P) → TriDat D T A₁ A₂ A₃ P r → μ = (-1) ^ r := by
  intro D T N N' A₁ A₂ A₃ e μ hT P r hP hσ hne hD
  obtain ⟨r₀, hr₀, hμ⟩ := GlobalTheory.TripleConstant.mu_form D T N N' A₁ A₂ A₃ e μ hT
  obtain ⟨n₁, n₂, n₃, -, -, -, -, -, h8, -⟩ := hT
  obtain ⟨X, Y, φ, hH, hm, hp, s₂, s₃, k₁, k₂⟩ := hD
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  let _ : Fintype (𝓞 D.host.E ⧸ P) := Fintype.ofFinite _
  let χ : Fin r → 𝓞 D.host.E → ℂ := fun i s => ch D (φ i s)
  have χadd : ∀ i a b, χ i (a + b) = χ i a * χ i b := fun i a b => by simp only [χ, map_add, ch_add]
  have hYX : ∀ i a a', bc D T (Y i a') (X i a) = χ i (a' * sgO D a) := fun i a a' => by
    rw [bc_eq, hH, if_pos rfl]
  have hYX' : ∀ i j a a', i ≠ j → bc D T (Y i a') (X j a) = 1 := fun i j a a' h => by
    rw [bc_eq, hH, if_neg h, ch_zero]
  have hXY' : ∀ i j a a', i ≠ j → bc D T (X j a) (Y i a') = 1 := fun i j a a' h => by
    rw [bc_eq, ← Hf_conj, hH, if_neg h, map_zero, ch_zero]
  have χP : ∀ i, ∀ a ∈ P, χ i a = 1 := fun i a ha => by
    have := hYX i 1 a
    rw [map_one (sgO D), mul_one] at this
    rw [← this]
    exact n₂.2.1 _ (hp i a ha).2.2 _ (hm i 1).1
  have χne : ∀ i, ∃ a, χ i (a + sgO D a) ≠ 1 := fun i => by
    by_contra hc
    push Not at hc
    have c1 : ∀ j a, bc D T (X i 1) (Y j a) = bc D T (Y j a) (X i 1) := fun j a => by
      by_cases h : j = i
      · subst h
        have e1 := n₁.2.1 _ (hm j 1).2.2 _ (hm j a).2.2
        rw [bc_add_left, bc_add_right, bc_add_right, n₂.2.1 _ (hm j 1).1 _ (hm j a).1,
          n₃.2.1 _ (hm j 1).2.1 _ (hm j a).2.1, hYX, one_mul, one_mul, mul_one] at e1
        have e2 := hc a
        rw [χadd] at e2
        rw [hYX, map_one (sgO D), mul_one]
        exact mul_right_cancel₀ (ch_ne_zero D _) (e1.trans e2.symm)
      · rw [hYX' j i _ _ h, hXY' j i _ _ h]
    have c2 : X i 1 ∈ A₃ := n₃.2.2 _ fun y hy => by
      obtain ⟨a, ha⟩ := s₃ y hy
      have hy' : y = (y - ∑ j, Y j (a j)) + ∑ j, Y j (a j) := by abel
      rw [hy', bc_add_left, bc_add_right, n₂.2.1 _ ha.2 _ (hm i 1).1, n₂.2.1 _ (hm i 1).1 _ ha.2,
        bc_sum_left, bc_sum_right]
      simp only [c1]
    obtain ⟨a, ha⟩ := s₃ _ c2
    have c3 : ∑ j, Y j (a j) ∈ A₂ := by
      have := A₂.sub_mem (hm i 1).1 ha.2
      simpa using this
    have c4 : ∑ j, Y j (a j) ∈ A₁ := A₁.sum_mem fun j _ => (hp j _ (k₂ a c3 j)).2.1
    have c5 : X i 1 ∈ A₁ := by
      have := A₁.add_mem ha.1 c4
      simpa using this
    have c6 : ∑ j, X j ((Pi.single i 1 : Fin r → 𝓞 D.host.E) j) = X i 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, map_zero]
      · simp
    have c7 := k₁ (Pi.single i 1) (c6 ▸ c5) i
    rw [Pi.single_eq_same] at c7
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 c7)
  have hG : ∀ i, ∃ m : ℝ, 0 < m ∧
      ∑ᶠ q : 𝓞 D.host.E ⧸ P, χ i (Quotient.out q * sgO D (Quotient.out q)) = -(m : ℂ) := fun i =>
    GlobalTheory.NormGauss.finsum_norm_neg _ (sgO D) P (sgO_sgO D) hσ hne (χ i) (χadd i) (χP i) (χne i)
  choose m hm0 hmG using hG
  have kX : ∀ a, sumHom X a ∈ A₁ ↔ ∀ i, a i ∈ P := fun a =>
    ⟨k₁ a, fun h => by rw [sumHom_apply]; exact A₁.sum_mem fun i _ => (hp i _ (h i)).1.1⟩
  have kY : ∀ a, sumHom Y a ∈ A₂ ↔ ∀ i, a i ∈ P := fun a =>
    ⟨k₂ a, fun h => by rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hp i _ (h i)).2.2⟩
  have mX : ∀ a, sumHom X a ∈ A₂ := fun a => by
    rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hm i _).1
  have mY : ∀ a, sumHom Y a ∈ A₃ := fun a => by
    rw [sumHom_apply]; exact A₃.sum_mem fun i _ => (hm i _).2.1
  have mXY : ∀ a, sumHom X a + sumHom Y a ∈ A₁ := fun a => by
    rw [sumHom_apply, sumHom_apply, ← Finset.sum_add_distrib]
    exact A₁.sum_mem fun i _ => (hm i _).2.2
  obtain ⟨e₂, a₂, h₂⟩ := exists_coords P A₁ A₂ A₃ (sumHom X) mX kX
    (fun z hz => (s₂ z hz).imp fun a ha => ⟨ha.1, ha.2⟩)
  obtain ⟨e₃, a₃, h₃⟩ := exists_coords P A₂ A₃ A₁ (sumHom Y) mY kY
    (fun z hz => (s₃ z hz).imp fun a ha => ⟨ha.2, ha.1⟩)
  let F : (Fin r → 𝓞 D.host.E ⧸ P) × (Fin r → 𝓞 D.host.E ⧸ P) → ℂ := fun p =>
    if p.1 = p.2 then ∏ i, χ i (Quotient.out (p.2 i) * sgO D (Quotient.out (p.2 i))) else 0
  have key : ∀ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂),
      (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) =
      F (Equiv.prodCongr e₃ e₂ p) := by
    rintro ⟨q₃, q₂⟩
    obtain ⟨⟨u1, u3⟩, u⟩ := h₂ q₂
    obtain ⟨⟨v2, v1⟩, v⟩ := h₃ q₃
    have x2 := (Quotient.out q₂ : A₂).2
    have y3 := (Quotient.out q₃ : A₃).2
    simp only [F, Equiv.prodCongr_apply, Prod.map]
    generalize ((Quotient.out q₂ : A₂) : VC D N N') = x at *
    generalize ((Quotient.out q₃ : A₃) : VC D N N') = y at *
    have hiff : y + x ∈ A₁ ↔ e₃ q₃ = e₂ q₂ := by
      have w : y + x = sumHom X (a₂ q₂ - a₃ q₃) + ((x - sumHom X (a₂ q₂)) + (y - sumHom Y (a₃ q₃)) +
          (sumHom X (a₃ q₃) + sumHom Y (a₃ q₃))) := by rw [map_sub]; abel
      rw [w, A₁.add_mem_cancel_right (A₁.add_mem (A₁.add_mem u1 v1) (mXY _)), kX, funext_iff]
      refine forall_congr' fun i => ?_
      rw [← u, ← v, eq_comm, Ideal.Quotient.eq, Pi.sub_apply]
    by_cases h : e₃ q₃ = e₂ q₂
    · rw [if_pos (hiff.2 h), if_pos h]
      have wx : x = sumHom X (a₂ q₂) + (x - sumHom X (a₂ q₂)) := by abel
      have wy : y = sumHom Y (a₃ q₃) + (y - sumHom Y (a₃ q₃)) := by abel
      rw [wy, bc_add_left, n₂.2.1 _ v2 _ x2, mul_one, wx, bc_add_right, n₃.2.1 _ (mY _) _ u3, mul_one,
        sumHom_apply, sumHom_apply, bc_sum_left]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [bc_sum_right, Finset.prod_eq_single i (fun j _ hj => hYX' i j _ _ hj.symm) (by simp), hYX]
      set t := Quotient.out (e₂ q₂ i) with ht
      have t2 : a₂ q₂ i - t ∈ P := Ideal.Quotient.eq.1 (by rw [u, ht, Ideal.Quotient.mk_out])
      have t3 : a₃ q₃ i - t ∈ P := Ideal.Quotient.eq.1 (by rw [v, h, ht, Ideal.Quotient.mk_out])
      have w : a₃ q₃ i * sgO D (a₂ q₂ i) = t * sgO D t +
          ((a₃ q₃ i - t) * sgO D (a₂ q₂ i) + t * sgO D (a₂ q₂ i - t)) := by rw [map_sub]; ring
      rw [w, χadd, χP i _ (P.add_mem (P.mul_mem_right _ t3) (P.mul_mem_left _ (hσ _ t2))), mul_one]
    · rw [if_neg (mt hiff.1 h), if_neg h]
  rw [finsum_congr key, finsum_comp_equiv (Equiv.prodCongr e₃ e₂) (f := F), finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type_right] at hμ
  simp only [F, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hμ
  simp only [finsum_eq_sum_of_fintype] at hmG
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun i (t : 𝓞 D.host.E ⧸ P) => χ i (Quotient.out t * sgO D (Quotient.out t)))] at hμ
  simp only [hmG] at hμ
  refine sign_of_pow hr₀ (Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hm0 i) h8 ?_
  rw [hμ, Finset.prod_neg]
  simp

end GlobalTheory.TriangleSign
