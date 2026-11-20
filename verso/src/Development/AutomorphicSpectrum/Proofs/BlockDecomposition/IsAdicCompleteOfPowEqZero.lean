import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PerfectWittMaps

/- English proof (translation)
Establish `hI : (Ideal.span {(p : B)}) ^ n = ⊥`. Rewrite using `[Ideal.span_singleton_pow, hn]`. Simplify using the standard rewrite rules. Establish `hz0 : ∀ x y : B, x ≡ y [SMOD ((Ideal.span {(p : B)}) ^ n • ⊤ : Submodule B B)] → x = y`. Introduce `x y h`.

Rewrite `h` using `[hI]`. Simplify `h` using `[SModEq.bot]`. Use `{ haus' := fun x h => hz0 _ _ (h n), prec' := fun f h => ⟨f n, fun m => ?_⟩ }` and prove the remaining obligations. Break down `le_total m n with hmn | hmn` into its components or cases. Conclude with `h hmn`.

Rewrite using `[hz0 _ _ (h hmn)]`.
-/
theorem isAdicComplete_of_pow_eq_zero (p : ℕ) {B : Type} [CommRing B] {n : ℕ} (hn : (p : B) ^ n = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hI : (Ideal.span {(p : B)}) ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn]; simp
  have hz0 : ∀ x y : B, x ≡ y [SMOD ((Ideal.span {(p : B)}) ^ n • ⊤ : Submodule B B)] → x = y := by
    intro x y h
    rw [hI] at h
    simpa [SModEq.bot] using h
  refine { haus' := fun x h => hz0 _ _ (h n), prec' := fun f h => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hmn
  · exact h hmn
  · rw [hz0 _ _ (h hmn)]

/- English proof (translation)
Proceed by induction on `k generalizing a with`. Consider the case `zero => exact ⟨a, by simp⟩`. Consider the case `succ k ih`. Take `⟨c, hc⟩` from `h.2 a`. Take `⟨b, hb⟩` from `ih c`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, pow_mul, hb]`. Conclude with `hc`.
-/
theorem exists_pow_pow_eq (p : ℕ) {A : Type} [CommRing A] (h : Function.Bijective fun x : A => x ^ p)
    (k : ℕ) (a : A) : ∃ b : A, b ^ p ^ k = a := by
  induction k generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := h.2 a
    obtain ⟨b, hb⟩ := ih c
    refine ⟨b, ?_⟩
    rw [pow_succ, pow_mul, hb]
    exact hc

/- English proof (translation)
Set `φ : B ⧸ J →+* ModP B p` to `Ideal.Quotient.lift J ((frobenius (ModP B p) p).comp (Ideal.Quotient.mk _)) (by`. Introduce `x hx`. Rewrite using `[RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hJ x hx)`. Set `σ : A →+* A` to `((frobeniusEquiv A p).symm : A ≃+* A)`.

Set `g₁ : A →+* ModP B p` to `φ.comp (g.comp σ)`. Set `G : A →+* PreTilt B p` to `Perfection.lift p A (ModP B p) g₁`. Establish `hle : Ideal.span {(p : B)} ≤ J` using `(Ideal.span_singleton_le_iff_mem _).2 hpJ`. Set `res : ModP B p →+* B ⧸ J` to `Ideal.Quotient.factor hle`. Establish `hres : ∀ u : B, Ideal.Quotient.mk J u = res (Ideal.Quotient.mk _ u)` using `fun u => rfl`.

Establish `hφ : ∀ y : B ⧸ J, res (φ y) = y ^ p`. Introduce `y`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `: φ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk _ (b ^ p)`. Simplify using `[φ, frobenius_def]`.

Rewrite using `[this, ← hres, map_pow]`. Use `⟨(WittVector.fontaineTheta B p).comp (WittVector.map G), fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : (WittVector.fontaineTheta B p).comp (WittVector.map G) (WittVector.teichmuller p a) = (G a).untilt`. Rewrite using `[RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]`. Establish `h3 : PreTilt.coeff 0 (G a) = g₁ a` using `rfl`.

Rewrite using `[h1, hres, PreTilt.mk_untilt_eq_coeff_zero, h3]`. Express the relevant statement in the definitionally equal form `res (φ (g (σ a))) = g a`. Rewrite using `[hφ, ← map_pow]`. Use `congr 1`. Conclude with `frobeniusEquiv_symm_pow_p A p a`.
-/
theorem exists_lift (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] [IsAdicComplete (Ideal.span {(p : B)}) B] (J : Ideal B)
    (hpJ : (p : B) ∈ J) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) (g : A →+* B ⧸ J) :
    ∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a := by
  let φ : B ⧸ J →+* ModP B p := Ideal.Quotient.lift J
    ((frobenius (ModP B p) p).comp (Ideal.Quotient.mk _)) (by
      intro x hx
      rw [RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJ x hx)
  let σ : A →+* A := ((frobeniusEquiv A p).symm : A ≃+* A)
  let g₁ : A →+* ModP B p := φ.comp (g.comp σ)
  let G : A →+* PreTilt B p := Perfection.lift p A (ModP B p) g₁
  have hle : Ideal.span {(p : B)} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hpJ
  let res : ModP B p →+* B ⧸ J := Ideal.Quotient.factor hle
  have hres : ∀ u : B, Ideal.Quotient.mk J u = res (Ideal.Quotient.mk _ u) := fun u => rfl
  have hφ : ∀ y : B ⧸ J, res (φ y) = y ^ p := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : φ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk _ (b ^ p) := by
      simp [φ, frobenius_def]
    rw [this, ← hres, map_pow]
  refine ⟨(WittVector.fontaineTheta B p).comp (WittVector.map G), fun a => ?_⟩
  have h1 : (WittVector.fontaineTheta B p).comp (WittVector.map G) (WittVector.teichmuller p a)
      = (G a).untilt := by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
  have h3 : PreTilt.coeff 0 (G a) = g₁ a := rfl
  rw [h1, hres, PreTilt.mk_untilt_eq_coeff_zero, h3]
  change res (φ (g (σ a))) = g a
  rw [hφ, ← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p A p a

/- English proof (translation)
Use `WittVector.eq_of_apply_teichmuller_eq f f' ⟨n, hn⟩ fun a => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `exists_pow_pow_eq p hbij (n + 1) a`. Rewrite using `[map_pow, map_pow, map_pow]`. Use `set u := f (WittVector.teichmuller p b)`. Use `set v := f' (WittVector.teichmuller p b)`.

Establish `huv : u - v ∈ J` using `Ideal.Quotient.eq.1 (h b)`. Establish `h1 : (p : B) ∣ u ^ p - v ^ p`. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, ← sub_pow_char, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hJ _ huv`. Establish `h2` using `dvd_sub_pow_of_dvd_sub h1 n`.

Establish `h0 : (p : B) ^ (n + 1) = 0` using `by rw [pow_succ, hn, zero_mul]`. Rewrite `h2` using `[h0, zero_dvd_iff, sub_eq_zero, ← pow_mul, ← pow_mul, ← pow_succ']`. Conclude with `h2`.
-/
theorem lift_unique (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] (J : Ideal B) (n : ℕ) (hbij : Function.Bijective fun x : A => x ^ p)
    (hn : (p : B) ^ n = 0) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)})
    (f f' : WittVector p A →+* B)
    (h : ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) =
      Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) : f = f' := by
  refine WittVector.eq_of_apply_teichmuller_eq f f' ⟨n, hn⟩ fun a => ?_
  obtain ⟨b, rfl⟩ := exists_pow_pow_eq p hbij (n + 1) a
  rw [map_pow, map_pow, map_pow]
  set u := f (WittVector.teichmuller p b)
  set v := f' (WittVector.teichmuller p b)
  have huv : u - v ∈ J := Ideal.Quotient.eq.1 (h b)
  have h1 : (p : B) ∣ u ^ p - v ^ p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow,
      ← sub_pow_char, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ _ huv
  have h2 := dvd_sub_pow_of_dvd_sub h1 n
  have h0 : (p : B) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [h0, zero_dvd_iff, sub_eq_zero, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  exact h2

/- English proof (translation)
Introduce `p _ A B _ _ J n hA hn hpJ hJ g`. Distinguish the cases in `hB : Subsingleton B`. Establish `hQ : Subsingleton (B ⧸ J)` using `(Ideal.Quotient.mk_surjective (I := J)).subsingleton`. Use `⟨⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _, map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun a => Subsingleton.elim _ _⟩, fun f f' _ => RingHom.ext fun x => Subsingleton.elim _ _⟩` and prove the remaining obligations. Rewrite `hB` using `[not_subsingleton_iff_nontrivial]`.

Establish `hu : ¬IsUnit (p : B)` using `IsNilpotent.not_isUnit ⟨n, hn⟩`. Use `haveI : Fact ¬IsUnit (p : B) := ⟨hu⟩`. Use `haveI := isAdicComplete_of_pow_eq_zero p hn`. Establish `hAn : Nontrivial A`. Assume the negation of the conclusion as `hA'`.

Rewrite `hA'` using `[not_nontrivial_iff_subsingleton]`. Establish `h1 : (1 : B) ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_one, ← map_one g, Subsingleton.elim (1 : A) 0, map_zero]`. Establish `h2` using `hJ 1 h1`. Rewrite `h2` using `[one_pow, Ideal.mem_span_singleton]`.

Conclude with `hu (isUnit_of_dvd_one h2)`. Use `haveI : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hA.char`. Use `haveI : PerfectRing A p := ⟨hA.bij⟩`. Conclude with `⟨exists_lift p J hpJ hJ g, fun f f' h => lift_unique p J n hA.bij hn hJ f f' h⟩`.
-/
theorem wittVector_lift : ∀ (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] (J : Ideal B) (n : ℕ), D.Pf p A → (p : B) ^ n = 0 → (p : B) ∈ J → (∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) → ∀ g : A →+* B ⧸ J, (∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a) ∧ ∀ f f' : WittVector p A →+* B, (∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) → f = f' := by
  intro p _ A B _ _ J n hA hn hpJ hJ g
  by_cases hB : Subsingleton B
  · have hQ : Subsingleton (B ⧸ J) := (Ideal.Quotient.mk_surjective (I := J)).subsingleton
    refine ⟨⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
               map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun a => Subsingleton.elim _ _⟩,
      fun f f' _ => RingHom.ext fun x => Subsingleton.elim _ _⟩
  · rw [not_subsingleton_iff_nontrivial] at hB
    have hu : ¬IsUnit (p : B) := IsNilpotent.not_isUnit ⟨n, hn⟩
    haveI : Fact ¬IsUnit (p : B) := ⟨hu⟩
    haveI := isAdicComplete_of_pow_eq_zero p hn
    have hAn : Nontrivial A := by
      by_contra hA'
      rw [not_nontrivial_iff_subsingleton] at hA'
      have h1 : (1 : B) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one, ← map_one g, Subsingleton.elim (1 : A) 0, map_zero]
      have h2 := hJ 1 h1
      rw [one_pow, Ideal.mem_span_singleton] at h2
      exact hu (isUnit_of_dvd_one h2)
    haveI : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hA.char
    haveI : PerfectRing A p := ⟨hA.bij⟩
    exact ⟨exists_lift p J hpJ hJ g, fun f f' h => lift_unique p J n hA.bij hn hJ f f' h⟩

end GlobalTheory.CompanionTheory.PerfectWittMaps
