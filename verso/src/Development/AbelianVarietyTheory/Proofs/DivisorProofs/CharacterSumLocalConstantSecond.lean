import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.BadPrimes

/- English proof (translation)
Take `⟨x, y, hxy⟩` from `h`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)))`.
-/
theorem false_of_isCoprime {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {a b : A}
    (h : IsCoprime a b) (ha : a ∈ P.asIdeal) (hb : b ∈ P.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := h
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)))

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Conclude with `false_of_isCoprime P (Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)) ha hb`.
-/
theorem eq_of_natCast_mem {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : (p : A) ∈ P.asIdeal) (hb : (q : A) ∈ P.asIdeal) : p = q := by
  by_contra hne
  exact false_of_isCoprime P (Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)) ha hb

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Introduce `i j h`. Use `hPr.g_ne` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`.
-/
theorem g_injective (hPr : Pr.Ok) : Function.Injective Pr.g := by
  intro i j h
  have := hPr.g_ne
  fin_cases i <;> fin_cases j <;> simp_all

/- English proof (translation)
Break down `Finset.mem_union.mp h with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`.
-/
theorem exists_vG {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, P ∈ Pr.vG i := by
  classical
  rcases Finset.mem_union.mp h with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/- English proof (translation)
The claim follows from `hPr.piG_norm i ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)`.
-/
theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piG_norm i ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)

/- English proof (translation)
The claim follows from `hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ (mem_of_mem_divs h)`.
-/
theorem T_mem (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ (mem_of_mem_divs h)

/- English proof (translation)
Rewrite `h` using `[mem_conjP, map_natCast]`. Conclude with `h`.
-/
theorem natCast_mem_of_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} (h : ((n : ℕ) : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal) :
    ((n : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast] at h
  exact h

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Break down `Finset.mem_union.mp hw with h | h` into its components or cases. Conclude with `h`.

Establish `h' : w ∈ QE sel ((mu0 X.F X.E X.K Sg : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K)` using `h`. Rewrite `h'` using `[twistPrimes_trivialTuple_empty sel Sg]`. Simplify using `at h'`. Introduce `hw`. Conclude with `Finset.mem_union.mpr (Or.inl hw)`.
-/
theorem rowSG_one (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) :
    rowSG Pr sel (1 : Tup X.F X.E X.K Sg) = Pr.vGs := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with h | h
    · exact h
    · have h' : w ∈ QE sel ((mu0 X.F X.E X.K Sg : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) := h
      rw [twistPrimes_trivialTuple_empty sel Sg] at h'
      simp at h'
  · intro hw
    exact Finset.mem_union.mpr (Or.inl hw)

/- English proof (translation)
Establish `hd : Disjoint (Pr.vG 0) (Pr.vG 1)` using `Finset.disjoint_left.2 fun P h0 h1 => hPr.g_ne (eq_of_natCast_mem P (hPr.g_prime 0) (hPr.g_prime 1) (g_mem hPr h0) (g_mem hPr h1))`. Establish `hi : ∀ i, ∏ P ∈ Pr.vG i, Formalism.L2.Col.qOf P = Pr.g i ^ X.f` using `fun i => by`. Unfold `Formalism.L2.Col.qOf`. Rewrite using `[Finset.prod_congr rfl (g := fun _ => Pr.g i) (fun P hP => hPr.vG_norm i P hP), Finset.prod_const, hPr.vG_card]`. Establish `hu : Pr.vGs = (Pr.vG 0).disjUnion (Pr.vG 1) hd`.

Use extensionality with `w`. Simplify using `[Primes.vGs]`. Rewrite using `[hu, Finset.prod_disjUnion, hi, hi, mul_pow]`.
-/
theorem prod_qOf_vGs (hPr : Pr.Ok) : ∏ P ∈ Pr.vGs, Formalism.L2.Col.qOf P = (Pr.g 0 * Pr.g 1) ^ X.f := by
  classical
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := Finset.disjoint_left.2 fun P h0 h1 =>
    hPr.g_ne (eq_of_natCast_mem P (hPr.g_prime 0) (hPr.g_prime 1) (g_mem hPr h0) (g_mem hPr h1))
  have hi : ∀ i, ∏ P ∈ Pr.vG i, Formalism.L2.Col.qOf P = Pr.g i ^ X.f := fun i => by
    unfold Formalism.L2.Col.qOf
    rw [Finset.prod_congr rfl (g := fun _ => Pr.g i) (fun P hP => hPr.vG_norm i P hP), Finset.prod_const, hPr.vG_card]
  have hu : Pr.vGs = (Pr.vG 0).disjUnion (Pr.vG 1) hd := by
    ext w
    simp [Primes.vGs]
  rw [hu, Finset.prod_disjUnion, hi, hi, mul_pow]

/- English proof (translation)
The claim follows from `Nat.odd_iff.2 ((hPr.g_cong i).of_dvd h2)`.
-/
theorem odd_g (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (i : Fin 2) : Odd (Pr.g i) :=
  Nat.odd_iff.2 ((hPr.g_cong i).of_dvd h2)

/- English proof (translation)
Introduce `hP`. Take `⟨c, hc⟩` from `hPr.piT_cong u`. Take `⟨k, hk⟩` from `h2`. Establish `h1 : Pr.piT u - 1 ∈ P.asIdeal`. Rewrite using `[hc, hk]`.

Use `push_cast`. Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `Ideal.mul_mem_right _ _ hP`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (mem_of_mem_divs h) h1))`.
-/
theorem two_notMem_vT (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    (2 : 𝓞 X.E) ∉ P.asIdeal := by
  intro hP
  obtain ⟨c, hc⟩ := hPr.piT_cong u
  obtain ⟨k, hk⟩ := h2
  have h1 : Pr.piT u - 1 ∈ P.asIdeal := by
    rw [hc, hk]
    push_cast
    rw [mul_assoc, mul_assoc]
    exact Ideal.mul_mem_right _ _ hP
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (mem_of_mem_divs h) h1))

/- English proof (translation)
Take `⟨P, hP⟩ : (Pr.vT u).Nonempty` from `Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)`. Use `(hPr.T_prime u).odd_of_ne_two fun h => two_notMem_vT hPr h2 hP ?_` and prove the remaining obligations. Use `T_mem hPr hP` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this` after adjusting the coercions.
-/
theorem odd_typePrime_of_two_dvd_cond (hX : X.Ok) (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (u : Pr.Word) : Odd (Pr.T u) := by
  obtain ⟨P, hP⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  refine (hPr.T_prime u).odd_of_ne_two fun h => two_notMem_vT hPr h2 hP ?_
  have := T_mem hPr hP
  rw [h] at this
  exact_mod_cast this

/- English proof (translation)
Introduce and unpack `(h' | h')`. Break down `h with h | h` into its components or cases. Conclude with `false_of_isCoprime P (hPr.piT_cop u) (mem_of_mem_divs h) (mem_of_mem_divs h' :)`. Take `⟨i, hi⟩` from `exists_vG h`. Conclude with `hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) (natCast_mem_of_conjP (T_mem hPr h')) (g_mem hPr hi))`.

Take `⟨j, hj⟩` from `exists_vG h'`. Establish `hg` using `natCast_mem_of_conjP (g_mem hPr hj)`. Break down `h with h | h` into its components or cases. Conclude with `hPr.T_ne_g u j (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime j) (T_mem hPr h) hg)`. Take `⟨i, hi⟩` from `exists_vG h`.

Take `rfl : i = j` from `g_injective hPr (eq_of_natCast_mem P (hPr.g_prime i) (hPr.g_prime j) (g_mem hPr hi) hg)`. Establish `h1 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal` using `(mem_of_mem_divs hj :)`. Rewrite `h1` using `[cO_cO]`. Conclude with `false_of_isCoprime P (hPr.piG_cop i) h1 (mem_of_mem_divs hi)`.
-/
theorem conjP_notMem (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u ∨ P ∈ Pr.vGs) :
    ¬ (conjPrime₂ P ∈ Pr.vT u ∨ conjPrime₂ P ∈ Pr.vGs) := by
  rintro (h' | h')
  · rcases h with h | h
    · exact false_of_isCoprime P (hPr.piT_cop u) (mem_of_mem_divs h) (mem_of_mem_divs h' :)
    · obtain ⟨i, hi⟩ := exists_vG h
      exact hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i)
        (natCast_mem_of_conjP (T_mem hPr h')) (g_mem hPr hi))
  · obtain ⟨j, hj⟩ := exists_vG h'
    have hg := natCast_mem_of_conjP (g_mem hPr hj)
    rcases h with h | h
    · exact hPr.T_ne_g u j (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime j) (T_mem hPr h) hg)
    · obtain ⟨i, hi⟩ := exists_vG h
      obtain rfl : i = j := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime i) (hPr.g_prime j) (g_mem hPr hi) hg)
      have h1 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal := (mem_of_mem_divs hj :)
      rw [cO_cO] at h1
      exact false_of_isCoprime P (hPr.piG_cop i) h1 (mem_of_mem_divs hi)

/- English proof (translation)
Introduce `D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h`. Take `⟨⟨-, -, -, -, -, -, hX1, -, -, hPr, -, hc, -, -⟩, -, -, -, hmu, -⟩` from `h`. Substitute `hmu` using the available equality. Establish `hX` using `hX1.ok`. Establish `h2 : 2 ∣ Pr.cond`.

Rewrite using `[hc, NumDatum.cond]`. Conclude with `N.H.two_dvd_condN`. Establish `hS : ∀ P, P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u ↔ P ∈ Pr.vT u ∨ P ∈ Pr.vGs` using `fun P => by`. Rewrite using `[← rowSG_one sel Sg]`. Conclude with `Finset.mem_union`.

Use `⟨fun P hP => rowSG_one sel Sg ▸ hP, fun P hP => ?_, fun P hP => T_mem hPr hP, ?_, odd_typePrime_of_two_dvd_cond hX hPr h2 u, odd_g hPr h2, fun P hP => ⟨fun h' => conjP_notMem hPr u ((hS _).1 hP) ((hS _).1 h'), ?_⟩⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_vG hP`. Establish `hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal` using `fun hT => hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) hT (g_mem hPr hi))`. Use `⟨i, hi, hPr.vG_norm i P hi, g_mem hPr hi, (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2, fun hg => ?_, hT, fun hπ => hT (hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ hπ)⟩` and prove the remaining obligations. Use `g_injective hPr (eq_of_natCast_mem P (hPr.g_prime _) (hPr.g_prime _) hg (g_mem hPr hi))` as an intermediate fact.

Apply the tactic sequence `fin_cases i <;> simp at this`. Rewrite using `[Finset.prod_coe_sort _ (fun P => Formalism.L2.Col.qOf P), rowSG_one, prod_qOf_vGs hPr, GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm]`. Break down `(hS _).1 hP with h | h` into its components or cases. Conclude with `two_notMem_vT hPr h2 h`. Take `⟨i, hi⟩` from `exists_vG h`.

Introduce `hP2`. Use `eq_of_natCast_mem P (hPr.g_prime i) Nat.prime_two (g_mem hPr hi) (by exact_mod_cast hP2)` as an intermediate fact. Establish `ho` using `odd_g hPr h2 i`. Rewrite `ho` using `[this]`. Conclude with `absurd ho (by decide)`.
-/
theorem bad_primes : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ P ∈ rowSG Pr sel mu, P ∈ Pr.vGs) ∧ (∀ P ∈ Pr.vGs, ∃ i, P ∈ Pr.vG i ∧ Formalism.L2.Col.qOf P = Pr.g i ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ ((Pr.g (1 - i) : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ Pr.piT u ∉ P.asIdeal) ∧ (∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal) ∧ (∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) = (Pr.g 0 * Pr.g 1) ^ N.R.f ∧ Odd (Pr.T u) ∧ (∀ i, Odd (Pr.g i)) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (2 : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h
  obtain ⟨⟨-, -, -, -, -, -, hX1, -, -, hPr, -, hc, -, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  have hX := hX1.ok
  have h2 : 2 ∣ Pr.cond := by
    rw [hc, NumDatum.cond]
    exact N.H.two_dvd_condN
  have hS : ∀ P, P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u ↔ P ∈ Pr.vT u ∨ P ∈ Pr.vGs := fun P => by
    rw [← rowSG_one sel Sg]
    exact Finset.mem_union
  refine ⟨fun P hP => rowSG_one sel Sg ▸ hP, fun P hP => ?_, fun P hP => T_mem hPr hP, ?_, odd_typePrime_of_two_dvd_cond hX hPr h2 u,
    odd_g hPr h2, fun P hP => ⟨fun h' => conjP_notMem hPr u ((hS _).1 hP) ((hS _).1 h'), ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_vG hP
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun hT =>
      hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) hT (g_mem hPr hi))
    refine ⟨i, hi, hPr.vG_norm i P hi, g_mem hPr hi,
      (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2, fun hg => ?_, hT,
      fun hπ => hT (hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ hπ)⟩
    have := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime _) (hPr.g_prime _) hg (g_mem hPr hi))
    fin_cases i <;> simp at this
  · rw [Finset.prod_coe_sort _ (fun P => Formalism.L2.Col.qOf P), rowSG_one, prod_qOf_vGs hPr,
      GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm]
  · rcases (hS _).1 hP with h | h
    · exact two_notMem_vT hPr h2 h
    · obtain ⟨i, hi⟩ := exists_vG h
      intro hP2
      have := eq_of_natCast_mem P (hPr.g_prime i) Nat.prime_two (g_mem hPr hi) (by exact_mod_cast hP2)
      have ho := odd_g hPr h2 i
      rw [this] at ho
      exact absurd ho (by decide)

end GlobalTheory.ColNorms.BadPrimes
