import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.XiNeZeroOfIsStdGeneric
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX

namespace Formalism.IndefR.NX

section general

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce `hn`. Apply `hP` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h` using `Nat.gcd_eq_gcd_ab n g`. Rewrite `h` using `[hc.gcd_eq_one]`.

Establish `h' : (1 : 𝓞 E) = (n : 𝓞 E) * ((Nat.gcdA n g : ℤ) : 𝓞 E) + (g : 𝓞 E) * ((Nat.gcdB n g : ℤ) : 𝓞 E)`. Establish `h2` using `congrArg (Int.cast : ℤ → 𝓞 E) h`. Move the coercions through the operations in `at h2`. Conclude with `h2`. Rewrite using `[h']`.

Conclude with `P.add_mem (P.mul_mem_right _ hn) (P.mul_mem_right _ hg)`.
-/
theorem natCast_not_mem_of_coprime_g {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) {g n : ℕ} (hg : ((g : ℕ) : 𝓞 E) ∈ P)
    (hc : Nat.Coprime n g) : ((n : ℕ) : 𝓞 E) ∉ P := by
  intro hn
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h := Nat.gcd_eq_gcd_ab n g
  rw [hc.gcd_eq_one] at h
  have h' : (1 : 𝓞 E) = (n : 𝓞 E) * ((Nat.gcdA n g : ℤ) : 𝓞 E) + (g : 𝓞 E) * ((Nat.gcdB n g : ℤ) : 𝓞 E) := by
    have h2 := congrArg (Int.cast : ℤ → 𝓞 E) h
    push_cast at h2
    exact h2
  rw [h']
  exact P.add_mem (P.mul_mem_right _ hn) (P.mul_mem_right _ hg)

/- English proof (translation)
Establish `hmax : (Ideal.span {(g : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime g`. Establish `hlo : ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P.LiesOver (Ideal.span {(g : ℤ)}) ↔ ((g : ℕ) : 𝓞 E) ∈ P`. Introduce `P hP`. Rewrite using `[Ideal.liesOver_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hg : (g : ℤ) ∈ P.under ℤ` using `h ▸ Ideal.mem_span_singleton_self _`. Rewrite `hg` using `[Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `hg`. Introduce `h`.

Establish `hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `h`. Conclude with `hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle`. Establish `hne0 : ((g : ℕ) : 𝓞 E) ≠ 0`.

Introduce `h`. Establish `: ((g : ℕ) : E) = 0`. Use `congrArg (fun x : 𝓞 E => (x : E)) h` as an intermediate fact. Simplify using `using this`. Conclude with `(Fact.out : g.Prime).ne_zero (by exact_mod_cast this)`.

Use extensionality with `P`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hl⟩`. Establish `hg : ((g : ℕ) : 𝓞 E) ∈ P` using `(hlo P).mp hl`.

Establish `hne : P ≠ ⊥` using `fun h => hne0 (by rw [h] at hg; exact hg)`. Conclude with `⟨⟨P, hP, hne⟩, hg, rfl⟩`. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨v.isPrime, (hlo v.asIdeal).mpr hv⟩`.
-/
theorem primesOver_eq_places (g : ℕ) [Fact g.Prime] :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) =
      (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' {v | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime g
  have hlo : ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P.LiesOver (Ideal.span {(g : ℤ)}) ↔ ((g : ℕ) : 𝓞 E) ∈ P := by
    intro P hP
    rw [Ideal.liesOver_iff]
    constructor
    · intro h
      have hg : (g : ℤ) ∈ P.under ℤ := h ▸ Ideal.mem_span_singleton_self _
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at hg
      exact hg
    · intro h
      have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap, map_natCast]
        exact h
      exact hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle
  have hne0 : ((g : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((g : ℕ) : E) = 0 := by
      have := congrArg (fun x : 𝓞 E => (x : E)) h
      simpa using this
    exact (Fact.out : g.Prime).ne_zero (by exact_mod_cast this)
  ext P
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hP, hl⟩
    have hg : ((g : ℕ) : 𝓞 E) ∈ P := (hlo P).mp hl
    have hne : P ≠ ⊥ := fun h => hne0 (by rw [h] at hg; exact hg)
    exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, (hlo v.asIdeal).mpr hv⟩

/- English proof (translation)
Establish `: Fact g.Prime` using `⟨hg⟩`. Use `set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def`. Establish `: p.IsMaximal` using `Int.ideal_span_isMaximal_of_prime g`. Establish `hfin : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).Finite`. Apply `Set.finite_of_ncard_pos` to reduce the goal to its premises.

Rewrite using `[hsplit]`. Conclude with `Module.finrank_pos`. Establish `hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)` using `fun a b h => HeightOneSpectrum.ext h`. Establish `hPO` using `primesOver_eq_places (E := E) g`. Establish `hfin' : (p.primesOver (𝓞 E)).Finite` using `by rw [hPO]; exact hfin.image _`.

Set `_ : Fintype (p.primesOver (𝓞 E))` to `hfin'.fintype`. Establish `hcard : Fintype.card (p.primesOver (𝓞 E)) = Module.finrank ℚ E`. Rewrite using `[← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', hPO, Set.ncard_image_of_injective _ hinj, hsplit]`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)`. Rewrite `hsum` using `[NumberField.RingOfIntegers.rank]`.

Establish `hle : ∀ q ∈ (Finset.univ : Finset (p.primesOver (𝓞 E))), (1 : ℕ) ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ`. Introduce `q _`. Use `q.2.1` as an intermediate fact. Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')`. Establish `hones : ∑ q : p.primesOver (𝓞 E), (1 : ℕ) = ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ`.

Rewrite using `[hsum, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, hcard]`. Establish `hall` using `(Finset.sum_eq_sum_iff_of_le hle).mp hones`. Establish `hwmem : w.asIdeal ∈ p.primesOver (𝓞 E)`. Rewrite using `[hPO]`. Conclude with `⟨w, hw, rfl⟩`.

Establish `h1` using `hall ⟨w.asIdeal, hwmem⟩ (Finset.mem_univ _)`. Establish `hf : w.asIdeal.inertiaDeg ℤ = 1` using `Nat.eq_one_of_mul_eq_one_left h1.symm`. Establish `: w.asIdeal.LiesOver p` using `hwmem.2`. Establish `hpow` using `Ideal.pow_inertiaDeg g w.asIdeal`. Rewrite `hpow` using `[hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Conclude with `hpow.symm`.
-/
theorem card_residue_of_split (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hsplit : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).ncard = Module.finrank ℚ E)
    (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) : Nat.card (𝓞 E ⧸ w.asIdeal) = g := by
  classical
  have : Fact g.Prime := ⟨hg⟩
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have : p.IsMaximal := Int.ideal_span_isMaximal_of_prime g
  have hfin : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).Finite := by
    apply Set.finite_of_ncard_pos
    rw [hsplit]; exact Module.finrank_pos
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) :=
    fun a b h => HeightOneSpectrum.ext h
  have hPO := primesOver_eq_places (E := E) g
  have hfin' : (p.primesOver (𝓞 E)).Finite := by rw [hPO]; exact hfin.image _
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin'.fintype
  have hcard : Fintype.card (p.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', hPO, Set.ncard_image_of_injective _ hinj, hsplit]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hle : ∀ q ∈ (Finset.univ : Finset (p.primesOver (𝓞 E))),
      (1 : ℕ) ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    have := q.2.1
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hones : ∑ q : p.primesOver (𝓞 E), (1 : ℕ) =
      ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [hsum, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, hcard]
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hones
  have hwmem : w.asIdeal ∈ p.primesOver (𝓞 E) := by
    rw [hPO]; exact ⟨w, hw, rfl⟩
  have h1 := hall ⟨w.asIdeal, hwmem⟩ (Finset.mem_univ _)
  have hf : w.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left h1.symm
  have : w.asIdeal.LiesOver p := hwmem.2
  have hpow := Ideal.pow_inertiaDeg g w.asIdeal
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpow
  exact hpow.symm

/- English proof (translation)
Use `haveI := Fact.mk hg`. Establish `hwt : w.asIdeal ≠ ⊤` using `w.isPrime.ne_top`. Assume the negation of the conclusion as `hne`. Establish `hab : x.val ≠ y.val` using `fun h' => hne (ZMod.val_injective g h')`. Establish `hxg` using `ZMod.val_lt x`.

Establish `hyg` using `ZMod.val_lt y`. Break down `Nat.lt_or_ge x.val y.val with hlt | hle` into its components or cases. Establish `hmem : (((y.val - x.val : ℕ)) : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[Nat.cast_sub hlt.le, ← neg_sub]`. Conclude with `w.asIdeal.neg_mem h`.

Establish `hcop : Nat.Coprime (y.val - x.val) g` using `(Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm`. Conclude with `natCast_not_mem_of_coprime_g hwt hw hcop hmem`. Establish `hmem : (((x.val - y.val : ℕ)) : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[Nat.cast_sub hle]`. Conclude with `h`.

Establish `hcop : Nat.Coprime (x.val - y.val) g` using `(Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm`. Conclude with `natCast_not_mem_of_coprime_g hwt hw hcop hmem`.
-/
private theorem zmod_eq_of_val_sub_mem_prime (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E)) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {x y : ZMod g} (h : ((x.val : ℕ) : 𝓞 E) - ((y.val : ℕ) : 𝓞 E) ∈ w.asIdeal) : x = y := by
  haveI := Fact.mk hg
  have hwt : w.asIdeal ≠ ⊤ := w.isPrime.ne_top
  by_contra hne
  have hab : x.val ≠ y.val := fun h' => hne (ZMod.val_injective g h')
  have hxg := ZMod.val_lt x
  have hyg := ZMod.val_lt y
  rcases Nat.lt_or_ge x.val y.val with hlt | hle
  · have hmem : (((y.val - x.val : ℕ)) : 𝓞 E) ∈ w.asIdeal := by
      rw [Nat.cast_sub hlt.le, ← neg_sub]
      exact w.asIdeal.neg_mem h
    have hcop : Nat.Coprime (y.val - x.val) g :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm
    exact natCast_not_mem_of_coprime_g hwt hw hcop hmem
  · have hmem : (((x.val - y.val : ℕ)) : 𝓞 E) ∈ w.asIdeal := by
      rw [Nat.cast_sub hle]
      exact h
    have hcop : Nat.Coprime (x.val - y.val) g :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm
    exact natCast_not_mem_of_coprime_g hwt hw hcop hmem

/- English proof (translation)
Use `haveI := Fact.mk hg`. Establish `hcard` using `card_residue_of_split g hg w hsplit hw`. Use `haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hg.ne_zero)`. Set `f : ZMod g → 𝓞 E ⧸ w.asIdeal` to `fun x => Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E)`. Establish `hinj : Function.Injective f`.

Introduce `x y hxy`. Conclude with `zmod_eq_of_val_sub_mem_prime g hg w hw (Ideal.Quotient.eq.1 hxy)`. Establish `hbij` using `hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])`. Take `⟨x, hx⟩` from `hbij.2 y`. Conclude with `⟨x, hx⟩`.
-/
theorem exists_zmod_residue (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hsplit : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).ncard = Module.finrank ℚ E)
    (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (y : 𝓞 E ⧸ w.asIdeal) :
    ∃ x : ZMod g, Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E) = y := by
  haveI := Fact.mk hg
  have hcard := card_residue_of_split g hg w hsplit hw
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hg.ne_zero)
  let f : ZMod g → 𝓞 E ⧸ w.asIdeal := fun x => Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact zmod_eq_of_val_sub_mem_prime g hg w hw (Ideal.Quotient.eq.1 hxy)
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨x, hx⟩

end general

section record

variable (D : D7)

/- English proof (translation)
Establish `h : D.host.sqrtMinusD ^ 2 = (((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[Host.sqrtMinusD_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `IsIntegral.of_pow (by norm_num : 0 < 2) (h ▸ RingOfIntegers.isIntegral_coe _)`.
-/
theorem isIntegral_sqrtMinusD : IsIntegral ℤ D.host.sqrtMinusD := by
  have h : D.host.sqrtMinusD ^ 2 = (((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) := by
    rw [Host.sqrtMinusD_sq]; push_cast; ring
  exact IsIntegral.of_pow (by norm_num : 0 < 2) (h ▸ RingOfIntegers.isIntegral_coe _)

def sqrtO : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, isIntegral_sqrtMinusD D⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_sqrtO : ((sqrtO D : 𝓞 D.host.E) : D.host.E) = D.host.sqrtMinusD :=
  rfl

/- English proof (translation)
Introduce `h0`. Establish `hsq` using `Host.sqrtMinusD_sq D.host`. Rewrite `hsq` using `[h0]`. Establish `hd0 : (D.host.d : D.host.E) ≠ 0` using `Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero`. Apply `hd0` to reduce the goal to its premises.

Establish `: -(D.host.d : D.host.E) = 0` using `by rw [← hsq]; ring`. Simplify using `using this`.
-/
theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h0
  have hsq := Host.sqrtMinusD_sq D.host
  rw [h0] at hsq
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero
  apply hd0
  have : -(D.host.d : D.host.E) = 0 := by rw [← hsq]; ring
  simpa using this

def xiDen : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) * sqrtO D

/- English proof (translation)
Establish `hN : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `D.host.ccK_ne_bot`. Establish `hs` using `sqrtMinusD_ne_zero D`. Express the relevant statement in the definitionally equal form `D.host.xi0 * (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) * D.host.sqrtMinusD) = -1`.

Rewrite using `[Host.xi0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem imaginary_generator_mul_denominator : D.host.xi0 * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -1 := by
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact D.host.ccK_ne_bot
  have hs := sqrtMinusD_ne_zero D
  change D.host.xi0 * (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) * D.host.sqrtMinusD) = -1
  rw [Host.xi0]
  field_simp

/- English proof (translation)
The claim follows from `D.naut.plGw_over kv.1 kv.2`.
-/
theorem g_mem_pG (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (pG D kv).asIdeal :=
  D.naut.plGw_over kv.1 kv.2

/- English proof (translation)
The claim follows from `D.host.ccK_coprime _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (D.host.g_level k))))))`.
-/
theorem coprime_normK_g (k : Fin 2) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) :=
  D.host.ccK_coprime _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (D.host.g_level k))))))

/- English proof (translation)
Establish `h` using `D.ntypes.g_cond k`. Establish `hdvd : D.host.d ∣ D.host.QS * D.host.q * D.host.d` using `Dvd.intro_left _ rfl`. Establish `hmod : D.host.g k % D.host.d = 1 % D.host.d`. Rewrite using `[← Nat.mod_mod_of_dvd _ hdvd, h]`. Rewrite using `[Nat.Coprime, Nat.gcd_rec, hmod, ← Nat.gcd_rec]`.

Conclude with `Nat.gcd_one_right _`.
-/
theorem coprime_d_g (k : Fin 2) : Nat.Coprime D.host.d (D.host.g k) := by
  have h := D.ntypes.g_cond k
  have hdvd : D.host.d ∣ D.host.QS * D.host.q * D.host.d := Dvd.intro_left _ rfl
  have hmod : D.host.g k % D.host.d = 1 % D.host.d := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, h]
  rw [Nat.Coprime, Nat.gcd_rec, hmod, ← Nat.gcd_rec]
  exact Nat.gcd_one_right _

/- English proof (translation)
Establish `hP : (pG D kv).asIdeal.IsPrime` using `(pG D kv).isPrime`. Establish `hg` using `g_mem_pG D kv`. Establish `hN` using `natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_normK_g D kv.1)`. Establish `hd` using `natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_d_g D kv.1)`. Establish `hs : sqrtO D ∉ (pG D kv).asIdeal`.

Introduce `hs`. Apply `hd` to reduce the goal to its premises. Establish `h2 : sqrtO D * sqrtO D ∈ (pG D kv).asIdeal` using `(pG D kv).asIdeal.mul_mem_left _ hs`. Establish `he : sqrtO D * sqrtO D = -((D.host.d : ℕ) : 𝓞 D.host.E)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Use `push_cast`. Express the relevant statement in the definitionally equal form `D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E)`. Rewrite using `[← sq, Host.sqrtMinusD_sq]`. Rewrite `h2` using `[he]`. Simplify using `using (pG D kv).asIdeal.neg_mem_iff.mp h2`.

Introduce `hc`. Break down `hP.mem_or_mem hc with h | h` into its components or cases. Conclude with `hN h`. Conclude with `hs h`.
-/
theorem xiDen_not_mem (kv : Σ k : Fin 2, D.nd.PlG k) : xiDen D ∉ (pG D kv).asIdeal := by
  have hP : (pG D kv).asIdeal.IsPrime := (pG D kv).isPrime
  have hg := g_mem_pG D kv
  have hN := natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_normK_g D kv.1)
  have hd := natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_d_g D kv.1)
  have hs : sqrtO D ∉ (pG D kv).asIdeal := by
    intro hs
    apply hd
    have h2 : sqrtO D * sqrtO D ∈ (pG D kv).asIdeal := (pG D kv).asIdeal.mul_mem_left _ hs
    have he : sqrtO D * sqrtO D = -((D.host.d : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      push_cast
      change D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E)
      rw [← sq, Host.sqrtMinusD_sq]
    rw [he] at h2
    simpa using (pG D kv).asIdeal.neg_mem_iff.mp h2
  intro hc
  rcases hP.mem_or_mem hc with h | h
  · exact hN h
  · exact hs h

/- English proof (translation)
Establish `: (pG D kv).asIdeal.IsMaximal` using `(pG D kv).isMaximal`. Set `_ : Field (𝓞 D.host.E ⧸ (pG D kv).asIdeal)` to `Ideal.Quotient.field _`. Establish `hc` using `xiDen_not_mem D kv`. Establish `hcq : Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis.

Take `⟨x, hx⟩` from `exists_zmod_residue (D.host.g kv.1) (D.host.g_prime kv.1) (pG D kv) (D.nd.g_split kv.1) (g_mem_pG D kv) (Ideal.Quotient.mk (pG D kv).asIdeal (-1) * (Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D))⁻¹)`. Use `⟨x, -1, xiDen D, hc, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `imaginary_generator_mul_denominator D`. Use `push_cast`. Conclude with `h1.symm`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hx, mul_assoc, inv_mul_cancel₀ hcq, mul_one, sub_self]`.
-/
theorem xiRed_cond (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ x : ZMod (D.host.g kv.1), ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
      ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal := by
  classical
  have : (pG D kv).asIdeal.IsMaximal := (pG D kv).isMaximal
  let _ : Field (𝓞 D.host.E ⧸ (pG D kv).asIdeal) := Ideal.Quotient.field _
  have hc := xiDen_not_mem D kv
  have hcq : Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨x, hx⟩ := exists_zmod_residue (D.host.g kv.1) (D.host.g_prime kv.1) (pG D kv) (D.nd.g_split kv.1)
    (g_mem_pG D kv) (Ideal.Quotient.mk (pG D kv).asIdeal (-1) * (Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D))⁻¹)
  refine ⟨x, -1, xiDen D, hc, ?_, ?_⟩
  · have h1 := imaginary_generator_mul_denominator D
    push_cast
    exact h1.symm
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hx, mul_assoc, inv_mul_cancel₀ hcq, mul_one, sub_self]

/- English proof (translation)
Introduce `h0`. Establish `hP` using `xiRed_cond D kv`. Establish `hx : xiRed D kv = hP.choose`. Unfold `Formalism.L2.NX.xiRed`. Rewrite using `[dif_pos hP]`.

Take `⟨a, c, hc, hac, hmem⟩` from `hP.choose_spec`. Rewrite `hmem` using `[← hx, h0, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_sub]`. Establish `ha : a ∈ (pG D kv).asIdeal` using `by simpa using (pG D kv).asIdeal.neg_mem hmem`. Establish `h1 : a * xiDen D = -c`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises.

Use `show (a : D.host.E) * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -(c : D.host.E)`. Rewrite using `[hac, mul_comm D.host.xi0, mul_assoc, imaginary_generator_mul_denominator, mul_neg_one]`. Apply `hc` to reduce the goal to its premises. Establish `h2 : -c ∈ (pG D kv).asIdeal`. Rewrite using `[← h1]`.

Conclude with `(pG D kv).asIdeal.mul_mem_right _ ha`. Simplify using `using (pG D kv).asIdeal.neg_mem h2`.
-/
theorem xiRed_ne_zero (kv : Σ k : Fin 2, D.nd.PlG k) : xiRed D kv ≠ 0 := by
  intro h0
  have hP := xiRed_cond D kv
  have hx : xiRed D kv = hP.choose := by
    unfold Formalism.L2.NX.xiRed
    rw [dif_pos hP]
  obtain ⟨a, c, hc, hac, hmem⟩ := hP.choose_spec
  rw [← hx, h0, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_sub] at hmem
  have ha : a ∈ (pG D kv).asIdeal := by simpa using (pG D kv).asIdeal.neg_mem hmem
  have h1 : a * xiDen D = -c := by
    apply NumberField.RingOfIntegers.ext
    show (a : D.host.E) * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -(c : D.host.E)
    rw [hac, mul_comm D.host.xi0, mul_assoc, imaginary_generator_mul_denominator, mul_neg_one]
  apply hc
  have h2 : -c ∈ (pG D kv).asIdeal := by
    rw [← h1]
    exact (pG D kv).asIdeal.mul_mem_right _ ha
  simpa using (pG D kv).asIdeal.neg_mem h2

def IsXiRes (kv : Σ k : Fin 2, D.nd.PlG k) (x : ZMod (D.host.g kv.1)) : Prop :=
  ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
    ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal

/- English proof (translation)
Establish `hP` using `xiRed_cond D kv`. Establish `hx : xiRed D kv = hP.choose`. Unfold `Formalism.L2.NX.xiRed`. Rewrite using `[dif_pos hP]`. Rewrite using `[hx]`.

Conclude with `hP.choose_spec`.
-/
theorem xiRed_isXiRes (kv : Σ k : Fin 2, D.nd.PlG k) : IsXiRes D kv (xiRed D kv) := by
  have hP := xiRed_cond D kv
  have hx : xiRed D kv = hP.choose := by
    unfold Formalism.L2.NX.xiRed
    rw [dif_pos hP]
  rw [hx]
  exact hP.choose_spec

/- English proof (translation)
Introduce `kv` and use `xiRed_ne_zero D kv`.
-/
theorem xiRedNZ (D : D7) : XiRedNZ D :=
  fun kv => xiRed_ne_zero D kv

end record

end Formalism.IndefR.NX
