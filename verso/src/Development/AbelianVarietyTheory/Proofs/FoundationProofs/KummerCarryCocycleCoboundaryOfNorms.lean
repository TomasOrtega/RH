import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter

open GlobalTheory.NeedB Polynomial
open scoped IntermediateField

namespace GlobalTheory.NeedB.NormCob

/- English proof (translation)
Establish `h1 : y 1 = 0`. Use `hy 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `left_eq_add.mp this`. Proceed by induction on `q with`.

Consider the case `zero => simp [h1]`. Consider the case `succ q ih => rw [pow_succ, hy, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hom_pow {G : Type*} [Group G] {N : ℕ} (y : G → ZMod N) (hy : ∀ g h, y (g * h) = y g + y h) (σ : G) (q : ℕ) :
    y (σ ^ q) = q * y σ := by
  have h1 : y 1 = 0 := by
    have := hy 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  induction q with
  | zero => simp [h1]
  | succ q ih => rw [pow_succ, hy, ih]; push_cast; ring

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `h1 : y 1 = 0` using `by simpa using hom_pow y hy 1 0`. Establish `hex : ∃ m : ℕ, 0 < m ∧ ∃ g, y g = m` using `⟨N, hN, 1, by simp [h1]⟩`. Take `⟨hm, σ, hσ⟩` from `Nat.find_spec hex`. Use `set m := Nat.find hex with hmdef`.

Establish `key : ∀ n : ℕ, (∃ g, y g = n) → m ∣ n`. Introduce and unpack `n ⟨g, hg⟩`. Assume the negation of the conclusion as `hnd`. Establish `hr : 0 < n % m` using `Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)`. Use `Nat.find_min hex (Nat.mod_lt n hm) ⟨hr, g * (σ ^ (n / m))⁻¹, ?_⟩` and prove the remaining obligations.

Establish `h2` using `hy (g * (σ ^ (n / m))⁻¹) (σ ^ (n / m))`. Rewrite `h2` using `[inv_mul_cancel_right, hg, hom_pow y hy, hσ]`. Establish `h3 : (n : ZMod N) = ((n % m : ℕ) : ZMod N) + ((n / m : ℕ) : ZMod N) * m` using `by conv_lhs => rw [← Nat.mod_add_div' n m] push_cast; ring`. Conclude with `(add_right_cancel (h2.symm.trans h3))`. Take `⟨d, hd⟩` from `key N ⟨1, by simp [h1]⟩`.

Conclude with `⟨d, m, σ, hm, hd.symm, hσ, fun g => key _ ⟨g, by simp⟩⟩`.
-/
theorem exists_generator {G : Type*} [Group G] {N : ℕ} (hN : 0 < N) (y : G → ZMod N)
    (hy : ∀ g h, y (g * h) = y g + y h) :
    ∃ (d m : ℕ) (σ : G), 0 < m ∧ m * d = N ∧ y σ = m ∧ ∀ g, m ∣ (y g).val := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  have h1 : y 1 = 0 := by simpa using hom_pow y hy 1 0
  have hex : ∃ m : ℕ, 0 < m ∧ ∃ g, y g = m := ⟨N, hN, 1, by simp [h1]⟩
  obtain ⟨hm, σ, hσ⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  have key : ∀ n : ℕ, (∃ g, y g = n) → m ∣ n := by
    rintro n ⟨g, hg⟩
    by_contra hnd
    have hr : 0 < n % m := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    refine Nat.find_min hex (Nat.mod_lt n hm) ⟨hr, g * (σ ^ (n / m))⁻¹, ?_⟩
    have h2 := hy (g * (σ ^ (n / m))⁻¹) (σ ^ (n / m))
    rw [inv_mul_cancel_right, hg, hom_pow y hy, hσ] at h2
    have h3 : (n : ZMod N) = ((n % m : ℕ) : ZMod N) + ((n / m : ℕ) : ZMod N) * m := by
      conv_lhs => rw [← Nat.mod_add_div' n m]
      push_cast; ring
    exact (add_right_cancel (h2.symm.trans h3))
  obtain ⟨d, hd⟩ := key N ⟨1, by simp [h1]⟩
  exact ⟨d, m, σ, hm, hd.symm, hσ, fun g => key _ ⟨g, by simp⟩⟩

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/- English proof (translation)
Establish `: (g : Ω →ₐ[K] Ω).comp K⟮β⟯.val = (g' : Ω →ₐ[K] Ω).comp K⟮β⟯.val`. Apply `IntermediateField.adjoin_algHom_ext` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality.

Conclude with `h`. Conclude with `DFunLike.congr_fun this x`.
-/
theorem agree {β : Ω} {g g' : Ω ≃ₐ[K] Ω} (h : g β = g' β) (x : K⟮β⟯) : g x = g' x := by
  have : (g : Ω →ₐ[K] Ω).comp K⟮β⟯.val = (g' : Ω →ₐ[K] Ω).comp K⟮β⟯.val := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h
  exact DFunLike.congr_fun this x

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K`. Use `haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic`. Use `haveI : FiniteDimensional K K⟮β⟯ := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)`. Rewrite using `[Algebra.norm_eq_prod_embeddings K Ω γ]`. Use `symm`.

Use `Finset.prod_bij (fun j _ => ((σ ^ j : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp K⟮β⟯.val) (by simp) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj hij`. Conclude with `hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) (DFunLike.congr_fun hij (IntermediateField.AdjoinSimple.gen K β))`. Introduce `τ _`. Take `⟨φ, hφ⟩` from `IntermediateField.exists_algHom_of_splits (F := K) (E := Ω) (K := Ω) (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) τ`.

Set `g : Ω ≃ₐ[K] Ω` to `AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)`. Take `⟨j, hj, hg⟩` from `hsurj g`. Use `⟨j, Finset.mem_range.mpr hj, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ]`. Use extensionality with `x`.

Conclude with `(agree hg x).symm`. Introduce `j _`. Both sides reduce to the same expression.
-/
theorem norm_eq_prod [CharZero K] [IsAlgClosure K Ω] {β : Ω} (σ : Ω ≃ₐ[K] Ω) (d : ℕ)
    (hinj : ∀ i < d, ∀ j < d, (σ ^ i) β = (σ ^ j) β → i = j)
    (hsurj : ∀ g : Ω ≃ₐ[K] Ω, ∃ j < d, g β = (σ ^ j) β) (γ : K⟮β⟯) :
    algebraMap K Ω (Algebra.norm K γ) = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  rw [Algebra.norm_eq_prod_embeddings K Ω γ]
  symm
  refine Finset.prod_bij (fun j _ => ((σ ^ j : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp K⟮β⟯.val) (by simp) ?_ ?_ ?_
  · intro i hi j hj hij
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      (DFunLike.congr_fun hij (IntermediateField.AdjoinSimple.gen K β))
  · intro τ _
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := K) (E := Ω) (K := Ω)
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) τ
    let g : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    obtain ⟨j, hj, hg⟩ := hsurj g
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [← hφ]
    ext x
    exact (agree hg x).symm
  · intro j _
    rfl

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hβ` using `[zero_pow hN.ne']`. Conclude with `hb ((map_eq_zero _).mp hβ.symm)`. Take `⟨hlc, hdef, hhom, -⟩` from `GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩`. Use `set y := kum (N := N) (K := K) ζ β with hydef`. Take `⟨d, m, σ, hm, hmd, hσ, hdvd⟩` from `exists_generator hN y hhom`.

Establish `hpow : ∀ j : ℕ, y (σ ^ j) = ((m * j : ℕ) : ZMod N)` using `fun j => by`. Rewrite using `[hom_pow y hhom, hσ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : ∀ g, (y g).val = m * ((y g).val / m)` using `fun g => (Nat.mul_div_cancel' (hdvd g)).symm`.

Establish `hlt : ∀ g, (y g).val / m < d` using `fun g => by`. Apply `Nat.div_lt_of_lt_mul` to reduce the goal to its premises. Rewrite using `[hmd]`. Conclude with `ZMod.val_lt _`. Establish `hyk : ∀ g, y g = y (σ ^ ((y g).val / m))` using `fun g => by`.

Rewrite using `[hpow, ← hval, ZMod.natCast_zmod_val]`. Establish `hag : ∀ g g', y g = y g' → g β = g' β` using `fun g g' h => by rw [hdef g, hdef g', h]`. Use `haveI : FiniteDimensional K K⟮β⟯ := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)`. Take `⟨γ, hγ⟩` from `hnorm K⟮β⟯ inferInstance a ha`. Establish `hγ0 : (γ : Ω) ≠ 0`.

Introduce `h`. Establish `: γ = 0` using `Subtype.ext h`. Rewrite `hγ` using `[this, Algebra.norm_zero]`. Conclude with `ha hγ.symm`. Establish `hprod : algebraMap K Ω a = ∏ j ∈ Finset.range d, (σ ^ j) γ`.

Rewrite using `[← hγ]`. Use `norm_eq_prod σ d ?_ (fun g => ⟨_, hlt g, hag _ _ (hyk g)⟩) γ` and prove the remaining obligations. Introduce `i hi j hj hij`. Establish `hi' : m * i < N` using `hmd ▸ Nat.mul_lt_mul_of_pos_left hi hm`. Establish `hj' : m * j < N` using `hmd ▸ Nat.mul_lt_mul_of_pos_left hj hm`.

Rewrite `hij` using `[hdef, hdef (σ ^ j), hpow, hpow, ZMod.val_cast_of_lt hi', ZMod.val_cast_of_lt hj']`. Conclude with `Nat.eq_of_mul_eq_mul_left hm (hζ.pow_inj hi' hj' (mul_right_cancel₀ hβ0 hij))`. Set `P : ℕ → Ω` to `fun n => ∏ j ∈ Finset.range n, (σ ^ j) γ`. Establish `hP0 : ∀ n, P n ≠ 0` using `fun n => Finset.prod_ne_zero_iff.mpr fun j _ => (_root_.map_ne_zero _).mpr hγ0`. Establish `hPadd : ∀ (g : Ω ≃ₐ[K] Ω) (i n : ℕ), y g = y (σ ^ i) → P i * g (P n) = P (i + n)`.

Introduce `g i n hg`. Simplify using `only [P]`. Rewrite using `[Finset.prod_range_add, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `: y (g * σ ^ j) = y (σ ^ (i + j))` using `by rw [pow_add, hhom, hhom, hg]`. Conclude with `agree (hag _ _ this) γ`. Establish `hPd : ∀ r, P (d + r) = algebraMap K Ω a * P r`. Introduce `r`. Establish `h1 : y 1 = y (σ ^ d)`.

Rewrite using `[hpow, hmd, ← pow_zero σ, hpow]`. Simplify using the standard rewrite rules. Rewrite using `[← hPadd 1 d r h1, hprod]`. Both sides reduce to the same expression. Use `⟨fun g => Units.mk0 (P ((y g).val / m)) (hP0 _), hlc.comp (fun z : ZMod N => Units.mk0 (P (z.val / m)) (hP0 _)), fun g h => ?_⟩` and prove the remaining obligations.

Simplify using `only [Units.val_mk0]`. Rewrite using `[hPadd g _ _ (hyk g), hhom, ZMod.val_add]`. Establish `hg` using `hlt g`. Establish `hh` using `hlt h`. Rewrite using `[hval g, hval h, ← mul_add, Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]`.

Generalize the expression as in `(y g).val / m = i at *`. Generalize the expression as in `(y h).val / m = j at *`. Distinguish the cases in `hij : i + j < d`. Establish `: m * (i + j) < N` using `hmd ▸ Nat.mul_lt_mul_of_pos_left hij hm`. Rewrite using `[Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, mul_comm]`.

Take `⟨r, hr⟩ : ∃ r, i + j = d + r` from `⟨i + j - d, by omega⟩`. Establish `hrd : r < d` using `by omega`. Establish `: m * r < N` using `hmd ▸ Nat.mul_lt_mul_of_pos_left hrd hm`. Rewrite using `[hr, mul_add, hmd, Nat.add_mod_left, Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, hPd, pow_add, hα]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem carry_coboundary : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨hlc, hdef, hhom, -⟩ := GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  set y := kum (N := N) (K := K) ζ β with hydef
  obtain ⟨d, m, σ, hm, hmd, hσ, hdvd⟩ := exists_generator hN y hhom
  have hpow : ∀ j : ℕ, y (σ ^ j) = ((m * j : ℕ) : ZMod N) := fun j => by
    rw [hom_pow y hhom, hσ]; push_cast; ring
  have hval : ∀ g, (y g).val = m * ((y g).val / m) := fun g => (Nat.mul_div_cancel' (hdvd g)).symm
  have hlt : ∀ g, (y g).val / m < d := fun g => by
    apply Nat.div_lt_of_lt_mul
    rw [hmd]; exact ZMod.val_lt _
  have hyk : ∀ g, y g = y (σ ^ ((y g).val / m)) := fun g => by
    rw [hpow, ← hval, ZMod.natCast_zmod_val]
  have hag : ∀ g g', y g = y g' → g β = g' β := fun g g' h => by rw [hdef g, hdef g', h]
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  obtain ⟨γ, hγ⟩ := hnorm K⟮β⟯ inferInstance a ha
  have hγ0 : (γ : Ω) ≠ 0 := by
    intro h
    have : γ = 0 := Subtype.ext h
    rw [this, Algebra.norm_zero] at hγ
    exact ha hγ.symm
  have hprod : algebraMap K Ω a = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
    rw [← hγ]
    refine norm_eq_prod σ d ?_ (fun g => ⟨_, hlt g, hag _ _ (hyk g)⟩) γ
    intro i hi j hj hij
    have hi' : m * i < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hi hm
    have hj' : m * j < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hj hm
    rw [hdef, hdef (σ ^ j), hpow, hpow, ZMod.val_cast_of_lt hi', ZMod.val_cast_of_lt hj'] at hij
    exact Nat.eq_of_mul_eq_mul_left hm (hζ.pow_inj hi' hj' (mul_right_cancel₀ hβ0 hij))
  let P : ℕ → Ω := fun n => ∏ j ∈ Finset.range n, (σ ^ j) γ
  have hP0 : ∀ n, P n ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun j _ => (_root_.map_ne_zero _).mpr hγ0
  have hPadd : ∀ (g : Ω ≃ₐ[K] Ω) (i n : ℕ), y g = y (σ ^ i) → P i * g (P n) = P (i + n) := by
    intro g i n hg
    simp only [P]
    rw [Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have : y (g * σ ^ j) = y (σ ^ (i + j)) := by rw [pow_add, hhom, hhom, hg]
    exact agree (hag _ _ this) γ
  have hPd : ∀ r, P (d + r) = algebraMap K Ω a * P r := by
    intro r
    have h1 : y 1 = y (σ ^ d) := by
      rw [hpow, hmd, ← pow_zero σ, hpow]; simp
    rw [← hPadd 1 d r h1, hprod]
    rfl
  refine ⟨fun g => Units.mk0 (P ((y g).val / m)) (hP0 _),
    hlc.comp (fun z : ZMod N => Units.mk0 (P (z.val / m)) (hP0 _)), fun g h => ?_⟩
  simp only [Units.val_mk0]
  rw [hPadd g _ _ (hyk g), hhom, ZMod.val_add]
  have hg := hlt g
  have hh := hlt h
  rw [hval g, hval h, ← mul_add, Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]
  generalize (y g).val / m = i at *
  generalize (y h).val / m = j at *
  by_cases hij : i + j < d
  · have : m * (i + j) < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hij hm
    rw [Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, mul_comm]
  · obtain ⟨r, hr⟩ : ∃ r, i + j = d + r := ⟨i + j - d, by omega⟩
    have hrd : r < d := by omega
    have : m * r < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hrd hm
    rw [hr, mul_add, hmd, Nat.add_mod_left, Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, hPd, pow_add, hα]
    ring

end GlobalTheory.NeedB.NormCob
