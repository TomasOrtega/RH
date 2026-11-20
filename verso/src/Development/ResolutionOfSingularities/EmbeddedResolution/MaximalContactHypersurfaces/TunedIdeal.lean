import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal

namespace FunctorialResolution.EmbeddedResolution

def tuningWeight (m : ℕ) (c : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range m, (m - j) * c j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tuningWeight_eq_sum (m : ℕ) (c : ℕ → ℕ) :
    tuningWeight m c = ∑ j ∈ Finset.range m, (m - j) * c j := rfl

/- English proof (translation)
Simplify using `[tuningWeight, Nat.mul_add, Finset.sum_add_distrib]`.
-/
theorem tuningWeight_fun_add (m : ℕ) (c d : ℕ → ℕ) :
    tuningWeight m (fun j => c j + d j) = tuningWeight m c + tuningWeight m d := by
  simp [tuningWeight, Nat.mul_add, Finset.sum_add_distrib]

/- English proof (translation)
The claim follows from `tuningWeight_fun_add m c d`.
-/
theorem tuningWeight_add (m : ℕ) (c d : ℕ → ℕ) :
    tuningWeight m (c + d) = tuningWeight m c + tuningWeight m d :=
  tuningWeight_fun_add m c d

/- English proof (translation)
Simplify using `[tuningWeight, Finset.mul_sum, Nat.mul_left_comm]`.
-/
theorem tuningWeight_mul_left (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (fun j => n * c j) = n * tuningWeight m c := by
  simp [tuningWeight, Finset.mul_sum, Nat.mul_left_comm]

/- English proof (translation)
Establish `: (n • c) = fun j => n * c j`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[this, tuningWeight_mul_left]`.
-/
theorem tuningWeight_nsmul (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (n • c) = n * tuningWeight m c := by
  have : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [this, tuningWeight_mul_left]

/- English proof (translation)
Rewrite using `[tuningWeight_eq_sum, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hni`.

Conclude with `absurd hi hni`.
-/
theorem tuningWeight_single (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningWeight m (Pi.single i 1) = m - i := by
  rw [tuningWeight_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]`. Simplify using the standard rewrite rules.
-/
theorem listProd_map_range_eq_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (List.map f (List.range m)).prod = ∏ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
      simp

section

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tuningMonomial (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) : Ideal S :=
  ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tuningMonomial_eq_prod (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j := rfl

/- English proof (translation)
Simplify using `[tuningMonomial_eq_prod, Ideal.one_eq_top]`.
-/
theorem tuningMonomial_zero (J : Ideal S) (m : ℕ) :
    tuningMonomial k J m (fun _ => 0) = ⊤ := by
  simp [tuningMonomial_eq_prod, Ideal.one_eq_top]

/- English proof (translation)
Rewrite using `[tuningMonomial_eq_prod, tuningMonomial_eq_prod, tuningMonomial_eq_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => (pow_add _ _ _).symm`.
-/
theorem tuningMonomial_mul_fun_add (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (fun j => c j + d j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, tuningMonomial_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => (pow_add _ _ _).symm

/- English proof (translation)
The claim follows from `tuningMonomial_mul_fun_add k J m c d`.
-/
theorem tuningMonomial_mul (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (c + d) :=
  tuningMonomial_mul_fun_add k J m c d

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.prod_range_succ, mul_pow, ih, Finset.prod_range_succ, ← pow_mul, Nat.mul_comm (c m) n]`.
-/
private theorem prod_derivIdealIterate_pow_pow (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    (∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j) ^ n
      = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ (n * c j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, mul_pow, ih, Finset.prod_range_succ, ← pow_mul,
        Nat.mul_comm (c m) n]

/- English proof (translation)
Rewrite using `[tuningMonomial_eq_prod, tuningMonomial_eq_prod]`. Conclude with `prod_derivIdealIterate_pow_pow k J m n c`.
-/
theorem tuningMonomial_pow_fun_mul (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (fun j => n * c j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod]
  exact prod_derivIdealIterate_pow_pow k J m n c

/- English proof (translation)
Establish `h : (n • c) = fun j => n * c j`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[h, tuningMonomial_pow_fun_mul]`.
-/
theorem tuningMonomial_pow (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (n • c) := by
  have h : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h, tuningMonomial_pow_fun_mul]

/- English proof (translation)
Rewrite using `[tuningMonomial_eq_prod, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hni`.

Conclude with `absurd hi hni`.
-/
theorem tuningMonomial_single (J : Ideal S) (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningMonomial k J m (Pi.single i 1) = derivIdealIterate k i J := by
  rw [tuningMonomial_eq_prod, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni

def tunedIdeal (J : Ideal S) (m s : ℕ) : Ideal S :=
  ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tunedIdeal_eq_iSup (J : Ideal S) (m s : ℕ) :
    tunedIdeal k J m s = ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c := rfl

/- English proof (translation)
The claim follows from `le_iSup_of_le c (le_iSup_of_le hc le_rfl)`.
-/
theorem tuningMonomial_le_tunedIdeal (J : Ideal S) (m s : ℕ) (c : ℕ → ℕ)
    (hc : s ≤ tuningWeight m c) : tuningMonomial k J m c ≤ tunedIdeal k J m s :=
  le_iSup_of_le c (le_iSup_of_le hc le_rfl)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Conclude with `le_trans (tuningMonomial_le_tunedIdeal k J m s c hc) h`. Introduce `h`. Conclude with `iSup_le fun c => iSup_le fun hc => h c hc`.
-/
theorem tunedIdeal_le_iff (J : Ideal S) (m s : ℕ) (K : Ideal S) :
    tunedIdeal k J m s ≤ K ↔ ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (tuningMonomial_le_tunedIdeal k J m s c hc) h
  · intro h
    exact iSup_le fun c => iSup_le fun hc => h c hc

/- English proof (translation)
Use `eq_top_iff.mpr ?_` and prove the remaining obligations. Rewrite using `[← tuningMonomial_zero k J m]`. Conclude with `tuningMonomial_le_tunedIdeal k J m 0 (fun _ => 0) (Nat.zero_le _)`.
-/
theorem tunedIdeal_zero (J : Ideal S) (m : ℕ) : tunedIdeal k J m 0 = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tuningMonomial_zero k J m]
  exact tuningMonomial_le_tunedIdeal k J m 0 (fun _ => 0) (Nat.zero_le _)

/- English proof (translation)
Rewrite using `[tunedIdeal_le_iff]`. Introduce `c hc`. Conclude with `tuningMonomial_le_tunedIdeal k J m s c (le_trans h hc)`.
-/
theorem tunedIdeal_antitone (J : Ideal S) (m : ℕ) {s t : ℕ} (h : s ≤ t) :
    tunedIdeal k J m t ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_le_iff]
  intro c hc
  exact tuningMonomial_le_tunedIdeal k J m s c (le_trans h hc)

/- English proof (translation)
Rewrite using `[tunedIdeal_eq_iSup, tunedIdeal_eq_iSup, Submodule.iSup_mul]`. Use `iSup_le fun c => ?_` and prove the remaining obligations. Rewrite using `[Submodule.iSup_mul]`. Use `iSup_le fun hc => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mul_iSup]`.

Use `iSup_le fun d => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mul_iSup]`. Use `iSup_le fun hd => ?_` and prove the remaining obligations. Rewrite using `[tuningMonomial_mul_fun_add]`. Use `tuningMonomial_le_tunedIdeal k J m _ _ ?_` and prove the remaining obligations.

Rewrite using `[tuningWeight_fun_add]`. Conclude with `Nat.add_le_add hc hd`.
-/
theorem tunedIdeal_mul_le (J : Ideal S) (m s t : ℕ) :
    tunedIdeal k J m s * tunedIdeal k J m t ≤ tunedIdeal k J m (s + t) := by
  rw [tunedIdeal_eq_iSup, tunedIdeal_eq_iSup, Submodule.iSup_mul]
  refine iSup_le fun c => ?_
  rw [Submodule.iSup_mul]
  refine iSup_le fun hc => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun d => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun hd => ?_
  rw [tuningMonomial_mul_fun_add]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_fun_add]
  exact Nat.add_le_add hc hd

/- English proof (translation)
Use `Ideal.mul_le.mpr ?_` and prove the remaining obligations. Introduce `b hb z hz`. Break down `Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩` into its components or cases. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem T (hX (Ideal.mul_mem_mul hb hx)) (hY (Ideal.mul_mem_mul hb hy))`.
-/
private theorem mul_sup_le {R : Type*} [CommRing R] (B X Y T : Ideal R)
    (hX : B * X ≤ T) (hY : B * Y ≤ T) : B * (X ⊔ Y) ≤ T := by
  refine Ideal.mul_le.mpr ?_
  intro b hb z hz
  rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
  rw [mul_add]
  exact Submodule.add_mem T (hX (Ideal.mul_mem_mul hb hx)) (hY (Ideal.mul_mem_mul hb hy))

/- English proof (translation)
Rewrite using `[Ideal.one_eq_top]`. Conclude with `derivIdeal_top A`.
-/
private theorem derivIdeal_one {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] : derivIdeal A (1 : Ideal R) = 1 := by
  rw [Ideal.one_eq_top]
  exact derivIdeal_top A

/- English proof (translation)
Establish `hmem : i ∈ Finset.range m` using `Finset.mem_range.mpr hi`. Establish `keyc : tuningWeight m c = (m - i) * c i + ∑ j ∈ (Finset.range m).erase i, (m - j) * c j`. Rewrite using `[tuningWeight_eq_sum]`. Conclude with `(Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * c j) hmem).symm`. Establish `keyd : tuningWeight m d = (m - i) * d i + ∑ j ∈ (Finset.range m).erase i, (m - j) * d j`.

Rewrite using `[tuningWeight_eq_sum]`. Conclude with `(Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * d j) hmem).symm`. Establish `h3 : ∑ j ∈ (Finset.range m).erase i, (m - j) * d j = ∑ j ∈ (Finset.range m).erase i, (m - j) * c j` using `Finset.sum_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]`. Rewrite using `[keyc, keyd, h3, ← hdi]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tuningWeight_eq_add_sub_of_succ (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) :
    tuningWeight m c = tuningWeight m d + (m - i) := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyc : tuningWeight m c
      = (m - i) * c i + ∑ j ∈ (Finset.range m).erase i, (m - j) * c j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * c j) hmem).symm
  have keyd : tuningWeight m d
      = (m - i) * d i + ∑ j ∈ (Finset.range m).erase i, (m - j) * d j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * d j) hmem).symm
  have h3 : ∑ j ∈ (Finset.range m).erase i, (m - j) * d j
      = ∑ j ∈ (Finset.range m).erase i, (m - j) * c j :=
    Finset.sum_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyc, keyd, h3, ← hdi]
  ring

/- English proof (translation)
Establish `hmem : i ∈ Finset.range m` using `Finset.mem_range.mpr hi`. Establish `keyd : tuningMonomial A J m d = derivIdealIterate A i J ^ d i * ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j`. Rewrite using `[tuningMonomial_eq_prod]`. Conclude with `(Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ d j) hmem).symm`. Establish `keyc : tuningMonomial A J m c = derivIdealIterate A i J ^ c i * ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j`.

Rewrite using `[tuningMonomial_eq_prod]`. Conclude with `(Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ c j) hmem).symm`. Establish `h3 : ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j = ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j` using `Finset.prod_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]`. Rewrite using `[keyd, keyc, h3, hdi, pow_succ]`. Simplify using `only [mul_comm, mul_assoc]`.
-/
private theorem tuningMonomial_eq_derivIdealIterate_mul_of_succ {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] (J : Ideal R) (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i = c i + 1) :
    tuningMonomial A J m d = derivIdealIterate A i J * tuningMonomial A J m c := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyd : tuningMonomial A J m d
      = derivIdealIterate A i J ^ d i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ d j) hmem).symm
  have keyc : tuningMonomial A J m c
      = derivIdealIterate A i J ^ c i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ c j) hmem).symm
  have h3 : ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j
      = ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j :=
    Finset.prod_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyd, keyc, h3, hdi, pow_succ]
  simp only [mul_comm, mul_assoc]

/- English proof (translation)
Establish `hw : tuningWeight m c = tuningWeight m d + (m - i)` using `tuningWeight_eq_add_sub_of_succ m i hi c d hne hdi`. Break down `Nat.lt_or_ge (i + 1) m with hlt | hge` into its components or cases. Establish `hmono : tuningMonomial A J m (fun j => if j = i + 1 then d j + 1 else d j) = derivIdealIterate A (i + 1) J * tuningMonomial A J m d` using `tuningMonomial_eq_derivIdealIterate_mul_of_succ J m (i + 1) hlt d (fun j => if j = i + 1 then d j + 1 else d j) (fun j hj => by simp [hj]) (by simp)`. Establish `hw' : tuningWeight m (fun j => if j = i + 1 then d j + 1 else d j) = tuningWeight m d + (m - (i + 1))` using `tuningWeight_eq_add_sub_of_succ m (i + 1) hlt (fun j => if j = i + 1 then d j + 1 else d j) d (fun j hj => by simp [hj]) (by simp)`. Use `le_trans (le_of_eq hmono.symm) (tuningMonomial_le_tunedIdeal A J m s (fun j => if j = i + 1 then d j + 1 else d j) ?_)` and prove the remaining obligations.

Use linear arithmetic over natural numbers and integers. Establish `hle : derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tuningMonomial A J m d` using `Ideal.mul_le.mpr fun r _ t ht => Ideal.mul_mem_left _ r ht`. Use `le_trans hle (tuningMonomial_le_tunedIdeal A J m s d ?_)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
private theorem derivIdealIterate_succ_mul_tuningMonomial_le {A : Type*} [CommRing A] {R : Type*}
    [CommRing R] [Algebra A R] (J : Ideal R) (m s i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) (hc : s + 1 ≤ tuningWeight m c) :
    derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tunedIdeal A J m s := by
  have hw : tuningWeight m c = tuningWeight m d + (m - i) :=
    tuningWeight_eq_add_sub_of_succ m i hi c d hne hdi
  rcases Nat.lt_or_ge (i + 1) m with hlt | hge
  · have hmono : tuningMonomial A J m (fun j => if j = i + 1 then d j + 1 else d j)
        = derivIdealIterate A (i + 1) J * tuningMonomial A J m d :=
      tuningMonomial_eq_derivIdealIterate_mul_of_succ J m (i + 1) hlt d (fun j => if j = i + 1 then d j + 1 else d j)
        (fun j hj => by simp [hj]) (by simp)
    have hw' : tuningWeight m (fun j => if j = i + 1 then d j + 1 else d j)
        = tuningWeight m d + (m - (i + 1)) :=
      tuningWeight_eq_add_sub_of_succ m (i + 1) hlt (fun j => if j = i + 1 then d j + 1 else d j) d
        (fun j hj => by simp [hj]) (by simp)
    refine le_trans (le_of_eq hmono.symm)
      (tuningMonomial_le_tunedIdeal A J m s (fun j => if j = i + 1 then d j + 1 else d j) ?_)
    omega
  · have hle : derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tuningMonomial A J m d :=
      Ideal.mul_le.mpr fun r _ t ht => Ideal.mul_mem_left _ r ht
    refine le_trans hle (tuningMonomial_le_tunedIdeal A J m s d ?_)
    omega

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `B h1 _`. Rewrite using `[Finset.range_zero, Finset.prod_empty, derivIdeal_one, mul_one]`.

Rewrite `h1` using `[Finset.range_zero, Finset.prod_empty, mul_one]`. Conclude with `h1`. Consider the case `succ n ih`. Introduce `B h1 h2`. Rewrite `h1` using `[Finset.prod_range_succ]`.

Rewrite using `[Finset.prod_range_succ]`. Use `le_trans (Ideal.mul_mono le_rfl (derivIdeal_mul_le A _ _)) ?_` and prove the remaining obligations. Use `mul_sup_le B _ _ T ?_ ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (c n) with h0 | hpos` into its components or cases. Rewrite `h1` using `[h0, pow_zero, mul_one]`.

Rewrite using `[h0, pow_zero, derivIdeal_one, mul_one]`. Conclude with `h1`. Take `⟨e, he⟩ : ∃ e, c n = e + 1` from `⟨c n - 1, by omega⟩`. Establish `hq1 : (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ (if j = n then e else c j)) = ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j` using `Finset.prod_congr rfl fun j hj => by`. Rewrite using `[if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]`.

Establish `hq2 : derivIdealIterate A n J ^ (if n = n then e else c n) = derivIdealIterate A n J ^ e` using `by simp`. Establish `hprod : (∏ j ∈ Finset.range (n + 1), derivIdealIterate A j J ^ (if j = n then e else c j)) = (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) * derivIdealIterate A n J ^ e`. Rewrite using `[Finset.prod_range_succ, hq1, hq2]`. Establish `hd : B * (derivIdealIterate A (n + 1) J * ((∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) * derivIdealIterate A n J ^ e)) ≤ T`. Rewrite using `[← hprod]`.

Conclude with `h2 n (Nat.lt_succ_self n) (fun j => if j = n then e else c j) (fun j hj => by simp [hj]) (by simp [he])`. Establish `hstep : derivIdeal A (derivIdealIterate A n J ^ c n) ≤ derivIdealIterate A n J ^ e * derivIdealIterate A (n + 1) J`. Rewrite using `[he, derivIdealIterate_succ]`. Conclude with `derivIdeal_pow_succ_le A (derivIdealIterate A n J) e`. Use `le_trans (Ideal.mul_mono le_rfl (Ideal.mul_mono le_rfl hstep)) ?_` and prove the remaining obligations.

Use `le_trans (le_of_eq ?_) hd` and prove the remaining obligations. Simplify using `only [mul_comm, mul_left_comm, mul_assoc]`. Establish `heq : B * (derivIdealIterate A n J ^ c n * derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j)) = (B * derivIdealIterate A n J ^ c n) * derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j)` using `(mul_assoc _ _ _).symm`. Rewrite using `[heq]`. Use `ih (B * derivIdealIterate A n J ^ c n) ?_ ?_` and prove the remaining obligations.

Use `le_trans (le_of_eq ?_) h1` and prove the remaining obligations. Simplify using `only [mul_comm, mul_assoc]`. Introduce `i hi d hne hdi`. Establish `hd` using `h2 i (Nat.lt_succ_of_lt hi) d hne hdi`. Rewrite `hd` using `[Finset.prod_range_succ, hne n (by omega : n ≠ i)]`.

Use `le_trans (le_of_eq ?_) hd` and prove the remaining obligations. Simplify using `only [mul_comm, mul_left_comm, mul_assoc]`.
-/
private theorem mul_derivIdeal_prod_le {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] (J T : Ideal R) (c : ℕ → ℕ) :
    ∀ (n : ℕ) (B : Ideal R),
      B * (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T →
      (∀ i, i < n → ∀ d : ℕ → ℕ, (∀ j, j ≠ i → d j = c j) → d i + 1 = c i →
        B * (derivIdealIterate A (i + 1) J *
          ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ d j) ≤ T) →
      B * derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T := by
  intro n
  induction n with
  | zero =>
      intro B h1 _
      rw [Finset.range_zero, Finset.prod_empty, derivIdeal_one, mul_one]
      rw [Finset.range_zero, Finset.prod_empty, mul_one] at h1
      exact h1
  | succ n ih =>
      intro B h1 h2
      rw [Finset.prod_range_succ] at h1
      rw [Finset.prod_range_succ]
      refine le_trans (Ideal.mul_mono le_rfl (derivIdeal_mul_le A _ _)) ?_
      refine mul_sup_le B _ _ T ?_ ?_
      · rcases Nat.eq_zero_or_pos (c n) with h0 | hpos
        · rw [h0, pow_zero, mul_one] at h1
          rw [h0, pow_zero, derivIdeal_one, mul_one]
          exact h1
        · obtain ⟨e, he⟩ : ∃ e, c n = e + 1 := ⟨c n - 1, by omega⟩
          have hq1 : (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ (if j = n then e else c j))
              = ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j :=
            Finset.prod_congr rfl fun j hj => by
              rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
          have hq2 : derivIdealIterate A n J ^ (if n = n then e else c n)
              = derivIdealIterate A n J ^ e := by simp
          have hprod : (∏ j ∈ Finset.range (n + 1),
                derivIdealIterate A j J ^ (if j = n then e else c j))
              = (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e := by
            rw [Finset.prod_range_succ, hq1, hq2]
          have hd : B * (derivIdealIterate A (n + 1) J *
              ((∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e)) ≤ T := by
            rw [← hprod]
            exact h2 n (Nat.lt_succ_self n) (fun j => if j = n then e else c j)
              (fun j hj => by simp [hj]) (by simp [he])
          have hstep : derivIdeal A (derivIdealIterate A n J ^ c n)
              ≤ derivIdealIterate A n J ^ e * derivIdealIterate A (n + 1) J := by
            rw [he, derivIdealIterate_succ]
            exact derivIdeal_pow_succ_le A (derivIdealIterate A n J) e
          refine le_trans (Ideal.mul_mono le_rfl (Ideal.mul_mono le_rfl hstep)) ?_
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]
      · have heq : B * (derivIdealIterate A n J ^ c n *
            derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j))
            = (B * derivIdealIterate A n J ^ c n) *
              derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) :=
          (mul_assoc _ _ _).symm
        rw [heq]
        refine ih (B * derivIdealIterate A n J ^ c n) ?_ ?_
        · refine le_trans (le_of_eq ?_) h1
          simp only [mul_comm, mul_assoc]
        · intro i hi d hne hdi
          have hd := h2 i (Nat.lt_succ_of_lt hi) d hne hdi
          rw [Finset.prod_range_succ, hne n (by omega : n ≠ i)] at hd
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]

/- English proof (translation)
Rewrite using `[tunedIdeal_eq_iSup k J m (s + 1)]`. Use `(derivIdeal_iSup_le k _).trans (iSup_le ?_)` and prove the remaining obligations. Introduce `c`. Use `(derivIdeal_iSup_le k _).trans (iSup_le ?_)` and prove the remaining obligations. Introduce `hc`.

Rewrite using `[tuningMonomial_eq_prod]`. Use `le_trans (le_of_eq (one_mul _).symm) ?_` and prove the remaining obligations. Use `mul_derivIdeal_prod_le J (tunedIdeal k J m s) c m 1 ?_ ?_` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `tuningMonomial_le_tunedIdeal k J m s c (by omega)`.

Introduce `i hi d hne hdi`. Rewrite using `[one_mul]`. Conclude with `derivIdealIterate_succ_mul_tuningMonomial_le J m s i hi c d hne hdi hc`.
-/
theorem derivIdeal_tunedIdeal_succ_le (J : Ideal S) (m s : ℕ) :
    derivIdeal k (tunedIdeal k J m (s + 1)) ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_eq_iSup k J m (s + 1)]
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro c
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro hc
  rw [tuningMonomial_eq_prod]
  refine le_trans (le_of_eq (one_mul _).symm) ?_
  refine mul_derivIdeal_prod_le J (tunedIdeal k J m s) c m 1 ?_ ?_
  · rw [one_mul]
    exact tuningMonomial_le_tunedIdeal k J m s c (by omega)
  · intro i hi d hne hdi
    rw [one_mul]
    exact derivIdealIterate_succ_mul_tuningMonomial_le J m s i hi c d hne hdi hc

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [derivIdealIterate_zero, Nat.sub_zero]`. Conclude with `le_rfl`. Consider the case `succ j ih`.

Rewrite using `[derivIdealIterate_succ]`. Use `le_trans (derivIdeal_mono k ih) ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (s - j) with h | h` into its components or cases. Establish `hsj : s - (j + 1) = 0` using `by omega`. Rewrite using `[hsj, tunedIdeal_zero]`.

Conclude with `le_top`. Take `⟨t, ht⟩ : ∃ t, s - j = t + 1` from `⟨s - j - 1, by omega⟩`. Establish `hsj : s - (j + 1) = t` using `by omega`. Rewrite using `[ht, hsj]`. Conclude with `derivIdeal_tunedIdeal_succ_le k J m t`.
-/
theorem derivIdealIterate_tunedIdeal_le (J : Ideal S) (m s j : ℕ) :
    derivIdealIterate k j (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - j) := by
  induction j with
  | zero =>
      simp only [derivIdealIterate_zero, Nat.sub_zero]
      exact le_rfl
  | succ j ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      rcases Nat.eq_zero_or_pos (s - j) with h | h
      · have hsj : s - (j + 1) = 0 := by omega
        rw [hsj, tunedIdeal_zero]
        exact le_top
      · obtain ⟨t, ht⟩ : ∃ t, s - j = t + 1 := ⟨s - j - 1, by omega⟩
        have hsj : s - (j + 1) = t := by omega
        rw [ht, hsj]
        exact derivIdeal_tunedIdeal_succ_le k J m t

/- English proof (translation)
Establish `hss : s - (s - 1) = 1` using `by omega`. Establish `hsum : 1 + (s - 1) = s` using `by omega`. Establish `h1 : derivIdealIterate k (s - 1) (tunedIdeal k J m s) ≤ tunedIdeal k J m 1`. Establish `h` using `derivIdealIterate_tunedIdeal_le k J m s (s - 1)`. Rewrite `h` using `[hss]`. Then use the resulting hypothesis.

Establish `h2 : derivIdeal k (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - 1)`. Establish `h` using `derivIdealIterate_tunedIdeal_le k J m s 1`. Rewrite `h` using `[derivIdealIterate_one]`. Then use the resulting hypothesis. Use `le_trans (Ideal.mul_mono h1 h2) ?_` and prove the remaining obligations. Establish `h3` using `tunedIdeal_mul_le k J m 1 (s - 1)`.

Rewrite `h3` using `[hsum]`. Then use the resulting hypothesis.
-/
theorem derivIdealIterate_mul_derivIdeal_tunedIdeal_le (J : Ideal S) (m s : ℕ) (hs : 1 ≤ s) :
    derivIdealIterate k (s - 1) (tunedIdeal k J m s) * derivIdeal k (tunedIdeal k J m s) ≤
      tunedIdeal k J m s := by
  have hss : s - (s - 1) = 1 := by omega
  have hsum : 1 + (s - 1) = s := by omega
  have h1 : derivIdealIterate k (s - 1) (tunedIdeal k J m s) ≤ tunedIdeal k J m 1 := by
    have h := derivIdealIterate_tunedIdeal_le k J m s (s - 1)
    rwa [hss] at h
  have h2 : derivIdeal k (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - 1) := by
    have h := derivIdealIterate_tunedIdeal_le k J m s 1
    rwa [derivIdealIterate_one] at h
  refine le_trans (Ideal.mul_mono h1 h2) ?_
  have h3 := tunedIdeal_mul_le k J m 1 (s - 1)
  rwa [hsum] at h3

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hz : tuningWeight m c = 0`. Rewrite using `[tuningWeight_eq_sum]`. Conclude with `Finset.sum_eq_zero fun j hj => by rw [hcon j hj, Nat.mul_zero]`.

Rewrite `hc` using `[hz]`. Conclude with `Nat.not_succ_le_zero 0 hc`.
-/
private theorem exists_ne_zero_of_one_le_tuningWeight {m : ℕ} {c : ℕ → ℕ}
    (hc : 1 ≤ tuningWeight m c) : ∃ j ∈ Finset.range m, c j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : tuningWeight m c = 0 := by
    rw [tuningWeight_eq_sum]
    exact Finset.sum_eq_zero fun j hj => by rw [hcon j hj, Nat.mul_zero]
  rw [hz] at hc
  exact Nat.not_succ_le_zero 0 hc

/- English proof (translation)
Rewrite using `[tunedIdeal_le_iff]`. Introduce `c hc`. Take `⟨j, hj, hcj⟩` from `exists_ne_zero_of_one_le_tuningWeight hc`. Establish `hjm : j ≤ m - 1` using `Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)`. Use `le_trans ?_ (derivIdealIterate_le_of_le k hjm J)` and prove the remaining obligations.

Establish `hsplit : derivIdealIterate k j J ^ c j * ∏ x ∈ (Finset.range m).erase j, derivIdealIterate k x J ^ c x = ∏ x ∈ Finset.range m, derivIdealIterate k x J ^ c x` using `Finset.mul_prod_erase (Finset.range m) (fun x => derivIdealIterate k x J ^ c x) hj`. Rewrite using `[tuningMonomial_eq_prod, ← hsplit]`. Conclude with `le_trans Ideal.mul_le_left (Ideal.pow_le_self hcj)`.
-/
theorem tunedIdeal_one_le_derivIdealIterate (J : Ideal S) (m : ℕ) (_hm : 1 ≤ m) :
    tunedIdeal k J m 1 ≤ derivIdealIterate k (m - 1) J := by
  rw [tunedIdeal_le_iff]
  intro c hc
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_one_le_tuningWeight hc
  have hjm : j ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  refine le_trans ?_ (derivIdealIterate_le_of_le k hjm J)
  have hsplit : derivIdealIterate k j J ^ c j *
      ∏ x ∈ (Finset.range m).erase j, derivIdealIterate k x J ^ c x =
      ∏ x ∈ Finset.range m, derivIdealIterate k x J ^ c x :=
    Finset.mul_prod_erase (Finset.range m) (fun x => derivIdealIterate k x J ^ c x) hj
  rw [tuningMonomial_eq_prod, ← hsplit]
  exact le_trans Ideal.mul_le_left (Ideal.pow_le_self hcj)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Conclude with `le_trans (Ideal.mul_mono le_rfl (tuningMonomial_le_tunedIdeal k J m s c hc)) h`. Introduce `h`. Rewrite using `[tunedIdeal_eq_iSup, Submodule.mul_iSup]`.

Use `iSup_le fun c => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mul_iSup]`. Conclude with `iSup_le fun hc => h c hc`.
-/
theorem mul_tunedIdeal_le_iff (I J : Ideal S) (m s : ℕ) (K : Ideal S) :
    I * tunedIdeal k J m s ≤ K ↔
      ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → I * tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (Ideal.mul_mono le_rfl (tuningMonomial_le_tunedIdeal k J m s c hc)) h
  · intro h
    rw [tunedIdeal_eq_iSup, Submodule.mul_iSup]
    refine iSup_le fun c => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun hc => h c hc

/- English proof (translation)
Establish `hmem : (m - 1) ∈ Finset.range m` using `Finset.mem_range.mpr (by omega)`. Establish `hspan : Ideal.span {x ^ n} ≤ tuningMonomial k J m (n • Pi.single (m - 1) 1)`. Rewrite using `[← tuningMonomial_pow, tuningMonomial_single k J m (m - 1) hmem, Ideal.span_singleton_le_iff_mem]`. Conclude with `Ideal.pow_mem_pow hx n`. Use `le_trans (Ideal.mul_mono hspan le_rfl) ?_` and prove the remaining obligations.

Rewrite using `[tuningMonomial_mul]`. Use `tuningMonomial_le_tunedIdeal k J m _ _ ?_` and prove the remaining obligations. Rewrite using `[tuningWeight_add, tuningWeight_nsmul, tuningWeight_single m (m - 1) hmem]`. Establish `hmm : m - (m - 1) = 1` using `by omega`. Rewrite using `[hmm]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem span_pow_mul_tuningMonomial_le (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n : ℕ) (c : ℕ → ℕ) :
    Ideal.span {x ^ n} * tuningMonomial k J m c ≤ tunedIdeal k J m (tuningWeight m c + n) := by
  have hmem : (m - 1) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have hspan : Ideal.span {x ^ n} ≤ tuningMonomial k J m (n • Pi.single (m - 1) 1) := by
    rw [← tuningMonomial_pow, tuningMonomial_single k J m (m - 1) hmem,
      Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow hx n
  refine le_trans (Ideal.mul_mono hspan le_rfl) ?_
  rw [tuningMonomial_mul]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_add, tuningWeight_nsmul, tuningWeight_single m (m - 1) hmem]
  have hmm : m - (m - 1) = 1 := by omega
  rw [hmm]
  omega

/- English proof (translation)
Rewrite using `[mul_tunedIdeal_le_iff]`. Introduce `c hc`. Use `le_trans (span_pow_mul_tuningMonomial_le k J m hm hx n c) ?_` and prove the remaining obligations. Conclude with `tunedIdeal_antitone k J m (Nat.add_le_add_right hc n)`.
-/
theorem span_pow_mul_tunedIdeal_le (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n t : ℕ) :
    Ideal.span {x ^ n} * tunedIdeal k J m t ≤ tunedIdeal k J m (t + n) := by
  rw [mul_tunedIdeal_le_iff]
  intro c hc
  refine le_trans (span_pow_mul_tuningMonomial_le k J m hm hx n c) ?_
  exact tunedIdeal_antitone k J m (Nat.add_le_add_right hc n)

section

variable [Algebra ℚ S]

/- English proof (translation)
Establish `hpos : (0 : ℚ) < (n : ℚ) + 1` using `by positivity`. Establish `hq : ((n : ℚ) + 1) ≠ 0` using `hpos.ne'`. Establish `hmap : algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1`. Rewrite using `[map_add, map_one, map_natCast]`. Establish `h1 : algebraMap ℚ A ((n : ℚ) + 1)⁻¹ * (((n : A) + 1) * y) ∈ I` using `Ideal.mul_mem_left I _ h`.

Rewrite `h1` using `[← hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]`. Conclude with `h1`.
-/
private theorem mem_of_natCast_add_one_mul_mem {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ)
    (I : Ideal A) (y : A) (h : ((n : A) + 1) * y ∈ I) : y ∈ I := by
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hq : ((n : ℚ) + 1) ≠ 0 := hpos.ne'
  have hmap : algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1 := by
    rw [map_add, map_one, map_natCast]
  have h1 : algebraMap ℚ A ((n : ℚ) + 1)⁻¹ * (((n : A) + 1) * y) ∈ I :=
    Ideal.mul_mem_left I _ h
  rw [← hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul] at h1
  exact h1

/- English proof (translation)
Establish `hg' : g ∈ tunedIdeal R J m (s - n)` using `derivIdealIterate_tunedIdeal_le R J m s n hg`. Conclude with `span_pow_mul_tunedIdeal_le R J m hm hx p (s - n) (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (x ^ p)) hg')`.
-/
private theorem pow_mul_mem_tunedIdeal (R : Type*) [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (s n p : ℕ) {g : A}
    (hg : g ∈ derivIdealIterate R n (tunedIdeal R J m s)) :
    x ^ p * g ∈ tunedIdeal R J m ((s - n) + p) := by
  have hg' : g ∈ tunedIdeal R J m (s - n) := derivIdealIterate_tunedIdeal_le R J m s n hg
  exact span_pow_mul_tunedIdeal_le R J m hm hx p (s - n)
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (x ^ p)) hg')

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `n hn g hg`. Establish `h1 : x ^ n * g ∈ tunedIdeal R J m ((s - n) + n)` using `pow_mul_mem_tunedIdeal R J m hm hx s n n hg`.

Establish `h2 : s + 1 ≤ (s - n) + n` using `by omega`. Conclude with `le_derivIdeal R _ (tunedIdeal_antitone R J m h2 h1)`. Consider the case `succ d ih`. Introduce `n hn g hg`. Establish `h1 : x ^ (n + 1) * g ∈ tunedIdeal R J m ((s - n) + (n + 1))` using `pow_mul_mem_tunedIdeal R J m hm hx s n (n + 1) hg`.

Establish `h2 : s + 1 ≤ (s - n) + (n + 1)` using `by omega`. Establish `h3 : x ^ (n + 1) * g ∈ tunedIdeal R J m (s + 1)` using `tunedIdeal_antitone R J m h2 h1`. Establish `h4 : δ (x ^ (n + 1) * g) ∈ derivIdeal R (tunedIdeal R J m (s + 1))` using `derivation_apply_mem_derivIdeal R (tunedIdeal R J m (s + 1)) δ h3`. Establish `h5 : δ g ∈ derivIdealIterate R (n + 1) (tunedIdeal R J m s)`. Rewrite using `[derivIdealIterate_succ]`.

Conclude with `derivation_apply_mem_derivIdeal R (derivIdealIterate R n (tunedIdeal R J m s)) δ hg`. Establish `h6 : x ^ (n + 1) * δ g ∈ derivIdeal R (tunedIdeal R J m (s + 1))` using `ih (n + 1) (by omega) (δ g) h5`. Establish `hd1 : δ (x ^ (n + 1)) = ((n : A) + 1) * x ^ n`. Establish `hpow` using `δ.leibniz_pow x (n + 1)`. Rewrite `hpow` using `[hδ]`.

Simplify using `using hpow`. Establish `hkey : ((n : A) + 1) * (x ^ n * g) = δ (x ^ (n + 1) * g) - x ^ (n + 1) * δ g`. Rewrite using `[Derivation.leibniz, hd1]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `mem_of_natCast_add_one_mul_mem n (derivIdeal R (tunedIdeal R J m (s + 1))) (x ^ n * g) ?_` and prove the remaining obligations. Rewrite using `[hkey]`. Conclude with `Submodule.sub_mem _ h4 h6`.
-/
private theorem pow_mul_mem_derivIdeal_tunedIdeal_succ (R : Type*) [CommRing R] {A : Type*}
    [CommRing A] [Algebra R A] [Algebra ℚ A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (δ : Derivation R A A) (hδ : δ x = 1) (s : ℕ) :
    ∀ d n : ℕ, s + 1 ≤ n + d → ∀ g : A, g ∈ derivIdealIterate R n (tunedIdeal R J m s) →
      x ^ n * g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) := by
  intro d
  induction d with
  | zero =>
      intro n hn g hg
      have h1 : x ^ n * g ∈ tunedIdeal R J m ((s - n) + n) :=
        pow_mul_mem_tunedIdeal R J m hm hx s n n hg
      have h2 : s + 1 ≤ (s - n) + n := by omega
      exact le_derivIdeal R _ (tunedIdeal_antitone R J m h2 h1)
  | succ d ih =>
      intro n hn g hg
      have h1 : x ^ (n + 1) * g ∈ tunedIdeal R J m ((s - n) + (n + 1)) :=
        pow_mul_mem_tunedIdeal R J m hm hx s n (n + 1) hg
      have h2 : s + 1 ≤ (s - n) + (n + 1) := by omega
      have h3 : x ^ (n + 1) * g ∈ tunedIdeal R J m (s + 1) :=
        tunedIdeal_antitone R J m h2 h1
      have h4 : δ (x ^ (n + 1) * g) ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        derivation_apply_mem_derivIdeal R (tunedIdeal R J m (s + 1)) δ h3
      have h5 : δ g ∈ derivIdealIterate R (n + 1) (tunedIdeal R J m s) := by
        rw [derivIdealIterate_succ]
        exact derivation_apply_mem_derivIdeal R (derivIdealIterate R n (tunedIdeal R J m s)) δ hg
      have h6 : x ^ (n + 1) * δ g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        ih (n + 1) (by omega) (δ g) h5
      have hd1 : δ (x ^ (n + 1)) = ((n : A) + 1) * x ^ n := by
        have hpow := δ.leibniz_pow x (n + 1)
        rw [hδ] at hpow
        simpa using hpow
      have hkey : ((n : A) + 1) * (x ^ n * g)
          = δ (x ^ (n + 1) * g) - x ^ (n + 1) * δ g := by
        rw [Derivation.leibniz, hd1]
        simp only [smul_eq_mul]
        ring
      refine mem_of_natCast_add_one_mul_mem n (derivIdeal R (tunedIdeal R J m (s + 1)))
        (x ^ n * g) ?_
      rw [hkey]
      exact Submodule.sub_mem _ h4 h6

/- English proof (translation)
Introduce `g hg`. Establish `h` using `pow_mul_mem_derivIdeal_tunedIdeal_succ k J m hm hx δ hδ s (s + 1) 0 (by omega) g (by rw [derivIdealIterate_zero]; exact hg)`. Rewrite `h` using `[pow_zero, one_mul]`. Then use the resulting hypothesis.
-/
theorem tunedIdeal_le_derivIdeal_tunedIdeal_succ (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (δ : Derivation k S S) (hδ : δ x = 1) (s : ℕ) :
    tunedIdeal k J m s ≤ derivIdeal k (tunedIdeal k J m (s + 1)) := by
  intro g hg
  have h := pow_mul_mem_derivIdeal_tunedIdeal_succ k J m hm hx δ hδ s (s + 1) 0 (by omega) g
    (by rw [derivIdealIterate_zero]; exact hg)
  rwa [pow_zero, one_mul] at h

end

end

end FunctorialResolution.EmbeddedResolution
