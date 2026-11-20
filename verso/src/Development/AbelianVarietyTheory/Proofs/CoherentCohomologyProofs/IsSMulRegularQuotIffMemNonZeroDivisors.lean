import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates

namespace GlobalTheory

section Regular

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
  {f : ι → R}

/- English proof (translation)
Introduce `y z hyz`. Take `⟨c, rfl⟩` from `(h.powGrEquiv a).surjective y`. Take `⟨d, rfl⟩` from `(h.powGrEquiv a).surjective z`. Establish `key : ∀ c, x • h.powGrEquiv a c = h.powGrEquiv a (x • c)` using `fun c => ((h.powGrEquiv a).map_smul (Ideal.Quotient.mk _ x) c).symm.trans (by`. Use `congr 1)`.

Simplify using `only [key] at hyz`. Use `(h.powGrEquiv a).injective hyz` as an intermediate fact. Use `congr 1`. Conclude with `funext fun α => hx (congrFun this α)`.
-/
theorem IsQuasiRegularSeq.isSMulRegular_powGr (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) :
    IsSMulRegular (powGr (Ideal.span (Set.range f)) M a) x := by
  intro y z hyz
  obtain ⟨c, rfl⟩ := (h.powGrEquiv a).surjective y
  obtain ⟨d, rfl⟩ := (h.powGrEquiv a).surjective z
  have key : ∀ c, x • h.powGrEquiv a c = h.powGrEquiv a (x • c) := fun c =>
    ((h.powGrEquiv a).map_smul (Ideal.Quotient.mk _ x) c).symm.trans (by
      congr 1)
  simp only [key] at hyz
  have := (h.powGrEquiv a).injective hyz
  congr 1
  exact funext fun α => hx (congrFun this α)

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Establish `h1` using `ih (powGr.pow_succ_smul_le _ M a hm)`. Establish `h2 : x • powGr.mk _ M a ⟨m, h1⟩ = 0`.

Rewrite using `[← map_smul, powGr.mk_eq_zero]`. Conclude with `hm`. Conclude with `(powGr.mk_eq_zero _).mp ((h.isSMulRegular_powGr hx a).right_eq_zero_of_smul h2)`.
-/
theorem IsQuasiRegularSeq.mem_pow_smul_top_of_smul_mem (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) {m : M}
    (hm : x • m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := ih (powGr.pow_succ_smul_le _ M a hm)
    have h2 : x • powGr.mk _ M a ⟨m, h1⟩ = 0 := by
      rw [← map_smul, powGr.mk_eq_zero]
      exact hm
    exact (powGr.mk_eq_zero _).mp ((h.isSMulRegular_powGr hx a).right_eq_zero_of_smul h2)

/- English proof (translation)
Use `IsSMulRegular.of_right_eq_zero_of_smul fun m hm => ?_` and prove the remaining obligations. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Rewrite `hm` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (h.mem_pow_smul_top_of_smul_mem hx a hm)`.
-/
theorem IsQuasiRegularSeq.isSMulRegular_quot_pow (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) :
    IsSMulRegular (M ⧸ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)) x := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun m hm => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  exact (Submodule.Quotient.mk_eq_zero _).mpr (h.mem_pow_smul_top_of_smul_mem hx a hm)

/- English proof (translation)
Use `⟨fun hm => ?_, fun hm => Submodule.smul_top_le_comap_smul_top _ g hm⟩` and prove the remaining obligations. Take `⟨s, hs, hsm⟩` from `exists_smul_mem_smul_top_of_isLocalizedModule T g _ hm`. Conclude with `h.mem_pow_smul_top_of_smul_mem (hT s hs) a hsm`.
-/
theorem IsQuasiRegularSeq.map_mem_pow_smul_top_iff (h : IsQuasiRegularSeq M f) (T : Submonoid R)
    (hT : ∀ t ∈ T, IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) t)
    {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) [IsLocalizedModule T g] (a : ℕ)
    (m : M) : g m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R N) ↔
      m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  refine ⟨fun hm => ?_, fun hm => Submodule.smul_top_le_comap_smul_top _ g hm⟩
  obtain ⟨s, hs, hsm⟩ := exists_smul_mem_smul_top_of_isLocalizedModule T g _ hm
  exact h.mem_pow_smul_top_of_smul_mem (hT s hs) a hsm

/- English proof (translation)
Rewrite using `[show (J • ⊤ : Submodule R R) = J by simp]`.
-/
theorem isSMulRegular_quot_smul_top_iff (J : Ideal R) (x : R) :
    IsSMulRegular (R ⧸ (J • ⊤ : Submodule R R)) x ↔ IsSMulRegular (R ⧸ J) x := by
  rw [show (J • ⊤ : Submodule R R) = J by simp]

/- English proof (translation)
Rewrite using `[← isRegular_iff_mem_nonZeroDivisors, ← isLeftRegular_iff_isRegular, isLeftRegular_iff]`. Conclude with `(isSMulRegular_algebraMap_iff (R ⧸ J)).symm`.
-/
theorem isSMulRegular_quot_iff_mem_nonZeroDivisors (J : Ideal R) (x : R) :
    IsSMulRegular (R ⧸ J) x ↔ Ideal.Quotient.mk J x ∈ nonZeroDivisors (R ⧸ J) := by
  rw [← isRegular_iff_mem_nonZeroDivisors, ← isLeftRegular_iff_isRegular, isLeftRegular_iff]
  exact (isSMulRegular_algebraMap_iff (R ⧸ J)).symm

/- English proof (translation)
The claim follows from `h.isSMulRegular_powGr ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a`.
-/
theorem IsQuasiRegularSeq.isSMulRegular_powGr_self (h : IsQuasiRegularSeq R f) {x : R}
    (hx : IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x) (a : ℕ) :
    IsSMulRegular (powGr (Ideal.span (Set.range f)) R a) x :=
  h.isSMulRegular_powGr ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a

/- English proof (translation)
The claim follows from `(isSMulRegular_quot_smul_top_iff _ x).mp (h.isSMulRegular_quot_pow ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a)`.
-/
theorem IsQuasiRegularSeq.isSMulRegular_quot_pow_self (h : IsQuasiRegularSeq R f) {x : R}
    (hx : IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x) (a : ℕ) :
    IsSMulRegular (R ⧸ Ideal.span (Set.range f) ^ a) x :=
  (isSMulRegular_quot_smul_top_iff _ x).mp
    (h.isSMulRegular_quot_pow ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a)

/- English proof (translation)
Simplify `hy)` using `using h.mem_pow_smul_top_of_smul_mem ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a (m := y) (by simpa`.
-/
theorem IsQuasiRegularSeq.mem_pow_of_mul_mem (h : IsQuasiRegularSeq R f) {x : R}
    (hx : IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x) (a : ℕ) {y : R}
    (hy : x * y ∈ Ideal.span (Set.range f) ^ a) : y ∈ Ideal.span (Set.range f) ^ a := by
  simpa using h.mem_pow_smul_top_of_smul_mem ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a
    (m := y) (by simpa using hy)

/- English proof (translation)
Use `le_antisymm (fun y hy => ?_) Ideal.le_comap_map` and prove the remaining obligations. Rewrite `hy` using `[Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff T]`. Take `⟨t, ht, hty⟩` from `hy`. Conclude with `h.mem_pow_of_mul_mem (hT t ht) a hty`.
-/
theorem IsQuasiRegularSeq.comap_map_pow (h : IsQuasiRegularSeq R f) (T : Submonoid R)
    (hT : ∀ t ∈ T, IsSMulRegular (R ⧸ Ideal.span (Set.range f)) t)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S] (a : ℕ) :
    ((Ideal.span (Set.range f) ^ a).map (algebraMap R S)).comap (algebraMap R S) =
      Ideal.span (Set.range f) ^ a := by
  refine le_antisymm (fun y hy => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff T] at hy
  obtain ⟨t, ht, hty⟩ := hy
  exact h.mem_pow_of_mul_mem (hT t ht) a hty

end Regular

section Prime

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {f : ι → R}

/- English proof (translation)
The claim follows from `(isSMulRegular_quot_iff_mem_nonZeroDivisors P x).mpr (mem_nonZeroDivisors_of_ne_zero fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h))`.
-/
theorem isSMulRegular_quot_of_notMem {P : Ideal R} [P.IsPrime] {x : R} (hx : x ∉ P) :
    IsSMulRegular (R ⧸ P) x :=
  (isSMulRegular_quot_iff_mem_nonZeroDivisors P x).mpr
    (mem_nonZeroDivisors_of_ne_zero fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h))

/- English proof (translation)
The claim follows from `h.mem_pow_of_mul_mem (isSMulRegular_quot_of_notMem hx) a hy`.
-/
theorem IsQuasiRegularSeq.mem_pow_of_mul_mem_of_notMem (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] {x y : R} (hx : x ∉ Ideal.span (Set.range f)) (a : ℕ)
    (hy : x * y ∈ Ideal.span (Set.range f) ^ a) : y ∈ Ideal.span (Set.range f) ^ a :=
  h.mem_pow_of_mul_mem (isSMulRegular_quot_of_notMem hx) a hy

/- English proof (translation)
Rewrite using `[Ideal.radical_pow P ha, hP.radical]`.
-/
theorem radical_pow_of_isPrime (P : Ideal R) [hP : P.IsPrime] {a : ℕ} (ha : a ≠ 0) :
    (P ^ a).radical = P := by
  rw [Ideal.radical_pow P ha, hP.radical]

/- English proof (translation)
Rewrite using `[Ideal.isPrimary_iff, radical_pow_of_isPrime _ ha]`. Use `⟨fun ht => hI.ne_top (top_le_iff.mp (ht ▸ Ideal.pow_le_self ha)), fun {x y} hxy => ?_⟩` and prove the remaining obligations. Rewrite using `[or_iff_not_imp_right]`. Conclude with `fun hy => h.mem_pow_of_mul_mem_of_notMem hy a (mul_comm x y ▸ hxy)`.
-/
theorem IsQuasiRegularSeq.isPrimary_pow (h : IsQuasiRegularSeq R f)
    [hI : (Ideal.span (Set.range f)).IsPrime] {a : ℕ} (ha : a ≠ 0) :
    (Ideal.span (Set.range f) ^ a).IsPrimary := by
  rw [Ideal.isPrimary_iff, radical_pow_of_isPrime _ ha]
  refine ⟨fun ht => hI.ne_top (top_le_iff.mp (ht ▸ Ideal.pow_le_self ha)), fun {x y} hxy => ?_⟩
  rw [or_iff_not_imp_right]
  exact fun hy => h.mem_pow_of_mul_mem_of_notMem hy a (mul_comm x y ▸ hxy)

variable (S : Type*) [CommRing S] [Algebra R S]

/- English proof (translation)
The claim follows from `h.comap_map_pow (Ideal.span (Set.range f)).primeCompl (fun _ ht => isSMulRegular_quot_of_notMem ht) S a`.
-/
theorem IsQuasiRegularSeq.comap_map_pow_atPrime (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] [IsLocalization.AtPrime S (Ideal.span (Set.range f))]
    (a : ℕ) : ((Ideal.span (Set.range f) ^ a).map (algebraMap R S)).comap (algebraMap R S) =
      Ideal.span (Set.range f) ^ a :=
  h.comap_map_pow (Ideal.span (Set.range f)).primeCompl
    (fun _ ht => isSMulRegular_quot_of_notMem ht) S a

/- English proof (translation)
Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span (Set.range f)) S, ← Ideal.map_pow, h.comap_map_pow_atPrime S a]`.
-/
theorem IsQuasiRegularSeq.comap_maximalIdeal_pow (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] [IsLocalRing S]
    [IsLocalization.AtPrime S (Ideal.span (Set.range f))] (a : ℕ) :
    (IsLocalRing.maximalIdeal S ^ a).comap (algebraMap R S) = Ideal.span (Set.range f) ^ a := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span (Set.range f)) S, ← Ideal.map_pow,
    h.comap_map_pow_atPrime S a]

/- English proof (translation)
Rewrite using `[← h.comap_maximalIdeal_pow S a, Ideal.mem_comap]`.
-/
theorem IsQuasiRegularSeq.algebraMap_mem_maximalIdeal_pow_iff (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] [IsLocalRing S]
    [IsLocalization.AtPrime S (Ideal.span (Set.range f))] (a : ℕ) (y : R) :
    algebraMap R S y ∈ IsLocalRing.maximalIdeal S ^ a ↔ y ∈ Ideal.span (Set.range f) ^ a := by
  rw [← h.comap_maximalIdeal_pow S a, Ideal.mem_comap]

end Prime

section Free

abbrev MonoDegLE (ι : Type*) (k : ℕ) : Type _ := {α : ι →₀ ℕ // α.degree ≤ k}

instance MonoDegLE.finite (ι : Type*) [Finite ι] (k : ℕ) : Finite (MonoDegLE ι k) :=
  (Finsupp.finite_of_degree_le (σ := ι) k).to_subtype

noncomputable instance MonoDegLE.fintype (ι : Type*) [Finite ι] (k : ℕ) :
    Fintype (MonoDegLE ι k) :=
  Fintype.ofFinite _

/- English proof (translation)
The claim follows from `fintypeCard_degree_le ι k`.
-/
theorem MonoDegLE.card (ι : Type*) [Fintype ι] (k : ℕ) :
    Fintype.card (MonoDegLE ι k) = (k + Fintype.card ι).choose (Fintype.card ι) :=
  fintypeCard_degree_le ι k

/- English proof (translation)
Establish `h1` using `Finset.sum_subtype (p := fun α : ι →₀ ℕ => α.degree ≤ k) (F := MonoDegLE.fintype ι k) (Finsupp.finite_of_degree_le (σ := ι) k).toFinset (by simp) g`. Rewrite using `[← h1, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (k + 1)) (g := Finsupp.degree) (by simp [Nat.lt_succ_iff])]`. Use `Finset.sum_congr rfl fun a ha => Finset.sum_subtype _ (fun α => ?_) g` and prove the remaining obligations. Rewrite `ha` using `[Finset.mem_range]`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem MonoDegLE.sum_eq_sum_range {ι N : Type*} [Finite ι] [AddCommMonoid N] (k : ℕ)
    (g : (ι →₀ ℕ) → N) :
    ∑ α : MonoDegLE ι k, g α.1 = ∑ a ∈ Finset.range (k + 1), ∑ α : MonoDeg ι a, g α.1 := by
  classical
  have h1 := Finset.sum_subtype (p := fun α : ι →₀ ℕ => α.degree ≤ k)
    (F := MonoDegLE.fintype ι k) (Finsupp.finite_of_degree_le (σ := ι) k).toFinset (by simp) g
  rw [← h1, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (k + 1)) (g := Finsupp.degree)
    (by simp [Nat.lt_succ_iff])]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_subtype _ (fun α => ?_) g
  rw [Finset.mem_range] at ha
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  omega

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite `hn` using `[Finset.sum_range_succ]`. Establish `htop : ∑ α : MonoDeg ι n, monoVal f α.1 • c α.1 ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M)` using `(mem_pow_smul_top_iff f n _).mpr ⟨_, rfl⟩`.

Establish `hlow` using `ih ((Submodule.add_mem_iff_left _ htop).mp (powGr.pow_succ_smul_le _ M n hn))`. Rewrite `hn` using `[Finset.sum_eq_zero, zero_add]`. Introduce `α hα`. Break down `(Nat.lt_succ_iff_lt_or_eq).mp hα with hα | hα` into its components or cases. Conclude with `hlow α hα`.

Conclude with `hc α (h n (fun β => c β.1) hn ⟨α, hα⟩)`. Introduce `a ha`. Use `Finset.sum_eq_zero fun α _ => ?_` and prove the remaining obligations. Rewrite using `[hlow α.1 (α.2.symm ▸ Finset.mem_range.mp ha), smul_zero]`.
-/
theorem IsQuasiRegularSeq.eq_zero_of_sum_range_mem {f : ι → R} (h : IsQuasiRegularSeq M f)
    (c : (ι →₀ ℕ) → M)
    (hc : ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) → c α = 0) (n : ℕ)
    (hn : ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • c α.1 ∈
      (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M)) :
    ∀ α, α.degree < n → c α = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ] at hn
    have htop : ∑ α : MonoDeg ι n, monoVal f α.1 • c α.1 ∈
        (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M) :=
      (mem_pow_smul_top_iff f n _).mpr ⟨_, rfl⟩
    have hlow := ih ((Submodule.add_mem_iff_left _ htop).mp (powGr.pow_succ_smul_le _ M n hn))
    rw [Finset.sum_eq_zero, zero_add] at hn
    · intro α hα
      rcases (Nat.lt_succ_iff_lt_or_eq).mp hα with hα | hα
      · exact hlow α hα
      · exact hc α (h n (fun β => c β.1) hn ⟨α, hα⟩)
    · intro a ha
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [hlow α.1 (α.2.symm ▸ Finset.mem_range.mp ha), smul_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨fun _ => (hs 0).choose, by simp⟩`. Consider the case `succ n ih`. Take `⟨c, hc⟩` from `ih`. Take `⟨d, hd⟩` from `(mem_pow_smul_top_iff f n _).mp hc`.

Use `choose e he using fun α => hs (d α)`. Use `⟨fun β => if hβ : β.degree = n then e ⟨β, hβ⟩ else c β, ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • s (if hβ : α.1.degree = n then e ⟨α.1, hβ⟩ else c α.1) = ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • s (c α.1)`. Use `Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[dif_neg (α.2.trans_ne (Finset.mem_range.mp ha).ne)]`.

Establish `h2 : ∑ α : MonoDeg ι n, monoVal f α.1 • s (if hβ : α.1.degree = n then e ⟨α.1, hβ⟩ else c α.1) = ∑ α : MonoDeg ι n, monoVal f α.1 • s (e α)` using `Finset.sum_congr rfl fun α _ => by rw [dif_pos α.2]`. Rewrite using `[Finset.sum_range_succ, h1, h2, ← sub_sub, ← hd, ← Finset.sum_sub_distrib, pow_succ, mul_smul]`. Use `Submodule.sum_mem _ fun α _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Conclude with `Submodule.smul_mem_smul (monoVal_mem_pow f α) (he α)`.
-/
theorem exists_sub_sum_range_mem (f : ι → R) {N : Type*} (s : N → M)
    (hs : ∀ m, ∃ y, m - s y ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) (n : ℕ) (m : M) :
    ∃ c : (ι →₀ ℕ) → N, m - ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • s (c α.1) ∈
      (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M) := by
  induction n with
  | zero => exact ⟨fun _ => (hs 0).choose, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := (mem_pow_smul_top_iff f n _).mp hc
    choose e he using fun α => hs (d α)
    refine ⟨fun β => if hβ : β.degree = n then e ⟨β, hβ⟩ else c β, ?_⟩
    have h1 : ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a,
        monoVal f α.1 • s (if hβ : α.1.degree = n then e ⟨α.1, hβ⟩ else c α.1) =
        ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • s (c α.1) := by
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun α _ => ?_
      rw [dif_neg (α.2.trans_ne (Finset.mem_range.mp ha).ne)]
    have h2 : ∑ α : MonoDeg ι n,
        monoVal f α.1 • s (if hβ : α.1.degree = n then e ⟨α.1, hβ⟩ else c α.1) =
        ∑ α : MonoDeg ι n, monoVal f α.1 • s (e α) :=
      Finset.sum_congr rfl fun α _ => by rw [dif_pos α.2]
    rw [Finset.sum_range_succ, h1, h2, ← sub_sub, ← hd, ← Finset.sum_sub_distrib, pow_succ,
      mul_smul]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [← smul_sub]
    exact Submodule.smul_mem_smul (monoVal_mem_pow f α) (he α)

variable {A : Type*} [CommRing A] [Algebra A R] [Module A M] [IsScalarTower A R M]
  {N : Type*} [AddCommGroup N] [Module A N]

noncomputable def monoLEToQuotPow (f : ι → R) (s : N →ₗ[A] M) (k : ℕ) :
    (MonoDegLE ι k → N) →ₗ[A] M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M) :=
  (Submodule.mkQ _).restrictScalars A ∘ₗ ∑ α : MonoDegLE ι k,
    (LinearMap.lsmul R M (monoVal f α.1)).restrictScalars A ∘ₗ s ∘ₗ LinearMap.proj α

/- English proof (translation)
Simplify using `only [monoLEToQuotPow, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, LinearMap.proj_apply, Submodule.mkQ_apply]`.
-/
theorem monoLEToQuotPow_apply (f : ι → R) (s : N →ₗ[A] M) (k : ℕ) (c : MonoDegLE ι k → N) :
    monoLEToQuotPow f s k c = Submodule.Quotient.mk (∑ α, monoVal f α.1 • s (c α)) := by
  simp only [monoLEToQuotPow, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, LinearMap.proj_apply,
    Submodule.mkQ_apply]

/- English proof (translation)
Rewrite using `[monoLEToQuotPow_apply, Finset.sum_eq_single α]`. Rewrite using `[Pi.single_eq_same]`. Introduce `β _ h`. Rewrite using `[Pi.single_eq_of_ne h, map_zero, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem monoLEToQuotPow_single [DecidableEq ι] (f : ι → R) (s : N →ₗ[A] M) (k : ℕ)
    (α : MonoDegLE ι k) (y : N) :
    monoLEToQuotPow f s k (Pi.single α y) = Submodule.Quotient.mk (monoVal f α.1 • s y) := by
  rw [monoLEToQuotPow_apply, Finset.sum_eq_single α]
  · rw [Pi.single_eq_same]
  · intro β _ h
    rw [Pi.single_eq_of_ne h, map_zero, smul_zero]
  · simp

/- English proof (translation)
Introduce `m`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Take `⟨c, hc⟩` from `exists_sub_sum_range_mem f s (fun m => by`. Take `⟨y, hy⟩` from `hs (Submodule.Quotient.mk m)`. Conclude with `⟨y, (Submodule.Quotient.eq _).mp hy.symm⟩) (k + 1) m`.

Use `⟨fun α => c α.1, ?_⟩` and prove the remaining obligations. Rewrite using `[monoLEToQuotPow_apply, MonoDegLE.sum_eq_sum_range k fun α => monoVal f α • s (c α), eq_comm, Submodule.Quotient.eq]`. Conclude with `hc`.
-/
theorem monoLEToQuotPow_surjective (f : ι → R) (s : N →ₗ[A] M)
    (hs : Function.Surjective fun y =>
      (Submodule.Quotient.mk (s y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) : Function.Surjective (monoLEToQuotPow f s k) := by
  intro m
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨c, hc⟩ := exists_sub_sum_range_mem f s (fun m => by
    obtain ⟨y, hy⟩ := hs (Submodule.Quotient.mk m)
    exact ⟨y, (Submodule.Quotient.eq _).mp hy.symm⟩) (k + 1) m
  refine ⟨fun α => c α.1, ?_⟩
  rw [monoLEToQuotPow_apply, MonoDegLE.sum_eq_sum_range k fun α => monoVal f α • s (c α), eq_comm,
    Submodule.Quotient.eq]
  exact hc

/- English proof (translation)
Establish `hs0 : ∀ y, s y ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) → y = 0` using `fun y hy => hs (by simpa using hy)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Set `c' : (ι →₀ ℕ) → N` to `fun β => if hβ : β.degree ≤ k then c ⟨β, hβ⟩ else 0`. Establish `hc' : ∀ α : MonoDegLE ι k, c α = c' α.1` using `fun α => by simp only [c', dif_pos α.2]`.

Rewrite `hc` using `[monoLEToQuotPow_apply, Submodule.Quotient.mk_eq_zero]`. Simplify using `only [hc'] at hc`. Rewrite `hc` using `[MonoDegLE.sum_eq_sum_range k fun α => monoVal f α • s (c' α)]`. Use `h.eq_zero_of_sum_range_mem (fun α => s (c' α)) (fun α hα => by rw [hs0 _ hα, map_zero]) (k + 1) hc` as an intermediate fact. Use function extensionality and compare the values at `α`.

Use `hs0 _ ?_` and prove the remaining obligations. Rewrite using `[hc', this α.1 (Nat.lt_succ_of_le α.2)]`. Conclude with `zero_mem _`.
-/
theorem IsQuasiRegularSeq.monoLEToQuotPow_injective {f : ι → R} (h : IsQuasiRegularSeq M f)
    (s : N →ₗ[A] M)
    (hs : Function.Injective fun y =>
      (Submodule.Quotient.mk (s y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) : Function.Injective (monoLEToQuotPow f s k) := by
  have hs0 : ∀ y, s y ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) → y = 0 := fun y hy =>
    hs (by simpa using hy)
  rw [injective_iff_map_eq_zero]
  intro c hc
  let c' : (ι →₀ ℕ) → N := fun β => if hβ : β.degree ≤ k then c ⟨β, hβ⟩ else 0
  have hc' : ∀ α : MonoDegLE ι k, c α = c' α.1 := fun α => by simp only [c', dif_pos α.2]
  rw [monoLEToQuotPow_apply, Submodule.Quotient.mk_eq_zero] at hc
  simp only [hc'] at hc
  rw [MonoDegLE.sum_eq_sum_range k fun α => monoVal f α • s (c' α)] at hc
  have := h.eq_zero_of_sum_range_mem (fun α => s (c' α))
    (fun α hα => by rw [hs0 _ hα, map_zero]) (k + 1) hc
  funext α
  refine hs0 _ ?_
  rw [hc', this α.1 (Nat.lt_succ_of_le α.2)]
  exact zero_mem _

noncomputable def IsQuasiRegularSeq.quotPowEquiv {f : ι → R} (h : IsQuasiRegularSeq M f)
    (s : N →ₗ[A] M)
    (hs : Function.Bijective fun y =>
      (Submodule.Quotient.mk (s y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) :
    (MonoDegLE ι k → N) ≃ₗ[A] M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M) :=
  LinearEquiv.ofBijective (monoLEToQuotPow f s k)
    ⟨h.monoLEToQuotPow_injective s hs.1 k, monoLEToQuotPow_surjective f s hs.2 k⟩

/- English proof (translation)
The claim follows from `funext fun y => Finsupp.apply_linearCombination A (P.mkQ.restrictScalars A) m y`.
-/
private theorem mk_linearCombination (P : Submodule R M) {κ : Type*} (m : κ → M) :
    (fun y : κ →₀ A => (Submodule.Quotient.mk (Finsupp.linearCombination A m y) : M ⧸ P)) =
      Finsupp.linearCombination A fun j => (Submodule.Quotient.mk (m j) : M ⧸ P) :=
  funext fun y => Finsupp.apply_linearCombination A (P.mkQ.restrictScalars A) m y

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[monoLEToQuotPow_single]`.
-/
private theorem monoLEToQuotPow_comp_basis (f : ι → R) {κ : Type*} (m : κ → M) (k : ℕ) :
    monoLEToQuotPow f (Finsupp.linearCombination A m) k ∘
      (Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex
        (Equiv.sigmaEquivProd _ _) =
      fun p : MonoDegLE ι k × κ => Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) := by
  classical
  funext p
  simp [monoLEToQuotPow_single]

/- English proof (translation)
Establish `hs : Function.Injective fun y : κ →₀ A => (Submodule.Quotient.mk (Finsupp.linearCombination A m y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M))`. Rewrite using `[mk_linearCombination]`. Conclude with `hm`. Establish `h1` using `((Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex (Equiv.sigmaEquivProd _ _)).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (h.monoLEToQuotPow_injective _ hs k))`. Rewrite `h1` using `[monoLEToQuotPow_comp_basis]`. Then use the resulting hypothesis.
-/
theorem IsQuasiRegularSeq.linearIndependent_monoVal_smul {f : ι → R} (h : IsQuasiRegularSeq M f)
    {κ : Type*} {m : κ → M}
    (hm : LinearIndependent A fun j =>
      (Submodule.Quotient.mk (m j) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) :
    LinearIndependent A fun p : MonoDegLE ι k × κ =>
      (Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) :
        M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M)) := by
  have hs : Function.Injective fun y : κ →₀ A =>
      (Submodule.Quotient.mk (Finsupp.linearCombination A m y) :
        M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) := by
    rw [mk_linearCombination]
    exact hm
  have h1 := ((Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex
    (Equiv.sigmaEquivProd _ _)).linearIndependent.map' _
    (LinearMap.ker_eq_bot.mpr (h.monoLEToQuotPow_injective _ hs k))
  rwa [monoLEToQuotPow_comp_basis] at h1

/- English proof (translation)
Establish `hs : Function.Surjective fun y : κ →₀ A => (Submodule.Quotient.mk (Finsupp.linearCombination A m y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M))`. Rewrite using `[mk_linearCombination, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]` and apply the resulting hypothesis. Establish `h1` using `congrArg (Submodule.map (monoLEToQuotPow f (Finsupp.linearCombination A m) k)) ((Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex (Equiv.sigmaEquivProd _ _)).span_eq`. Rewrite `h1` using `[Submodule.map_top, LinearMap.range_eq_top.mpr (monoLEToQuotPow_surjective f _ hs k), Submodule.map_span, ← Set.range_comp, monoLEToQuotPow_comp_basis]`. Then use the resulting hypothesis.
-/
theorem span_monoVal_smul_eq_top (f : ι → R) {κ : Type*} {m : κ → M}
    (hm : Submodule.span A (Set.range fun j =>
      (Submodule.Quotient.mk (m j) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M))) = ⊤)
    (k : ℕ) :
    Submodule.span A (Set.range fun p : MonoDegLE ι k × κ =>
      (Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) :
        M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M))) = ⊤ := by
  have hs : Function.Surjective fun y : κ →₀ A =>
      (Submodule.Quotient.mk (Finsupp.linearCombination A m y) :
        M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) := by
    rwa [mk_linearCombination, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  have h1 := congrArg (Submodule.map (monoLEToQuotPow f (Finsupp.linearCombination A m) k))
    ((Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex
      (Equiv.sigmaEquivProd _ _)).span_eq
  rwa [Submodule.map_top, LinearMap.range_eq_top.mpr (monoLEToQuotPow_surjective f _ hs k),
    Submodule.map_span, ← Set.range_comp, monoLEToQuotPow_comp_basis] at h1

noncomputable def IsQuasiRegularSeq.quotPowBasis {f : ι → R} (h : IsQuasiRegularSeq M f)
    {κ : Type*} (b : Module.Basis κ A (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (m : κ → M) (hm : ∀ j, Submodule.Quotient.mk (m j) = b j) (k : ℕ) :
    Module.Basis (MonoDegLE ι k × κ) A
      (M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M)) :=
  Module.Basis.mk
    (h.linearIndependent_monoVal_smul (m := m) (by simpa only [hm] using b.linearIndependent) k)
    (span_monoVal_smul_eq_top f (m := m) (by simpa only [hm] using b.span_eq) k).ge

/- English proof (translation)
The claim follows from `Module.Basis.mk_apply _ _ _`.
-/
@[simp] theorem IsQuasiRegularSeq.quotPowBasis_apply {f : ι → R} (h : IsQuasiRegularSeq M f)
    {κ : Type*} (b : Module.Basis κ A (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (m : κ → M) (hm : ∀ j, Submodule.Quotient.mk (m j) = b j) (k : ℕ) (p : MonoDegLE ι k × κ) :
    h.quotPowBasis b m hm k p = Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) :=
  Module.Basis.mk_apply _ _ _

end Free

section FreeRing

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {f : ι → R}
  {A : Type*} [CommRing A] [Algebra A R]

variable (A) in

noncomputable def quotSMulTopEquivQuotOver (J : Ideal R) :
    (R ⧸ (J • ⊤ : Submodule R R)) ≃ₗ[A] R ⧸ J :=
  (Submodule.quotEquivOfEq (J • ⊤ : Submodule R R) J (by simp)).restrictScalars A

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quotSMulTopEquivQuotOver_mk (J : Ideal R) (x : R) :
    quotSMulTopEquivQuotOver A J (Submodule.Quotient.mk x) = Ideal.Quotient.mk J x := rfl

noncomputable def IsQuasiRegularSeq.quotPowBasisSelf (h : IsQuasiRegularSeq R f)
    {κ : Type*} (b : Module.Basis κ A (R ⧸ Ideal.span (Set.range f)))
    (r : κ → R) (hr : ∀ j, Ideal.Quotient.mk _ (r j) = b j) (k : ℕ) :
    Module.Basis (MonoDegLE ι k × κ) A (R ⧸ Ideal.span (Set.range f) ^ (k + 1)) :=
  (h.quotPowBasis (b.map (quotSMulTopEquivQuotOver A _).symm) r (fun j => by
    rw [Module.Basis.map_apply, LinearEquiv.eq_symm_apply, quotSMulTopEquivQuotOver_mk, hr]) k).map
    (quotSMulTopEquivQuotOver A _)

/- English proof (translation)
Rewrite using `[IsQuasiRegularSeq.quotPowBasisSelf, Module.Basis.map_apply, IsQuasiRegularSeq.quotPowBasis_apply, quotSMulTopEquivQuotOver_mk, smul_eq_mul]`.
-/
@[simp] theorem IsQuasiRegularSeq.quotPowBasisSelf_apply (h : IsQuasiRegularSeq R f)
    {κ : Type*} (b : Module.Basis κ A (R ⧸ Ideal.span (Set.range f)))
    (r : κ → R) (hr : ∀ j, Ideal.Quotient.mk _ (r j) = b j) (k : ℕ) (p : MonoDegLE ι k × κ) :
    h.quotPowBasisSelf b r hr k p = Ideal.Quotient.mk _ (monoVal f p.1.1 * r p.2) := by
  rw [IsQuasiRegularSeq.quotPowBasisSelf, Module.Basis.map_apply,
    IsQuasiRegularSeq.quotPowBasis_apply, quotSMulTopEquivQuotOver_mk, smul_eq_mul]

/- English proof (translation)
Use `choose r hr using fun j => Ideal.Quotient.mk_surjective (b j)`. Use `⟨(h.quotPowBasisSelf b r hr k).reindex (Fintype.equivFinOfCardEq ?_)⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_prod, MonoDegLE.card, Fintype.card_fin, mul_comm]`.
-/
theorem IsQuasiRegularSeq.nonempty_basis_quot_pow_self {ι : Type*} [Fintype ι] {f : ι → R}
    (h : IsQuasiRegularSeq R f) {d : ℕ} (b : Module.Basis (Fin d) A (R ⧸ Ideal.span (Set.range f)))
    (k : ℕ) :
    Nonempty (Module.Basis (Fin (d * (k + Fintype.card ι).choose (Fintype.card ι))) A
      (R ⧸ Ideal.span (Set.range f) ^ (k + 1))) := by
  choose r hr using fun j => Ideal.Quotient.mk_surjective (b j)
  refine ⟨(h.quotPowBasisSelf b r hr k).reindex (Fintype.equivFinOfCardEq ?_)⟩
  rw [Fintype.card_prod, MonoDegLE.card, Fintype.card_fin, mul_comm]

end FreeRing

universe u v

/- English proof (translation)
Use `⟨fun x hx a => ⟨h.isSMulRegular_powGr_self hx a, h.isSMulRegular_quot_pow_self hx a⟩, fun a => ⟨fun ha => ⟨h.isPrimary_pow ha, radical_pow_of_isPrime _ ha⟩, h.comap_map_pow_atPrime _ a, h.algebraMap_mem_maximalIdeal_pow_iff _ a⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `A _ _ d k ⟨b⟩`. Use `h.nonempty_basis_quot_pow_self b k` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Then use the resulting hypothesis.
-/
theorem IsQuasiRegularSeq.powers {R : Type u} [CommRing R] {n : ℕ} {f : Fin n → R}
    (h : IsQuasiRegularSeq R f) :
    (∀ x : R, IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x → ∀ a : ℕ,
      IsSMulRegular (powGr (Ideal.span (Set.range f)) R a) x ∧
        IsSMulRegular (R ⧸ Ideal.span (Set.range f) ^ a) x) ∧
    (∀ [(Ideal.span (Set.range f)).IsPrime] (a : ℕ),
      (a ≠ 0 → (Ideal.span (Set.range f) ^ a).IsPrimary ∧
        (Ideal.span (Set.range f) ^ a).radical = Ideal.span (Set.range f)) ∧
      ((Ideal.span (Set.range f) ^ a).map
          (algebraMap R (Localization.AtPrime (Ideal.span (Set.range f))))).comap
        (algebraMap R (Localization.AtPrime (Ideal.span (Set.range f)))) =
          Ideal.span (Set.range f) ^ a ∧
      ∀ y : R, algebraMap R (Localization.AtPrime (Ideal.span (Set.range f))) y ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span (Set.range f))) ^ a ↔
        y ∈ Ideal.span (Set.range f) ^ a) ∧
    (∀ (A : Type v) [CommRing A] [Algebra A R] (d k : ℕ),
      Nonempty (Module.Basis (Fin d) A (R ⧸ Ideal.span (Set.range f))) →
      Nonempty (Module.Basis (Fin (d * (k + n).choose n)) A
        (R ⧸ Ideal.span (Set.range f) ^ (k + 1)))) := by
  refine ⟨fun x hx a => ⟨h.isSMulRegular_powGr_self hx a, h.isSMulRegular_quot_pow_self hx a⟩,
    fun a => ⟨fun ha => ⟨h.isPrimary_pow ha, radical_pow_of_isPrime _ ha⟩,
      h.comap_map_pow_atPrime _ a, h.algebraMap_mem_maximalIdeal_pow_iff _ a⟩, ?_⟩
  rintro A _ _ d k ⟨b⟩
  have := h.nonempty_basis_quot_pow_self b k
  rwa [Fintype.card_fin] at this

/- English proof (translation)
Establish `: (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).IsPrime`. Establish `hk : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) = RingHom.ker MvPolynomial.constantCoeff`. Use extensionality with `p`. Rewrite using `[← pow_one (Ideal.span _), RingHom.mem_ker]`. Use `(MvPolynomial.mem_pow_idealOfVars_iff' _ _).trans ?_` and prove the remaining obligations.

Simplify using `[Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]`. Rewrite using `[hk]`. Conclude with `RingHom.ker_isPrime _`. Conclude with `(isQuasiRegularSeq_X (R := ℤ) (Fin 2)).isPrimary_pow (by norm_num)`.
-/
example : (MvPolynomial.idealOfVars (Fin 2) ℤ ^ 3).IsPrimary := by
  have : (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).IsPrime := by
    have hk : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) =
        RingHom.ker MvPolynomial.constantCoeff := by
      ext p
      rw [← pow_one (Ideal.span _), RingHom.mem_ker]
      refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).trans ?_
      simp [Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]
    rw [hk]
    exact RingHom.ker_isPrime _
  exact (isQuasiRegularSeq_X (R := ℤ) (Fin 2)).isPrimary_pow (by norm_num)

/- English proof (translation)
Establish `hk : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) = RingHom.ker (MvPolynomial.aeval (R` using `ℤ) fun _ : Fin 2 => (0 : ℤ)) := by`. Use extensionality with `p`. Rewrite using `[← pow_one (Ideal.span _), RingHom.mem_ker]`. Use `(MvPolynomial.mem_pow_idealOfVars_iff' _ _).trans ?_` and prove the remaining obligations. Simplify using `[Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]`.

Establish `e` using `(Ideal.quotientEquivAlgOfEq ℤ hk).trans (Ideal.quotientKerAlgEquivOfSurjective (f := MvPolynomial.aeval (R := ℤ) fun _ : Fin 2 => (0 : ℤ)) fun z => ⟨MvPolynomial.C z, by simp⟩)`. Conclude with `(isQuasiRegularSeq_X (R := ℤ) (Fin 2)).powers.2.2 ℤ 1 2 ⟨(Module.Basis.singleton (Fin 1) ℤ).map e.symm.toLinearEquiv⟩`.
-/
example : Nonempty (Module.Basis (Fin 6) ℤ
    (MvPolynomial (Fin 2) ℤ ⧸ MvPolynomial.idealOfVars (Fin 2) ℤ ^ 3)) := by
  have hk : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) =
      RingHom.ker (MvPolynomial.aeval (R := ℤ) fun _ : Fin 2 => (0 : ℤ)) := by
    ext p
    rw [← pow_one (Ideal.span _), RingHom.mem_ker]
    refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).trans ?_
    simp [Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]
  have e := (Ideal.quotientEquivAlgOfEq ℤ hk).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := MvPolynomial.aeval (R := ℤ) fun _ : Fin 2 => (0 : ℤ))
      fun z => ⟨MvPolynomial.C z, by simp⟩)
  exact (isQuasiRegularSeq_X (R := ℤ) (Fin 2)).powers.2.2 ℤ 1 2
    ⟨(Module.Basis.singleton (Fin 1) ℤ).map e.symm.toLinearEquiv⟩

end GlobalTheory
