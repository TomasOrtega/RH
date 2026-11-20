import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Lemmata.GeneralBFactSide.Imports

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Take `⟨rs, hlen, hmem, hreg⟩` from `h`. Use `⟨rs.take m, by simp [hlen, hmn], fun r hr => hmem r (List.mem_of_mem_take hr), ?_⟩` and prove the remaining obligations. Establish `hw : IsWeaklyRegular M (rs.take m)`. Use `hreg.toIsWeaklyRegular` as an intermediate fact. Rewrite `this` using `[← List.take_append_drop m rs, isWeaklyRegular_append_iff]`.

Conclude with `this.1`. Use `⟨hw, fun htop => hreg.top_ne_smul ?_⟩` and prove the remaining obligations. Use `le_antisymm (htop.le.trans (Submodule.smul_mono_left ?_)) le_top` and prove the remaining obligations. Conclude with `Ideal.span_mono fun r hr => List.mem_of_mem_take hr`.
-/
theorem ModDepthGE.mono {m n : ℕ} (hmn : m ≤ n) (h : ModDepthGE R M n) : ModDepthGE R M m := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.take m, by simp [hlen, hmn], fun r hr => hmem r (List.mem_of_mem_take hr), ?_⟩
  have hw : IsWeaklyRegular M (rs.take m) := by
    have := hreg.toIsWeaklyRegular
    rw [← List.take_append_drop m rs, isWeaklyRegular_append_iff] at this
    exact this.1
  refine ⟨hw, fun htop => hreg.top_ne_smul ?_⟩
  refine le_antisymm (htop.le.trans (Submodule.smul_mono_left ?_)) le_top
  exact Ideal.span_mono fun r hr => List.mem_of_mem_take hr

/- English proof (translation)
Take `⟨rs, hlen, hmem, hreg⟩` from `h`. Use `⟨x :: rs, by simp [hlen], ?_, (isRegular_cons_iff M x rs).mpr ⟨reg, hreg⟩⟩` and prove the remaining obligations. Introduce `r hr`. Break down `List.mem_cons.mp hr with rfl | hr` into its components or cases. Conclude with `hx`.

Conclude with `hmem r hr`.
-/
theorem ModDepthGE.of_quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R (QuotSMulTop x M) n) : ModDepthGE R M (n + 1) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨x :: rs, by simp [hlen], ?_, (isRegular_cons_iff M x rs).mpr ⟨reg, hreg⟩⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hx
  · exact hmem r hr

/- English proof (translation)
Take `⟨b, -, hb⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma y hy)`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Introduce `hby`. Take `⟨b', -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hby`. Apply `ha` to reduce the goal to its premises.

Establish `: y • a = y • (x • b')` using `by rw [← hb, smul_comm]`. Rewrite using `[ry this]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top`. Introduce `z hz`. Take `⟨c, -, hc⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma z hz)`.

Establish `: x • (z • b) = x • (y • c)`. Rewrite using `[smul_comm x z, hb, smul_comm x y, hc, smul_comm]`. Rewrite using `[rx this]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top`.
-/
theorem exch_socle {x y : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) {a : M} (ha : a ∉ x • (⊤ : Submodule R M))
    (hma : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M)) :
    ∃ b : M, b ∉ y • (⊤ : Submodule R M) ∧
      ∀ z ∈ maximalIdeal R, z • b ∈ y • (⊤ : Submodule R M) := by
  obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma y hy)
  refine ⟨b, ?_, ?_⟩
  · intro hby
    obtain ⟨b', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hby
    apply ha
    have : y • a = y • (x • b') := by rw [← hb, smul_comm]
    rw [ry this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro z hz
    obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma z hz)
    have : x • (z • b) = x • (y • c) := by
      rw [smul_comm x z, hb, smul_comm x y, hc, smul_comm]
    rw [rx this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

section Noeth

variable [IsNoetherianRing R]

/- English proof (translation)
Take `⟨-, a, ha⟩` from `Submodule.isAssociatedPrime_iff.mp h`. Use `⟨a, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `(maximalIdeal.isMaximal R).ne_top` to reduce the goal to its premises. Rewrite using `[ha, eq_top_iff]`.

Introduce `r _`. Conclude with `Submodule.mem_colon_singleton.mpr (by simp)`. Rewrite `hz` using `[ha]`. Simplify using `using Submodule.mem_colon_singleton.mp hz`.
-/
theorem socle_of_max_mem_ass {N : Type*} [AddCommGroup N] [Module R N]
    (h : maximalIdeal R ∈ associatedPrimes R N) :
    ∃ a : N, a ≠ 0 ∧ ∀ z ∈ maximalIdeal R, z • a = 0 := by
  obtain ⟨-, a, ha⟩ := Submodule.isAssociatedPrime_iff.mp h
  refine ⟨a, ?_, fun z hz => ?_⟩
  · rintro rfl
    apply (maximalIdeal.isMaximal R).ne_top
    rw [ha, eq_top_iff]
    intro r _
    exact Submodule.mem_colon_singleton.mpr (by simp)
  · rw [ha] at hz
    simpa using Submodule.mem_colon_singleton.mp hz

/- English proof (translation)
Introduce `h`. Take `⟨a, ha, hz⟩` from `socle_of_max_mem_ass h`. Conclude with `ha (rw (show w • a = w • (0 : N) by rw [hz w hw, smul_zero]))`.
-/
theorem max_not_mem_ass_of_reg {N : Type*} [AddCommGroup N] [Module R N] {w : R}
    (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular N w) :
    maximalIdeal R ∉ associatedPrimes R N := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  exact ha (rw (show w • a = w • (0 : N) by rw [hz w hw, smul_zero]))

/- English proof (translation)
Introduce `h`. Take `⟨a, ha, hz⟩` from `socle_of_max_mem_ass h`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Establish `ha' : a ∉ x • (⊤ : Submodule R M)` using `fun h' => ha ((Submodule.Quotient.mk_eq_zero _).mpr h')`. Establish `hz' : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M)` using `fun z hz0 => (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_smul]; exact hz z hz0)`.

Take `⟨b, hb, hzb⟩` from `exch_socle hy rx ry ha' hz'`. Establish `hb0 : (Submodule.Quotient.mk b : QuotSMulTop y M) ≠ 0` using `fun h' => hb ((Submodule.Quotient.mk_eq_zero _).mp h')`. Apply `hb0` to reduce the goal to its premises. Apply `rw` to reduce the goal to its premises. Use `show w • _ = w • (0 : QuotSMulTop y M)`.

Rewrite using `[smul_zero, ← Submodule.Quotient.mk_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (hzb w hw)`.
-/
theorem max_not_mem_ass_swap {x y w : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular (QuotSMulTop y M) w) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x M) := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have ha' : a ∉ x • (⊤ : Submodule R M) := fun h' => ha ((Submodule.Quotient.mk_eq_zero _).mpr h')
  have hz' : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M) := fun z hz0 =>
    (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_smul]; exact hz z hz0)
  obtain ⟨b, hb, hzb⟩ := exch_socle hy rx ry ha' hz'
  have hb0 : (Submodule.Quotient.mk b : QuotSMulTop y M) ≠ 0 :=
    fun h' => hb ((Submodule.Quotient.mk_eq_zero _).mp h')
  apply hb0
  apply rw
  show w • _ = w • (0 : QuotSMulTop y M)
  rw [smul_zero, ← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hzb w hw)

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_side.goal1 .. | (apply Bl.general_b_fact_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_side.goal1 <;> assumption)`.
-/
theorem exists_reg_both {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : maximalIdeal R ∉ associatedPrimes R N₁) (h₂ : maximalIdeal R ∉ associatedPrimes R N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  first | exact Bl.general_b_fact_side.goal1 .. | (apply Bl.general_b_fact_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_side.goal1 <;> assumption)

end Noeth

section Main

variable [IsNoetherianRing R]

universe u in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `N _ _ _ x hx reg h`. Take `⟨rs, -, -, hreg⟩` from `h`. Use `hreg.nontrivial` as an intermediate fact.

Use `nontrivial_quotSMulTop_of_mem_maximalIdeal N hx` as an intermediate fact. Conclude with `⟨[], rfl, by simp, (isRegular_cons_iff N x []).mpr ⟨reg, IsRegular.nil R _⟩⟩`. Consider the case `succ n ih`. Introduce `N _ _ _ x hx reg h`. Take `⟨ys0, hlen, hmem, hreg⟩` from `h`.

Break down `ys0 with _ | ⟨y, ys⟩` into its components or cases. Simplify using `at hlen`. Break down `ys with _ | ⟨y', ys'⟩` into its components or cases. Simplify using `at hlen`. Establish `hy : y ∈ maximalIdeal R` using `hmem y (by simp)`.

Establish `hy' : y' ∈ maximalIdeal R` using `hmem y' (by simp)`. Use `hreg.nontrivial` as an intermediate fact. Take `⟨ry, hys⟩` from `(isRegular_cons_iff N y _).mp hreg`. Establish `ry' : IsSMulRegular (QuotSMulTop y N) y'` using `((isRegular_cons_iff _ _ _).mp hys).1`. Establish `hAy` using `max_not_mem_ass_of_reg hy' ry'`.

Establish `hAx` using `max_not_mem_ass_swap hy reg ry hy' ry'`. Take `⟨z, hz, rzx, rzy⟩` from `exists_reg_both hAx hAy`. Establish `hdy : ModDepthGE R (QuotSMulTop y N) (n + 1)` using `⟨y' :: ys', by simpa using hlen, fun r hr => hmem r (List.mem_cons_of_mem _ hr), hys⟩`. Take `⟨zs, hzs, hzsm, hzreg⟩` from `ih (QuotSMulTop y N) hz rzy hdy`. Establish `h1 : IsRegular N (y :: z :: zs)` using `(isRegular_cons_iff N y _).mpr ⟨ry, hzreg⟩`.

Establish `h2 : IsRegular N (z :: y :: zs)` using `IsLocalRing.isRegular_of_perm h1 (List.Perm.swap z y zs)`. Take `⟨rz, hyz⟩` from `(isRegular_cons_iff N z _).mp h2`. Establish `: Nontrivial (QuotSMulTop x N)` using `nontrivial_quotSMulTop_of_mem_maximalIdeal N hx`. Establish `: Nontrivial (QuotSMulTop z (QuotSMulTop x N))` using `nontrivial_quotSMulTop_of_mem_maximalIdeal _ hz`. Establish `h3 : IsRegular N [x, z]` using `(isRegular_cons_iff N x _).mpr ⟨reg, (isRegular_cons_iff _ z _).mpr ⟨rzx, IsRegular.nil R _⟩⟩`.

Establish `h4 : IsRegular N [z, x]` using `IsLocalRing.isRegular_of_perm h3 (List.Perm.swap z x [])`. Establish `rxz : IsSMulRegular (QuotSMulTop z N) x` using `((isRegular_cons_iff _ x _).mp ((isRegular_cons_iff N z _).mp h4).2).1`. Establish `hdz : ModDepthGE R (QuotSMulTop z N) (n + 1)`. Use `⟨y :: zs, by simp [hzs], fun r hr => ?_, hyz⟩` and prove the remaining obligations. Break down `List.mem_cons.mp hr with rfl | hr` into its components or cases.

Use `exacts [hy, hzsm r hr]`. Take `⟨ws, hws, hwsm, hwreg⟩` from `ih (QuotSMulTop z N) hx rxz hdz`. Establish `h5 : IsRegular N (z :: x :: ws)` using `(isRegular_cons_iff N z _).mpr ⟨rz, hwreg⟩`. Establish `h6 : IsRegular N (x :: z :: ws)` using `IsLocalRing.isRegular_of_perm h5 (List.Perm.swap x z ws)`. Use `⟨z :: ws, by simp [hws], fun r hr => ?_, h6⟩` and prove the remaining obligations.

Break down `List.mem_cons.mp hr with rfl | hr` into its components or cases. Use `exacts [hz, hwsm r hr]`.
-/
theorem exists_regular_sequence_cons (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R},
      x ∈ maximalIdeal R → IsSMulRegular N x → ModDepthGE R N (n + 1) →
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular N (x :: rs) := by
  induction n with
  | zero =>
    intro N _ _ _ x hx reg h
    obtain ⟨rs, -, -, hreg⟩ := h
    have := hreg.nontrivial
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    exact ⟨[], rfl, by simp, (isRegular_cons_iff N x []).mpr ⟨reg, IsRegular.nil R _⟩⟩
  | succ n ih =>
    intro N _ _ _ x hx reg h
    obtain ⟨ys0, hlen, hmem, hreg⟩ := h
    rcases ys0 with _ | ⟨y, ys⟩
    · simp at hlen
    rcases ys with _ | ⟨y', ys'⟩
    · simp at hlen
    have hy : y ∈ maximalIdeal R := hmem y (by simp)
    have hy' : y' ∈ maximalIdeal R := hmem y' (by simp)
    have := hreg.nontrivial
    obtain ⟨ry, hys⟩ := (isRegular_cons_iff N y _).mp hreg
    have ry' : IsSMulRegular (QuotSMulTop y N) y' := ((isRegular_cons_iff _ _ _).mp hys).1
    have hAy := max_not_mem_ass_of_reg hy' ry'
    have hAx := max_not_mem_ass_swap hy reg ry hy' ry'
    obtain ⟨z, hz, rzx, rzy⟩ := exists_reg_both hAx hAy
    have hdy : ModDepthGE R (QuotSMulTop y N) (n + 1) :=
      ⟨y' :: ys', by simpa using hlen, fun r hr => hmem r (List.mem_cons_of_mem _ hr), hys⟩
    obtain ⟨zs, hzs, hzsm, hzreg⟩ := ih (QuotSMulTop y N) hz rzy hdy
    have h1 : IsRegular N (y :: z :: zs) := (isRegular_cons_iff N y _).mpr ⟨ry, hzreg⟩
    have h2 : IsRegular N (z :: y :: zs) := IsLocalRing.isRegular_of_perm h1 (List.Perm.swap z y zs)
    obtain ⟨rz, hyz⟩ := (isRegular_cons_iff N z _).mp h2
    have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    have : Nontrivial (QuotSMulTop z (QuotSMulTop x N)) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal _ hz
    have h3 : IsRegular N [x, z] :=
      (isRegular_cons_iff N x _).mpr ⟨reg, (isRegular_cons_iff _ z _).mpr ⟨rzx, IsRegular.nil R _⟩⟩
    have h4 : IsRegular N [z, x] := IsLocalRing.isRegular_of_perm h3 (List.Perm.swap z x [])
    have rxz : IsSMulRegular (QuotSMulTop z N) x :=
      ((isRegular_cons_iff _ x _).mp ((isRegular_cons_iff N z _).mp h4).2).1
    have hdz : ModDepthGE R (QuotSMulTop z N) (n + 1) := by
      refine ⟨y :: zs, by simp [hzs], fun r hr => ?_, hyz⟩
      rcases List.mem_cons.mp hr with rfl | hr
      exacts [hy, hzsm r hr]
    obtain ⟨ws, hws, hwsm, hwreg⟩ := ih (QuotSMulTop z N) hx rxz hdz
    have h5 : IsRegular N (z :: x :: ws) := (isRegular_cons_iff N z _).mpr ⟨rz, hwreg⟩
    have h6 : IsRegular N (x :: z :: ws) := IsLocalRing.isRegular_of_perm h5 (List.Perm.swap x z ws)
    refine ⟨z :: ws, by simp [hws], fun r hr => ?_, h6⟩
    rcases List.mem_cons.mp hr with rfl | hr
    exacts [hz, hwsm r hr]

end Main

variable [IsNoetherianRing R] [Module.Finite R M]

/- English proof (translation)
The claim follows from `exists_regular_sequence_cons n M hx reg h`.
-/
theorem exists_isRegular_cons_of_modDepthGE {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) {n : ℕ} (h : ModDepthGE R M (n + 1)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M (x :: rs) :=
  exists_regular_sequence_cons n M hx reg h

/- English proof (translation)
Take `⟨rs, hl, hm, hr⟩` from `exists_isRegular_cons_of_modDepthGE hx reg h`. Conclude with `⟨rs, hl, hm, ((isRegular_cons_iff M x rs).mp hr).2⟩`.
-/
theorem ModDepthGE.quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R M (n + 1)) : ModDepthGE R (QuotSMulTop x M) n := by
  obtain ⟨rs, hl, hm, hr⟩ := exists_isRegular_cons_of_modDepthGE hx reg h
  exact ⟨rs, hl, hm, ((isRegular_cons_iff M x rs).mp hr).2⟩

/- English proof (translation)
Proceed by induction on `rs generalizing M with`. Consider the case `nil`. Simplify using `only [List.length_nil, zero_add] at h`. Take `⟨rs', hl, hm, hr⟩` from `h`. Conclude with `⟨rs', hl, hm, hr⟩`.

Consider the case `cons r rs ih`. Establish `hr : r ∈ maximalIdeal R` using `hrs r (by simp)`. Take `⟨rreg, hq⟩` from `(isRegular_cons_iff M r rs).mp reg`. Establish `hlen : (r :: rs).length + n = rs.length + n + 1` using `by simp; omega`. Rewrite `h` using `[hlen]`.

Take `⟨rs', hl, hm, hreg'⟩` from `ih (M := QuotSMulTop r M) (fun s hs => hrs s (List.mem_cons_of_mem _ hs)) hq (ModDepthGE.quotSMulTop hr rreg h)`. Conclude with `⟨rs', hl, hm, (isRegular_cons_iff M r _).mpr ⟨rreg, hreg'⟩⟩`.
-/
theorem exists_isRegular_append_of_modDepthGE {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular M rs) {n : ℕ} (h : ModDepthGE R M (rs.length + n)) :
    ∃ rs' : List R, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular M (rs ++ rs') := by
  induction rs generalizing M with
  | nil =>
    simp only [List.length_nil, zero_add] at h
    obtain ⟨rs', hl, hm, hr⟩ := h
    exact ⟨rs', hl, hm, hr⟩
  | cons r rs ih =>
    have hr : r ∈ maximalIdeal R := hrs r (by simp)
    obtain ⟨rreg, hq⟩ := (isRegular_cons_iff M r rs).mp reg
    have hlen : (r :: rs).length + n = rs.length + n + 1 := by simp; omega
    rw [hlen] at h
    obtain ⟨rs', hl, hm, hreg'⟩ := ih (M := QuotSMulTop r M)
      (fun s hs => hrs s (List.mem_cons_of_mem _ hs)) hq (ModDepthGE.quotSMulTop hr rreg h)
    exact ⟨rs', hl, hm, (isRegular_cons_iff M r _).mpr ⟨rreg, hreg'⟩⟩

end ReciprocityTheory.CA
