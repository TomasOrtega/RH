import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicExistsIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZpowSmulMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompOneAddPowMul

noncomputable section
namespace GlobalTheory.PsiShiftProof
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.PhiGam.Inh GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters GlobalTheory.PsiLemmaCompare

section Filt
variable {k : Type} [Field k]

def Dp (k : Type) [Field k] (s : ℤ) : Submodule k⟦X⟧ k⸨X⸩ := sh s (stdLat k)

/- English proof (translation)
Rewrite using `[Dp, mem_sh_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨b, rfl⟩` from `mem_stdLat.1 hy`. Conclude with `⟨b, rfl⟩`.

Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨b, mem_stdLat.2 ⟨b, rfl⟩, rfl⟩`.
-/
theorem mem_Dp {s : ℤ} {x : k⸨X⸩} : x ∈ Dp k s ↔ ∃ b : k⟦X⟧, x = vv k ^ s * (b : k⸨X⸩) := by
  rw [Dp, mem_sh_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := mem_stdLat.1 hy
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, mem_stdLat.2 ⟨b, rfl⟩, rfl⟩

/- English proof (translation)
The claim follows from `mem_Dp.trans (PsiBasis.mem_iff s x)`.
-/
theorem mem_Dp_coeff {s : ℤ} {x : k⸨X⸩} : x ∈ Dp k s ↔ ∀ m < s, x.coeff m = 0 :=
  mem_Dp.trans (PsiBasis.mem_iff s x)

/- English proof (translation)
Simplify using `[mem_Dp]`.
-/
theorem mem_Dp_zero {x : k⸨X⸩} : x ∈ Dp k 0 ↔ ∃ b : k⟦X⟧, x = (b : k⸨X⸩) := by
  simp [mem_Dp]

/- English proof (translation)
The claim follows from `mem_Dp_zero.2 ⟨b, rfl⟩`.
-/
theorem coe_mem (b : k⟦X⟧) : (b : k⸨X⸩) ∈ Dp k 0 := mem_Dp_zero.2 ⟨b, rfl⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `mem_Dp.1 hx`. Take `⟨b, rfl⟩` from `mem_Dp.1 hy`. Use `sh_le_sh_of_le h _ (mem_Dp.2 ⟨a * b, ?_⟩)` and prove the remaining obligations. Rewrite using `[zpow_add₀ (vv_ne_zero k), map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dp_mul {s t u : ℤ} {x y : k⸨X⸩} (hx : x ∈ Dp k s) (hy : y ∈ Dp k t) (h : u ≤ s + t) :
    x * y ∈ Dp k u := by
  obtain ⟨a, rfl⟩ := mem_Dp.1 hx
  obtain ⟨b, rfl⟩ := mem_Dp.1 hy
  refine sh_le_sh_of_le h _ (mem_Dp.2 ⟨a * b, ?_⟩)
  rw [zpow_add₀ (vv_ne_zero k), map_mul]; ring

/- English proof (translation)
The claim follows from `sh_le_sh_of_le h _ hx`.
-/
theorem Dp_mono {s t : ℤ} (h : t ≤ s) {x : k⸨X⸩} (hx : x ∈ Dp k s) : x ∈ Dp k t :=
  sh_le_sh_of_le h _ hx

/- English proof (translation)
The claim follows from `mem_Dp.2 ⟨1, by simp⟩`.
-/
theorem zpow_mem (s : ℤ) : vv k ^ s ∈ Dp k s := mem_Dp.2 ⟨1, by simp⟩

/- English proof (translation)
Simplify using `using zpow_mem (k := k) s`.
-/
theorem pow_mem (s : ℕ) : vv k ^ s ∈ Dp k s := by simpa using zpow_mem (k := k) s

/- English proof (translation)
The claim follows from `mem_Dp_coeff.2 fun _ hm => HahnSeries.coeff_eq_zero_of_lt_order hm`.
-/
theorem order_mem (x : k⸨X⸩) : x ∈ Dp k x.order :=
  mem_Dp_coeff.2 fun _ hm => HahnSeries.coeff_eq_zero_of_lt_order hm

/- English proof (translation)
Introduce `h` and use `by simpa using mem_Dp_coeff.1 h 0 one_pos`.
-/
theorem one_not_mem : (1 : k⸨X⸩) ∉ Dp k 1 := fun h => by
  simpa using mem_Dp_coeff.1 h 0 one_pos

/- English proof (translation)
The claim follows from `mem_Dp_zero.2 ⟨(1 + PowerSeries.X) ^ j, by simp [vv_eq_coe_X]⟩`.
-/
theorem one_add_pow_mem (j : ℕ) : (1 + vv k) ^ j ∈ Dp k 0 :=
  mem_Dp_zero.2 ⟨(1 + PowerSeries.X) ^ j, by simp [vv_eq_coe_X]⟩

/- English proof (translation)
Establish `h0` using `congrArg (fun a : k⟦X⟧ => (a : k⸨X⸩)) (powerSeries_oneAddConstMulX_mul_inv (1 : k))`. Simplify using `only [map_one, one_mul, map_mul, map_add, ← vv_eq_coe_X] at h0`. Use `Dp_mul (coe_mem (inv1 (1 : k))) h (u := s) (by simp)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_comm _ (1 + vv k), h0, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_of_one_add_mul {s : ℤ} {x : k⸨X⸩} (h : (1 + vv k) * x ∈ Dp k s) : x ∈ Dp k s := by
  have h0 := congrArg (fun a : k⟦X⟧ => (a : k⸨X⸩)) (powerSeries_oneAddConstMulX_mul_inv (1 : k))
  simp only [map_one, one_mul, map_mul, map_add, ← vv_eq_coe_X] at h0
  have := Dp_mul (coe_mem (inv1 (1 : k))) h (u := s) (by simp)
  rwa [← mul_assoc, mul_comm _ (1 + vv k), h0, one_mul] at this

/- English proof (translation)
Take `⟨u, hu⟩` from `hv`. Take `⟨b, rfl⟩` from `mem_Dp.1 hx`. Take `⟨c, hc⟩` from `hint b`. Use `mem_Dp.2 ⟨((u ^ a : (k⟦X⟧)ˣ) : k⟦X⟧) * c, ?_⟩` and prove the remaining obligations. Establish `: ((((u ^ a : (k⟦X⟧)ˣ) : k⟦X⟧)) : k⸨X⸩) = (((u : k⟦X⟧)) : k⸨X⸩) ^ a`.

Establish `h` using `map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k).toMonoidHom) u a`. Establish `h2` using `congrArg Units.val h`. Rewrite `h2` using `[Units.val_zpow_eq_zpow_val]`. Conclude with `h2`. Rewrite using `[map_mul, map_zpow₀, hu, hc, map_mul, this, mul_zpow, zpow_mul, zpow_natCast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_mem {σ : k⸨X⸩ →+* k⸨X⸩} (hint : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = (b : k⸨X⸩)) {e : ℕ}
    (hv : ∃ u : (k⟦X⟧)ˣ, σ (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ e) {a : ℤ} {x : k⸨X⸩} (hx : x ∈ Dp k a) :
    σ x ∈ Dp k (e * a) := by
  obtain ⟨u, hu⟩ := hv
  obtain ⟨b, rfl⟩ := mem_Dp.1 hx
  obtain ⟨c, hc⟩ := hint b
  refine mem_Dp.2 ⟨((u ^ a : (k⟦X⟧)ˣ) : k⟦X⟧) * c, ?_⟩
  have : ((((u ^ a : (k⟦X⟧)ˣ) : k⟦X⟧)) : k⸨X⸩) = (((u : k⟦X⟧)) : k⸨X⸩) ^ a := by
    have h := map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k).toMonoidHom) u a
    have h2 := congrArg Units.val h
    rw [Units.val_zpow_eq_zpow_val] at h2
    exact h2
  rw [map_mul, map_zpow₀, hu, hc, map_mul, this, mul_zpow, zpow_mul, zpow_natCast]
  ring

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Assume the negation of the conclusion as `hc`. Establish `h1 : x.order ≤ a - 1`.

Assume the negation of the conclusion as `h`. Conclude with `hc (Dp_mono (by omega) (order_mem x))`. Establish `h2 : x.order + (x⁻¹).order = 0`. Rewrite using `[← HahnSeries.order_mul h0 (inv_ne_zero h0), mul_inv_cancel₀ h0, HahnSeries.order_one]`. Establish `h3` using `map_mem hint hv (order_mem x⁻¹)`.

Establish `h4` using `Dp_mul hx h3 (u := 1) (by`. Establish `: (x⁻¹).order = -x.order` using `by omega`. Rewrite using `[this]`. Establish `: (0 : ℤ) ≤ e` using `by positivity`. Use the proof step `nlinarith)`.

Rewrite `h4` using `[← map_mul, mul_inv_cancel₀ h0, map_one]`. Conclude with `one_not_mem h4`.
-/
theorem mem_of_map_mem {σ : k⸨X⸩ →+* k⸨X⸩} (hint : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = (b : k⸨X⸩)) {e : ℕ}
    (hv : ∃ u : (k⟦X⟧)ˣ, σ (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ e) {a s : ℤ} (hs : e * (a - 1) < s)
    {x : k⸨X⸩} (hx : σ x ∈ Dp k s) : x ∈ Dp k a := by
  by_cases h0 : x = 0
  · rw [h0]; exact Submodule.zero_mem _
  by_contra hc
  have h1 : x.order ≤ a - 1 := by
    by_contra h
    exact hc (Dp_mono (by omega) (order_mem x))
  have h2 : x.order + (x⁻¹).order = 0 := by
    rw [← HahnSeries.order_mul h0 (inv_ne_zero h0), mul_inv_cancel₀ h0, HahnSeries.order_one]
  have h3 := map_mem hint hv (order_mem x⁻¹)
  have h4 := Dp_mul hx h3 (u := 1) (by
    have : (x⁻¹).order = -x.order := by omega
    rw [this]
    have : (0 : ℤ) ≤ e := by positivity
    nlinarith)
  rw [← map_mul, mul_inv_cancel₀ h0, map_one] at h4
  exact one_not_mem h4

end Filt

section Psi
variable (k : Type) [Field k] (l : ℕ) [hl : Fact l.Prime]

def psiPi : k⸨X⸩ →ₗ[k] k⸨X⸩ := PsiBasis.psi l hl.out.pos

/- English proof (translation)
Use `split_ifs with h`. Take `⟨q, rfl⟩` from `h`. Rewrite using `[phiPi_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast hl.out.ne_zero)]`. Conclude with `phiPi_coeff_not k l x m h`.
-/
theorem phi_coeff (x : k⸨X⸩) (m : ℤ) :
    (phiPi k l x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0 := by
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [phiPi_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast hl.out.ne_zero)]
  · exact phiPi_coeff_not k l x m h

/- English proof (translation)
Establish `hl' : (0 : ℤ) < l` using `by exact_mod_cast hl.out.pos`. Rewrite `hx`, the goal using `[mem_Dp_coeff]`. Introduce `m hm`. Rewrite using `[phi_coeff]`. Use `split_ifs with h`.

Take `⟨q, rfl⟩` from `h`. Rewrite using `[Int.mul_ediv_cancel_left _ hl'.ne']`. Conclude with `hx q (lt_of_mul_lt_mul_left hm hl'.le)`. Both sides reduce to the same expression.
-/
theorem phi_mem {s : ℤ} {x : k⸨X⸩} (hx : x ∈ Dp k s) : phiPi k l x ∈ Dp k (l * s) := by
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  rw [mem_Dp_coeff] at hx ⊢
  intro m hm
  rw [phi_coeff]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Int.mul_ediv_cancel_left _ hl'.ne']
    exact hx q (lt_of_mul_lt_mul_left hm hl'.le)
  · rfl

/- English proof (translation)
Rewrite using `[psiPi, PsiBasis.psi_apply]`. Establish `: ∀ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • PsiBasis.comp l hl.out.pos i ((1 + vv k) ^ j * phiPi k l a) = ((-1 : ℤ) ^ i * (j.choose i : ℤ)) • a`. Introduce `i hi`. Use `PsiBasis.comp_one_add_pow_mul l hl.out.pos (phiPi k l) (phi_coeff k l) (Finset.mem_range.1 hi) hj a` as an intermediate fact. Rewrite using `[vv, this, mul_smul, natCast_zsmul]`.

Rewrite using `[Finset.sum_congr rfl this, ← Finset.sum_smul, ← Finset.sum_subset (Finset.range_subset_range.2 (show j + 1 ≤ l from hj)), Int.alternating_sum_range_choose]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `i _ hi`. Rewrite using `[Nat.choose_eq_zero_of_lt (by simpa using hi)]`. Simplify using the standard rewrite rules.
-/
theorem psi_pow_mul {j : ℕ} (hj : j < l) (a : k⸨X⸩) :
    psiPi k l ((1 + vv k) ^ j * phiPi k l a) = if j = 0 then a else 0 := by
  rw [psiPi, PsiBasis.psi_apply]
  have : ∀ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • PsiBasis.comp l hl.out.pos i ((1 + vv k) ^ j * phiPi k l a)
      = ((-1 : ℤ) ^ i * (j.choose i : ℤ)) • a := by
    intro i hi
    have := PsiBasis.comp_one_add_pow_mul l hl.out.pos (phiPi k l) (phi_coeff k l) (Finset.mem_range.1 hi) hj a
    rw [vv, this, mul_smul, natCast_zsmul]
  rw [Finset.sum_congr rfl this, ← Finset.sum_smul,
    ← Finset.sum_subset (Finset.range_subset_range.2 (show j + 1 ≤ l from hj)),
    Int.alternating_sum_range_choose]
  · split_ifs <;> simp
  · intro i _ hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]
    simp

/- English proof (translation)
Rewrite using `[assemble, map_sum, Finset.sum_eq_single 0]`. Rewrite using `[psi_pow_mul k l (0 : Fin l).2, if_pos (by simp)]`. Introduce `j _ hj`. Rewrite using `[psi_pow_mul k l j.2, if_neg (by simpa using hj)]`. Simplify using the standard rewrite rules.
-/
theorem psi_assemble (y : Fin l → k⸨X⸩) : psiPi k l (assemble k l y) = y 0 := by
  rw [assemble, map_sum, Finset.sum_eq_single 0]
  · rw [psi_pow_mul k l (0 : Fin l).2, if_pos (by simp)]
  · intro j _ hj
    rw [psi_pow_mul k l j.2, if_neg (by simpa using hj)]
  · simp

/- English proof (translation)
Rewrite using `[psiPi, PsiBasis.psi_apply, HahnSeries.coeff_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[HahnSeries.coeff_smul, PsiBasis.comp_coeff]`.
-/
theorem psi_coeff (y : k⸨X⸩) (m : ℤ) :
    (psiPi k l y).coeff m = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • y.coeff (l * m + i) := by
  rw [psiPi, PsiBasis.psi_apply, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HahnSeries.coeff_smul, PsiBasis.comp_coeff]

/- English proof (translation)
Establish `hl' : (0 : ℤ) < l` using `by exact_mod_cast hl.out.pos`. Rewrite `hy`, the goal using `[mem_Dp_coeff]`. Introduce `m hm`. Rewrite using `[psi_coeff]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations.

Establish `hi' : (i : ℤ) < l` using `by exact_mod_cast Finset.mem_range.1 hi`. Rewrite using `[hy, smul_zero]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem psi_mem {s t : ℤ} (h : l * t ≤ s) {y : k⸨X⸩} (hy : y ∈ Dp k s) : psiPi k l y ∈ Dp k t := by
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  rw [mem_Dp_coeff] at hy ⊢
  intro m hm
  rw [psi_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : (i : ℤ) < l := by exact_mod_cast Finset.mem_range.1 hi
  rw [hy, smul_zero]
  nlinarith

/- English proof (translation)
Establish `h1` using `hl.out.pos`. Rewrite using `[psi_coeff, Finset.sum_eq_single (l - 1)]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Introduce `i hi hne`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Rewrite using `[mem_Dp_coeff.1 hy, smul_zero]`. Use linear arithmetic over natural numbers and integers. Introduce `h; exact absurd (Finset.mem_range.2 (by omega)) h`.
-/
theorem psi_coeff_zero {y : k⸨X⸩} (hy : y ∈ Dp k (l - 1)) :
    (psiPi k l y).coeff 0 = ((-1 : ℤ) ^ (l - 1)) • y.coeff (l - 1) := by
  have h1 := hl.out.pos
  rw [psi_coeff, Finset.sum_eq_single (l - 1)]
  · congr 2; omega
  · intro i hi hne
    have := Finset.mem_range.1 hi
    rw [mem_Dp_coeff.1 hy, smul_zero]
    omega
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/- English proof (translation)
Establish `h1` using `psi_coeff_zero k l hy`. Rewrite `h1` using `[h, HahnSeries.coeff_zero, eq_comm, zsmul_eq_mul, mul_eq_zero]`. Establish `h2` using `h1.resolve_left (by simp)`. Use `mem_Dp_coeff.2 fun m hm => ?_` and prove the remaining obligations. Break down `eq_or_ne m (l - 1) with rfl | hne` into its components or cases.

Conclude with `h2`. Conclude with `mem_Dp_coeff.1 hy m (by omega)`.
-/
theorem mem_of_psi_eq_zero {y : k⸨X⸩} (hy : y ∈ Dp k (l - 1)) (h : psiPi k l y = 0) : y ∈ Dp k l := by
  have h1 := psi_coeff_zero k l hy
  rw [h, HahnSeries.coeff_zero, eq_comm, zsmul_eq_mul, mul_eq_zero] at h1
  have h2 := h1.resolve_left (by simp)
  refine mem_Dp_coeff.2 fun m hm => ?_
  rcases eq_or_ne m (l - 1) with rfl | hne
  · exact h2
  · exact mem_Dp_coeff.1 hy m (by omega)

/- English proof (translation)
Take `⟨y, rfl⟩` from `(assemble_bijective k l).2 x`. Establish `: phiPi k l a * assemble k l y = assemble k l (fun j => a * y j)`. Simplify using `only [assemble, Finset.mul_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[this, psi_assemble, psi_assemble]`.
-/
theorem psi_phi_mul (a x : k⸨X⸩) : psiPi k l (phiPi k l a * x) = a * psiPi k l x := by
  obtain ⟨y, rfl⟩ := (assemble_bijective k l).2 x
  have : phiPi k l a * assemble k l y = assemble k l (fun j => a * y j) := by
    simp only [assemble, Finset.mul_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, psi_assemble, psi_assemble]

/- English proof (translation)
Take `⟨y, rfl⟩` from `(assemble_bijective k l).2 x`. Rewrite using `[psi_assemble, assemble, map_sum, map_sum, Finset.sum_eq_single 0]`. Use `psi_pow_mul k l hl.out.pos (σ (y 0))` as an intermediate fact. Simplify `this` using `[hφ]`. Introduce `j _ hj0`.

Take `⟨i, w, h0, h1, h2⟩` from `hj j (Nat.pos_of_ne_zero (by simpa using hj0)) j.2`. Rewrite using `[map_mul, h2, hφ, mul_assoc, ← map_mul, psi_pow_mul k l h1, if_neg h0.ne']`. Simplify using the standard rewrite rules.
-/
theorem psi_comm (σ : k⸨X⸩ →+* k⸨X⸩) (hφ : ∀ x, σ (phiPi k l x) = phiPi k l (σ x))
    (hj : ∀ j : ℕ, 0 < j → j < l → ∃ (i : ℕ) (w : k⸨X⸩), 0 < i ∧ i < l ∧
      σ ((1 + vv k) ^ j) = (1 + vv k) ^ i * phiPi k l w) (x : k⸨X⸩) :
    psiPi k l (σ x) = σ (psiPi k l x) := by
  obtain ⟨y, rfl⟩ := (assemble_bijective k l).2 x
  rw [psi_assemble, assemble, map_sum, map_sum, Finset.sum_eq_single 0]
  · have := psi_pow_mul k l hl.out.pos (σ (y 0))
    simpa [hφ] using this
  · intro j _ hj0
    obtain ⟨i, w, h0, h1, h2⟩ := hj j (Nat.pos_of_ne_zero (by simpa using hj0)) j.2
    rw [map_mul, h2, hφ, mul_assoc, ← map_mul, psi_pow_mul k l h1, if_neg h0.ne']
  · simp

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun j _ => Dp_mul (one_add_pow_mem j) (phi_mem k l (h j)) (by simp)`.
-/
theorem assemble_mem {s : ℤ} {y : Fin l → k⸨X⸩} (h : ∀ j, y j ∈ Dp k s) : assemble k l y ∈ Dp k (l * s) :=
  Submodule.sum_mem _ fun j _ => Dp_mul (one_add_pow_mem j) (phi_mem k l (h j)) (by simp)

variable [CharP k l]

/- English proof (translation)
Use `haveI : CharP k⸨X⸩ l := charP_of_injective_algebraMap (algebraMap k k⸨X⸩).injective l`. Rewrite using `[map_add, map_one, phiPi_vv, add_pow_char, one_pow]`.
-/
theorem phi_one_add : phiPi k l (1 + vv k) = (1 + vv k) ^ l := by
  haveI : CharP k⸨X⸩ l := charP_of_injective_algebraMap (algebraMap k k⸨X⸩).injective l
  rw [map_add, map_one, phiPi_vv, add_pow_char, one_pow]

/- English proof (translation)
Establish `h1` using `psi_mem k l le_rfl (Dp_mul (one_add_pow_mem (l - j)) h (u := l * s) (by simp))`. Apply `mem_of_one_add_mul` to reduce the goal to its premises. Use `h1 using 1` and compare the differences between its conclusion and the goal. Establish `hj` using `j.2`. Establish `key : ∀ i : Fin l, (j : ℕ) ≤ i → (1 + vv k) ^ (l - j) * ((1 + vv k) ^ (i : ℕ) * phiPi k l (y i)) = (1 + vv k) ^ ((i : ℕ) - j) * phiPi k l ((1 + vv k) * y i)`.

Introduce `i hi`. Rewrite using `[map_mul, phi_one_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[assemble, Finset.mul_sum, map_sum, Finset.sum_eq_single j]`.

Rewrite using `[key j le_rfl, psi_pow_mul k l (by omega), if_pos (by omega)]`. Introduce `i _ hi`. Establish `hi' : (i : ℕ) ≠ j` using `fun e => hi (Fin.ext e)`. Use `i.2` as an intermediate fact. Break down `lt_or_ge (i : ℕ) j with h2 | h2` into its components or cases.

Rewrite using `[← mul_assoc, ← pow_add, psi_pow_mul k l (by omega), if_neg (by omega)]`. Rewrite using `[key i h2, psi_pow_mul k l (by omega), if_neg (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem mem_of_assemble_mem {s : ℤ} {y : Fin l → k⸨X⸩} (h : assemble k l y ∈ Dp k (l * s)) (j : Fin l) :
    y j ∈ Dp k s := by
  have h1 := psi_mem k l le_rfl (Dp_mul (one_add_pow_mem (l - j)) h (u := l * s) (by simp))
  apply mem_of_one_add_mul
  convert h1 using 1
  have hj := j.2
  have key : ∀ i : Fin l, (j : ℕ) ≤ i → (1 + vv k) ^ (l - j) * ((1 + vv k) ^ (i : ℕ) * phiPi k l (y i)) =
      (1 + vv k) ^ ((i : ℕ) - j) * phiPi k l ((1 + vv k) * y i) := by
    intro i hi
    rw [map_mul, phi_one_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    congr 2; omega
  rw [assemble, Finset.mul_sum, map_sum, Finset.sum_eq_single j]
  · rw [key j le_rfl, psi_pow_mul k l (by omega), if_pos (by omega)]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ j := fun e => hi (Fin.ext e)
    have := i.2
    rcases lt_or_ge (i : ℕ) j with h2 | h2
    · rw [← mul_assoc, ← pow_add, psi_pow_mul k l (by omega), if_neg (by omega)]
    · rw [key i h2, psi_pow_mul k l (by omega), if_neg (by omega)]
  · simp

end Psi

section Delta
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]

/- English proof (translation)
Simplify using `only [onePlusPow, PowerSeries.binomialSeries_add, map_mul]`.
-/
theorem opp_add (z w : ℤ_[l]) : onePlusPow k l (z + w) = onePlusPow k l z * onePlusPow k l w := by
  simp only [onePlusPow, PowerSeries.binomialSeries_add, map_mul]

/- English proof (translation)
The claim follows from `FrobeniusBinomialReduction.binomPow_natCast k l m`.
-/
theorem opp_nat (m : ℕ) : onePlusPow k l (m : ℤ_[l]) = (1 + PowerSeries.X) ^ m :=
  FrobeniusBinomialReduction.binomPow_natCast k l m

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using opp_nat (k := k) (l := l) 0`. Consider the case `succ n ih => rw [Nat.cast_succ, add_mul, one_mul, opp_add, ih, pow_succ]`.
-/
theorem opp_mul (m : ℕ) (z : ℤ_[l]) : onePlusPow k l (m * z) = onePlusPow k l z ^ m := by
  induction m with
  | zero => simpa using opp_nat (k := k) (l := l) 0
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, opp_add, ih, pow_succ]

/- English proof (translation)
The claim follows from `PowerSeries.X_dvd_iff.2 (binom_const z)`.
-/
theorem opp_dvd (z : ℤ_[l]) : PowerSeries.X ∣ onePlusPow k l z - 1 :=
  PowerSeries.X_dvd_iff.2 (binom_const z)

/- English proof (translation)
Use `haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l`. Establish `hX : PowerSeries.X ∣ σ PowerSeries.X`. Rewrite `h` using `[map_add, map_one, ← eq_sub_iff_add_eq']`. Rewrite using `[h, PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules.

Establish `key : ∀ N : ℕ, PowerSeries.X ^ N ∣ σ (onePlusPow k l z) - onePlusPow k l z ^ m`. Introduce `N`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.1 (PadicInt.appr_spec N z)`. Establish `hz : z = (z.appr N : ℕ) + ((l ^ N : ℕ) : ℤ_[l]) * w` using `by push_cast; linear_combination hw`. Establish `h1 : PowerSeries.X ∣ σ (onePlusPow k l w) - onePlusPow k l w ^ m`.

Take `⟨c, hc⟩` from `opp_dvd (k := k) w`. Establish `h2 : PowerSeries.X ∣ σ (onePlusPow k l w) - 1`. Rewrite using `[← map_one σ, ← map_sub, hc, map_mul]`. Conclude with `hX.mul_right _`. Establish `h3 : PowerSeries.X ∣ onePlusPow k l w ^ m - 1` using `(opp_dvd w).trans (by simpa using sub_dvd_pow_sub_pow (onePlusPow k l w) 1 m)`.

Simplify using `using dvd_sub h2 h3`. Rewrite using `[hz, opp_add, opp_nat, opp_mul, map_mul, map_pow, map_pow, h, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm m, ← mul_sub, mul_comm (l ^ N) m, pow_mul (onePlusPow k l w), ← sub_pow_char_pow]`. Conclude with `((pow_dvd_pow _ (Nat.lt_pow_self hl.out.one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)).mul_left _`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `n`.

Conclude with `PowerSeries.X_pow_dvd_iff.1 (key (n + 1)) n (by omega)`.
-/
theorem hom_opp (σ : k⟦X⟧ →+* k⟦X⟧) (m : ℕ) (h : σ (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ m) (z : ℤ_[l]) :
    σ (onePlusPow k l z) = onePlusPow k l z ^ m := by
  haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  have hX : PowerSeries.X ∣ σ PowerSeries.X := by
    rw [map_add, map_one, ← eq_sub_iff_add_eq'] at h
    rw [h, PowerSeries.X_dvd_iff]; simp
  have key : ∀ N : ℕ, PowerSeries.X ^ N ∣ σ (onePlusPow k l z) - onePlusPow k l z ^ m := by
    intro N
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N z)
    have hz : z = (z.appr N : ℕ) + ((l ^ N : ℕ) : ℤ_[l]) * w := by push_cast; linear_combination hw
    have h1 : PowerSeries.X ∣ σ (onePlusPow k l w) - onePlusPow k l w ^ m := by
      obtain ⟨c, hc⟩ := opp_dvd (k := k) w
      have h2 : PowerSeries.X ∣ σ (onePlusPow k l w) - 1 := by
        rw [← map_one σ, ← map_sub, hc, map_mul]; exact hX.mul_right _
      have h3 : PowerSeries.X ∣ onePlusPow k l w ^ m - 1 :=
        (opp_dvd w).trans (by simpa using sub_dvd_pow_sub_pow (onePlusPow k l w) 1 m)
      simpa using dvd_sub h2 h3
    rw [hz, opp_add, opp_nat, opp_mul, map_mul, map_pow, map_pow, h, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
      mul_comm m, ← mul_sub, mul_comm (l ^ N) m, pow_mul (onePlusPow k l w), ← sub_pow_char_pow]
    exact ((pow_dvd_pow _ (Nat.lt_pow_self hl.out.one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)).mul_left _
  rw [← sub_eq_zero]
  ext n
  exact PowerSeries.X_pow_dvd_iff.1 (key (n + 1)) n (by omega)

def delPi (k : Type) [Field k] [CharP k l] (t : ℤ_[l]ˣ) : k⸨X⸩ →+* k⸨X⸩ :=
  substHom (onePlusPow k l t - 1) (binom_const _) (binom_unit_ne t)

/- English proof (translation)
The claim follows from `substHom_coe _ _ _ a`.
-/
theorem delPi_coe (t : ℤ_[l]ˣ) (a : k⟦X⟧) :
    delPi k t (a : k⸨X⸩) = ((a.subst (onePlusPow k l t - 1) : k⟦X⟧) : k⸨X⸩) := substHom_coe _ _ _ a

/- English proof (translation)
The claim follows from `substL_eq _ (binom_const _) (binom_unit_ne t) x`.
-/
theorem delPi_eq (t : ℤ_[l]ˣ) (x : k⸨X⸩) : FrobeniusBinomialReduction.actπ k l t x = delPi k t x :=
  substL_eq _ (binom_const _) (binom_unit_ne t) x

/- English proof (translation)
Establish `ha` using `PowerSeries.HasSubst.of_constantCoeff_zero' h0`. Establish `hb : PowerSeries.HasSubst (onePlusPow k l t - 1)` using `PowerSeries.HasSubst.of_constantCoeff_zero' (binom_const (k := k) (t : ℤ_[l]))`. Establish `key : PowerSeries.subst (onePlusPow k l t - 1) ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) = PowerSeries.subst ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) (onePlusPow k l t - 1)`. Use `hom_opp (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom m (by simp [PowerSeries.substAlgHom_X]) t` as an intermediate fact. Rewrite using `[← PowerSeries.coe_substAlgHom ha, ← PowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_pow, map_add, PowerSeries.substAlgHom_X, map_one, map_one]`.

Rewrite using `[show (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧) (onePlusPow k l t) = _ from this]`. Simplify using the standard rewrite rules. Establish `: (delPi k t).comp (substHom _ h0 h1) = (substHom _ h0 h1).comp (delPi k t)`. Use `hom_ext fun a => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, delPi_coe, substHom_coe]`.

Rewrite using `[PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_comp_subst_apply hb ha, key]`. Conclude with `RingHom.congr_fun this x`.
-/
theorem delPi_comm (t : ℤ_[l]ˣ) (m : ℕ) (h0 : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) = 0)
    (h1 : ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) ≠ 0) (x : k⸨X⸩) :
    delPi k t (substHom _ h0 h1 x) = substHom _ h0 h1 (delPi k t x) := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hb : PowerSeries.HasSubst (onePlusPow k l t - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (binom_const (k := k) (t : ℤ_[l]))
  have key : PowerSeries.subst (onePlusPow k l t - 1) ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) =
      PowerSeries.subst ((1 + PowerSeries.X : k⟦X⟧) ^ m - 1) (onePlusPow k l t - 1) := by
    have := hom_opp (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom m
      (by simp [PowerSeries.substAlgHom_X]) t
    rw [← PowerSeries.coe_substAlgHom ha, ← PowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_pow, map_add,
      PowerSeries.substAlgHom_X, map_one, map_one]
    rw [show (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧) (onePlusPow k l t) = _ from this]
    simp
  have : (delPi k t).comp (substHom _ h0 h1) = (substHom _ h0 h1).comp (delPi k t) := by
    refine hom_ext fun a => ?_
    simp only [RingHom.comp_apply, delPi_coe, substHom_coe]
    rw [PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_comp_subst_apply hb ha, key]
  exact RingHom.congr_fun this x

/- English proof (translation)
Use `haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l`. Rewrite using `[add_pow_char]`. Simplify using the standard rewrite rules.
-/
theorem frob_eq : ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = PowerSeries.X ^ l := by
  haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  rw [add_pow_char]; simp

/- English proof (translation)
Rewrite using `[frob_eq]`. Conclude with `pow_ne_zero _ PowerSeries.X_ne_zero`.
-/
theorem frob_ne : ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) ≠ 0 := by
  rw [frob_eq]; exact pow_ne_zero _ PowerSeries.X_ne_zero

/- English proof (translation)
Rewrite using `[phiPi_eq, FrobeniusBinomialReduction.frobπ, ← substL_eq, frob_eq]`.
-/
theorem phi_eq_subst (x : k⸨X⸩) :
    phiPi k l x = substHom ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) (by simp) frob_ne x := by
  rw [phiPi_eq, FrobeniusBinomialReduction.frobπ, ← substL_eq, frob_eq]

/- English proof (translation)
Rewrite using `[phi_eq_subst, phi_eq_subst, delPi_comm]`.
-/
theorem del_phi (t : ℤ_[l]ˣ) (x : k⸨X⸩) : delPi k t (phiPi k l x) = phiPi k l (delPi k t x) := by
  rw [phi_eq_subst, phi_eq_subst, delPi_comm]

/- English proof (translation)
Establish `ha : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1)` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)`. Use `hom_opp (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom l (by simp [PowerSeries.substAlgHom_X]) w` as an intermediate fact. Rewrite using `[phi_eq_subst, substHom_coe, ← this, ← PowerSeries.coe_substAlgHom ha]`. Both sides reduce to the same expression.
-/
theorem phi_opp (w : ℤ_[l]) :
    phiPi k l (onePlusPow k l w : k⟦X⟧) = ((onePlusPow k l w ^ l : k⟦X⟧) : k⸨X⸩) := by
  have ha : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have := hom_opp (PowerSeries.substAlgHom ha : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom l
      (by simp [PowerSeries.substAlgHom_X]) w
  rw [phi_eq_subst, substHom_coe, ← this, ← PowerSeries.coe_substAlgHom ha]
  rfl

/- English proof (translation)
Rewrite using `[map_add, map_one, vv_eq, delPi_coe, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (show PowerSeries.constantCoeff (onePlusPow k l t - 1) = 0 from binom_const _))]`. Simplify using the standard rewrite rules.
-/
theorem del_one_add (t : ℤ_[l]ˣ) : delPi k t (1 + vv k) = ((onePlusPow k l t : k⟦X⟧) : k⸨X⸩) := by
  rw [map_add, map_one, vv_eq, delPi_coe,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
      (show PowerSeries.constantCoeff (onePlusPow k l t - 1) = 0 from binom_const _))]
  simp

/- English proof (translation)
Use `psi_comm k l _ (del_phi t) (fun j h0 h1 => ?_) x` and prove the remaining obligations. Take `⟨i, hi, hm⟩` from `PadicInt.exists_mem_range ((j : ℤ_[l]) * (t : ℤ_[l]))`. Rewrite `hm` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Take `⟨w, hw⟩` from `hm`. Use `⟨i, (onePlusPow k l w : k⟦X⟧), Nat.pos_of_ne_zero ?_, hi, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Establish `h2 : (l : ℤ_[l]) ∣ (j : ℤ_[l])`. Rewrite using `[← Units.dvd_mul_right (u := t)]; exact ⟨w, by simpa using hw⟩`. Establish `h3 : ‖((j : ℤ) : ℤ_[l])‖ < 1`. Rewrite using `[PadicInt.norm_lt_one_iff_dvd]`.

Simplify using `using h2`. Rewrite `h3` using `[PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast]`. Conclude with `absurd (Nat.le_of_dvd h0 h3) (by omega)`. Rewrite using `[map_pow, del_one_add, phi_opp, ← map_pow, ← opp_mul, ← opp_mul, eq_add_of_sub_eq' hw, opp_add, opp_nat]`. Simplify using `[vv_eq]`.
-/
theorem psi_del (t : ℤ_[l]ˣ) (x : k⸨X⸩) : psiPi k l (delPi k t x) = delPi k t (psiPi k l x) := by
  refine psi_comm k l _ (del_phi t) (fun j h0 h1 => ?_) x
  obtain ⟨i, hi, hm⟩ := PadicInt.exists_mem_range ((j : ℤ_[l]) * (t : ℤ_[l]))
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  refine ⟨i, (onePlusPow k l w : k⟦X⟧), Nat.pos_of_ne_zero ?_, hi, ?_⟩
  · rintro rfl
    have h2 : (l : ℤ_[l]) ∣ (j : ℤ_[l]) := by
      rw [← Units.dvd_mul_right (u := t)]; exact ⟨w, by simpa using hw⟩
    have h3 : ‖((j : ℤ) : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]; simpa using h2
    rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at h3
    exact absurd (Nat.le_of_dvd h0 h3) (by omega)
  · rw [map_pow, del_one_add, phi_opp, ← map_pow, ← opp_mul, ← opp_mul, eq_add_of_sub_eq' hw, opp_add, opp_nat]
    simp [vv_eq]

def gamPi (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] : k⸨X⸩ →ₐ[k] k⸨X⸩ :=
  extend (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (gam_const (k := k) (l := l))))
    (by rw [PowerSeries.substAlgHom_X]; exact gam_ne)

/- English proof (translation)
Establish `: (gamPi k l : k⸨X⸩ →+* k⸨X⸩) = substHom _ (gam_const (k` using `k) (l := l)) gam_ne := by`. Use `hom_ext fun a => ?_` and prove the remaining obligations. Rewrite using `[substHom_coe, RingHom.coe_coe, gamPi, extend_coe, PowerSeries.coe_substAlgHom]`. Conclude with `RingHom.congr_fun this x`.
-/
theorem gamPi_eq (x : k⸨X⸩) : gamPi k l x = substHom _ (gam_const (k := k) (l := l)) gam_ne x := by
  have : (gamPi k l : k⸨X⸩ →+* k⸨X⸩) = substHom _ (gam_const (k := k) (l := l)) gam_ne := by
    refine hom_ext fun a => ?_
    rw [substHom_coe, RingHom.coe_coe, gamPi, extend_coe, PowerSeries.coe_substAlgHom]
  exact RingHom.congr_fun this x

/- English proof (translation)
Rewrite using `[gamPi_eq, FrobeniusBinomialReduction.gamπ, substL_eq]`.
-/
theorem gamPi_eq' (x : k⸨X⸩) : FrobeniusBinomialReduction.gamπ k l x = gamPi k l x := by
  rw [gamPi_eq, FrobeniusBinomialReduction.gamπ, substL_eq]

/- English proof (translation)
Rewrite using `[gamPi_eq, gamPi_eq, delPi_comm]`.
-/
theorem del_gam (t : ℤ_[l]ˣ) (x : k⸨X⸩) : delPi k t (gamPi k l x) = gamPi k l (delPi k t x) := by
  rw [gamPi_eq, gamPi_eq, delPi_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, extend_coe _ _ a⟩`.
-/
theorem gam_int (a : k⟦X⟧) : ∃ b : k⟦X⟧, gamPi k l (a : k⸨X⸩) = b := ⟨_, extend_coe _ _ a⟩

/- English proof (translation)
Rewrite using `[map_add, map_one, vv_eq, gamPi, extend_coe, PowerSeries.substAlgHom_X]`. Simplify using the standard rewrite rules.
-/
theorem gam_one_add : gamPi k l (1 + vv k) = (1 + vv k) ^ (1 + l) := by
  rw [map_add, map_one, vv_eq, gamPi, extend_coe, PowerSeries.substAlgHom_X]
  simp

/- English proof (translation)
Establish `ha : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1)` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)`. Establish `hb` using `PowerSeries.HasSubst.of_constantCoeff_zero' (gam_const (k := k) (l := l))`. Establish `: (gamPi k l : k⸨X⸩ →+* k⸨X⸩).comp (phiPi k l) = (phiPi k l).comp (gamPi k l : k⸨X⸩ →+* k⸨X⸩)`. Use `hom_ext fun a => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, gamPi_eq, phi_eq_subst, substHom_coe]`.

Rewrite using `[PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_comp_subst_apply hb ha]`. Use `congr 2`. Rewrite using `[← PowerSeries.coe_substAlgHom ha, ← PowerSeries.coe_substAlgHom hb]`. Simplify using `only [map_sub, map_pow, map_add, map_one, PowerSeries.substAlgHom_X, add_sub_cancel, ← pow_mul, mul_comm]`. Conclude with `RingHom.congr_fun this x`.
-/
theorem gam_phi (x : k⸨X⸩) : gamPi k l (phiPi k l x) = phiPi k l (gamPi k l x) := by
  have ha : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hb := PowerSeries.HasSubst.of_constantCoeff_zero' (gam_const (k := k) (l := l))
  have : (gamPi k l : k⸨X⸩ →+* k⸨X⸩).comp (phiPi k l) = (phiPi k l).comp (gamPi k l : k⸨X⸩ →+* k⸨X⸩) := by
    refine hom_ext fun a => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, gamPi_eq, phi_eq_subst, substHom_coe]
    rw [PowerSeries.subst_comp_subst_apply ha hb, PowerSeries.subst_comp_subst_apply hb ha]
    congr 2
    rw [← PowerSeries.coe_substAlgHom ha, ← PowerSeries.coe_substAlgHom hb]
    simp only [map_sub, map_pow, map_add, map_one, PowerSeries.substAlgHom_X, add_sub_cancel, ← pow_mul, mul_comm]
  exact RingHom.congr_fun this x

/- English proof (translation)
Rewrite using `[map_pow, map_pow, gam_one_add, phi_one_add, ← mul_pow, pow_add, pow_one]`.
-/
theorem gam_pow (j : ℕ) : gamPi k l ((1 + vv k) ^ j) = (1 + vv k) ^ j * phiPi k l ((1 + vv k) ^ j) := by
  rw [map_pow, map_pow, gam_one_add, phi_one_add, ← mul_pow, pow_add, pow_one]

/- English proof (translation)
The claim follows from `psi_comm k l (gamPi k l : k⸨X⸩ →+* k⸨X⸩) gam_phi (fun j h0 h1 => ⟨j, _, h0, h1, gam_pow j⟩) x`.
-/
theorem psi_gam (x : k⸨X⸩) : psiPi k l (gamPi k l x) = gamPi k l (psiPi k l x) :=
  psi_comm k l (gamPi k l : k⸨X⸩ →+* k⸨X⸩) gam_phi (fun j h0 h1 => ⟨j, _, h0, h1, gam_pow j⟩) x

/- English proof (translation)
Use `haveI : CharP k⸨X⸩ l := charP_of_injective_algebraMap (algebraMap k k⸨X⸩).injective l`. Establish `h` using `gam_one_add (k := k) (l := l)`. Rewrite `h` using `[map_add, map_one, pow_add, pow_one, add_pow_char, one_pow]`. Take `⟨e, he⟩ : ∃ e, l = e + 3` from `⟨l - 3, by omega⟩`. Rewrite `h` using `[show vv k ^ l = vv k ^ (e + 3) by rw [← he]]`.

Use `⟨PowerSeries.X ^ e * (1 + PowerSeries.X), ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, map_add, map_one, ← vv_eq]`. Take the linear combination `h`.
-/
theorem gam_vv (h5 : 5 ≤ l) : ∃ c : k⟦X⟧, gamPi k l (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2) := by
  haveI : CharP k⸨X⸩ l := charP_of_injective_algebraMap (algebraMap k k⸨X⸩).injective l
  have h := gam_one_add (k := k) (l := l)
  rw [map_add, map_one, pow_add, pow_one, add_pow_char, one_pow] at h
  obtain ⟨e, he⟩ : ∃ e, l = e + 3 := ⟨l - 3, by omega⟩
  rw [show vv k ^ l = vv k ^ (e + 3) by rw [← he]] at h
  refine ⟨PowerSeries.X ^ e * (1 + PowerSeries.X), ?_⟩
  simp only [map_mul, map_pow, map_add, map_one, ← vv_eq]
  linear_combination h

/- English proof (translation)
Take `⟨c, hc⟩` from `gam_vv (k := k) h5`. Establish `step : ∀ (s : ℤ), s ≤ 1 → (∀ b : k⟦X⟧, gamPi k l b - b ∈ Dp k s) → ∀ b : k⟦X⟧, gamPi k l b - b ∈ Dp k (s + 1)`. Introduce `s hs h a`. Use `set b : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a`. Establish `ha : (a : k⸨X⸩) = vv k * (b : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff a)` using `by conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a, map_add, map_mul, ← vv_eq_coe_X]`.

Both sides reduce to the same expression. Take `⟨t, ht⟩` from `gam_int (l := l) b`. Establish `: gamPi k l a - a = vv k ^ 1 * (gamPi k l b - b) + vv k ^ 3 * ((c * t : k⟦X⟧) : k⸨X⸩)`. Rewrite using `[ha, map_add (gamPi k l), map_mul (gamPi k l), AlgHom.commutes, hc, ht, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (Dp_mul (pow_mem 1) (h b) (by omega)) (Dp_mul (pow_mem 3) (coe_mem _) (by omega))`. Take `⟨a, rfl⟩` from `mem_Dp_zero.1 hx`. Use `step 1 le_rfl (step 0 zero_le_one fun b => ?_) a` and prove the remaining obligations. Take `⟨t, ht⟩` from `gam_int (l := l) b`.

Rewrite using `[ht]`. Conclude with `Submodule.sub_mem _ (coe_mem _) (coe_mem _)`.
-/
theorem gam_sub_mem (h5 : 5 ≤ l) {x : k⸨X⸩} (hx : x ∈ Dp k 0) : gamPi k l x - x ∈ Dp k 2 := by
  obtain ⟨c, hc⟩ := gam_vv (k := k) h5
  have step : ∀ (s : ℤ), s ≤ 1 → (∀ b : k⟦X⟧, gamPi k l b - b ∈ Dp k s) →
      ∀ b : k⟦X⟧, gamPi k l b - b ∈ Dp k (s + 1) := by
    intro s hs h a
    set b : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
    have ha : (a : k⸨X⸩) = vv k * (b : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff a) := by
      conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a, map_add, map_mul, ← vv_eq_coe_X]
      rfl
    obtain ⟨t, ht⟩ := gam_int (l := l) b
    have : gamPi k l a - a = vv k ^ 1 * (gamPi k l b - b) + vv k ^ 3 * ((c * t : k⟦X⟧) : k⸨X⸩) := by
      rw [ha, map_add (gamPi k l), map_mul (gamPi k l), AlgHom.commutes, hc, ht, map_mul]; ring
    rw [this]
    exact Submodule.add_mem _ (Dp_mul (pow_mem 1) (h b) (by omega)) (Dp_mul (pow_mem 3) (coe_mem _) (by omega))
  obtain ⟨a, rfl⟩ := mem_Dp_zero.1 hx
  refine step 1 le_rfl (step 0 zero_le_one fun b => ?_) a
  obtain ⟨t, ht⟩ := gam_int (l := l) b
  rw [ht]
  exact Submodule.sub_mem _ (coe_mem _) (coe_mem _)

end Delta

section Core
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l] {n : ℕ}

def piLat (k : Type) [Field k] (n : ℕ) : Submodule k⟦X⟧ (Fin n → k⸨X⸩) :=
  Submodule.pi Set.univ fun _ => stdLat k

/- English proof (translation)
Simplify using `only [Dp, mem_sh_iff_smul_mem, piLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Pi.smul_apply]`.
-/
theorem mem_sh_piLat {s : ℤ} {y : Fin n → k⸨X⸩} : y ∈ sh s (piLat k n) ↔ ∀ i, y i ∈ Dp k s := by
  simp only [Dp, mem_sh_iff_smul_mem, piLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Pi.smul_apply]

/- English proof (translation)
Use `⟨Submodule.fg_pi fun _ => isLat_stdLat.1, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← (Pi.basisFun k⸨X⸩ (Fin n)).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩ i -`. Rewrite using `[Pi.basisFun_apply, Pi.single_apply]`.

Use `split_ifs`. Conclude with `mem_stdLat.2 ⟨1, map_one _⟩`. Conclude with `Submodule.zero_mem _`.
-/
theorem isLat_piLat : IsLat (piLat k n) := by
  refine ⟨Submodule.fg_pi fun _ => isLat_stdLat.1, ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun k⸨X⸩ (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩ i -
  rw [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  · exact mem_stdLat.2 ⟨1, map_one _⟩
  · exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨s, hs⟩` from `(Set.finite_range fun i => (y i).order).bddBelow`. Conclude with `⟨s, mem_sh_piLat.2 fun i => Dp_mono (hs ⟨i, rfl⟩) (order_mem _)⟩`.
-/
theorem exists_mem_sh (y : Fin n → k⸨X⸩) : ∃ s, y ∈ sh s (piLat k n) := by
  obtain ⟨s, hs⟩ := (Set.finite_range fun i => (y i).order).bddBelow
  exact ⟨s, mem_sh_piLat.2 fun i => Dp_mono (hs ⟨i, rfl⟩) (order_mem _)⟩

def semiOp (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : Matrix (Fin n) (Fin n) k⸨X⸩) : (Fin n → k⸨X⸩) →ₗ[k] (Fin n → k⸨X⸩) :=
  ((Matrix.toLin' H).restrictScalars k) ∘ₗ (lin σ).compLeft (Fin n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem semiOp_apply (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : Matrix (Fin n) (Fin n) k⸨X⸩) (y : Fin n → k⸨X⸩) (i : Fin n) :
    semiOp σ H y i = ∑ m, H i m * σ (y m) := rfl

/- English proof (translation)
Introduce `a x`. Use function extensionality and compare the values at `i`. Simplify using `only [semiOp_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem semi_semiOp (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : Matrix (Fin n) (Fin n) k⸨X⸩) : Semi σ (semiOp σ H) := by
  intro a x
  funext i
  simp only [semiOp_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use `TwistShift.bijOn_twist (gamPi k l) _ (semi_semiOp _ H) gam_int (gam_vv h5) _ isLat_piLat ?_ j ?_ s` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← sh_zero_eq (piLat k n), mem_sh_piLat]`. Use `mem_sh_piLat.2 fun i => ?_` and prove the remaining obligations. Establish `: (semiOp (gamPi k l) H x - x) i = ∑ m, (H - 1) i m * gamPi k l (x m) + (gamPi k l (x i) - x i)`.

Simplify using `[semiOp_apply, sub_mul, Matrix.one_apply]`. Rewrite using `[this]`. Use `Submodule.add_mem _ (Submodule.sum_mem _ fun m _ => Dp_mul (t := 0) (hH i m) ?_ (by simp)) (gam_sub_mem h5 (hx i))` and prove the remaining obligations. Take `⟨a, ha⟩` from `mem_Dp_zero.1 (hx m)`. Take `⟨b, hb⟩` from `gam_int (l := l) a`.

Rewrite using `[ha, hb]`. Conclude with `coe_mem _`. Rewrite using `[Ne, CharP.cast_eq_zero_iff k l]`. Conclude with `Nat.not_dvd_of_pos_of_lt h0 h1`.
-/
theorem twist_bij (h5 : 5 ≤ l) (H : Matrix (Fin n) (Fin n) k⸨X⸩) (hH : ∀ i m, (H - 1) i m ∈ Dp k 2)
    {j : ℕ} (h0 : 0 < j) (h1 : j < l) (s : ℤ) :
    Set.BijOn (fun y => (1 + vv k) ^ j • semiOp (gamPi k l) H y - y) (sh s (piLat k n)) (sh (s + 1) (piLat k n)) := by
  refine TwistShift.bijOn_twist (gamPi k l) _ (semi_semiOp _ H) gam_int (gam_vv h5) _ isLat_piLat ?_ j ?_ s
  · intro x hx
    rw [← sh_zero_eq (piLat k n), mem_sh_piLat] at hx
    refine mem_sh_piLat.2 fun i => ?_
    have : (semiOp (gamPi k l) H x - x) i =
        ∑ m, (H - 1) i m * gamPi k l (x m) + (gamPi k l (x i) - x i) := by
      simp [semiOp_apply, sub_mul, Matrix.one_apply]
    rw [this]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun m _ => Dp_mul (t := 0) (hH i m) ?_ (by simp))
      (gam_sub_mem h5 (hx i))
    obtain ⟨a, ha⟩ := mem_Dp_zero.1 (hx m)
    obtain ⟨b, hb⟩ := gam_int (l := l) a
    rw [ha, hb]; exact coe_mem _
  · rw [Ne, CharP.cast_eq_zero_iff k l]
    exact Nat.not_dvd_of_pos_of_lt h0 h1

/- English proof (translation)
Simplify using `only [assemble, map_sum, map_mul (gamPi k l), gam_pow, gam_phi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, semiOp_apply, map_sub, map_mul (phiPi k l), mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem op_assemble (H : Matrix (Fin n) (Fin n) k⸨X⸩) (y : Fin l → Fin n → k⸨X⸩) (i : Fin n) :
    ∑ m, phiPi k l (H i m) * gamPi k l (assemble k l fun j => y j m) - assemble k l (fun j => y j i) =
      assemble k l fun j => ((1 + vv k) ^ (j : ℕ) • semiOp (gamPi k l) H (y j) - y j) i := by
  simp only [assemble, map_sum, map_mul (gamPi k l), gam_pow, gam_phi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    semiOp_apply, map_sub, map_mul (phiPi k l), mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [CharP k l] in
/- English proof (translation)
Use `choose y hy using fun i => (assemble_bijective k l).2 (x i)`. Use `⟨fun j i => y i j, funext fun i => ?_, funext fun i => (hy i).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y i 0 = 0`. Rewrite using `[← psi_assemble k l (y i), hy, hx]`.
-/
theorem exists_assemble (x : Fin n → k⸨X⸩) (hx : ∀ i, psiPi k l (x i) = 0) :
    ∃ y : Fin l → Fin n → k⸨X⸩, y 0 = 0 ∧ x = fun i => assemble k l fun j => y j i := by
  choose y hy using fun i => (assemble_bijective k l).2 (x i)
  refine ⟨fun j i => y i j, funext fun i => ?_, funext fun i => (hy i).symm⟩
  change y i 0 = 0
  rw [← psi_assemble k l (y i), hy, hx]

variable (h5 : 5 ≤ l) (H : Matrix (Fin n) (Fin n) k⸨X⸩) (hH : ∀ i m, (H - 1) i m ∈ Dp k 2)
include h5 hH

/- English proof (translation)
Take `⟨y, h0, rfl⟩` from `exists_assemble x hx`. Rewrite using `[op_assemble, psi_assemble]`. Use `⟨by simp [h0], assemble_mem k l fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = 0`. Simplify using `[hj, h0]`.

Conclude with `mem_sh_piLat.1 ((twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).1 (mem_sh_piLat.2 fun i => mem_of_assemble_mem k l (hs i) j)) i`.
-/
theorem core_maps {s : ℤ} (x : Fin n → k⸨X⸩) (hx : ∀ i, psiPi k l (x i) = 0) (hs : ∀ i, x i ∈ Dp k (l * s))
    (i : Fin n) : psiPi k l (∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i) = 0 ∧
      ∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i ∈ Dp k (l * (s + 1)) := by
  obtain ⟨y, h0, rfl⟩ := exists_assemble x hx
  rw [op_assemble, psi_assemble]
  refine ⟨by simp [h0], assemble_mem k l fun j => ?_⟩
  by_cases hj : j = 0
  · simp [hj, h0]
  · exact mem_sh_piLat.1 ((twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).1
      (mem_sh_piLat.2 fun i => mem_of_assemble_mem k l (hs i) j)) i

/- English proof (translation)
Take `⟨y, h0, rfl⟩` from `exists_assemble x hx`. Establish `hz : assemble k l 0 = 0` using `by simp [assemble]`. Establish `: ∀ j, y j = 0`. Introduce `j`. Distinguish the cases in `hj : j = 0`.

Rewrite using `[hj, h0]`. Take `⟨s, hs⟩` from `exists_mem_sh (y j)`. Use `(twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).2.1 hs (Submodule.zero_mem _) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1` using `h i`.

Rewrite `h1` using `[op_assemble, ← hz]`. Simplify using `using congrFun ((assemble_bijective k l).1 h1) j`. Use function extensionality and compare the values at `i`. Simplify using `[this, assemble]`.
-/
theorem core_inj (x : Fin n → k⸨X⸩) (hx : ∀ i, psiPi k l (x i) = 0)
    (h : ∀ i, ∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i = 0) : x = 0 := by
  obtain ⟨y, h0, rfl⟩ := exists_assemble x hx
  have hz : assemble k l 0 = 0 := by simp [assemble]
  have : ∀ j, y j = 0 := by
    intro j
    by_cases hj : j = 0
    · rw [hj, h0]
    obtain ⟨s, hs⟩ := exists_mem_sh (y j)
    refine (twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).2.1 hs (Submodule.zero_mem _) ?_
    funext i
    have h1 := h i
    rw [op_assemble, ← hz] at h1
    simpa using congrFun ((assemble_bijective k l).1 h1) j
  funext i
  simp [this, assemble]

/- English proof (translation)
Take `⟨w, h0, rfl⟩` from `exists_assemble z hz`. Establish `: ∀ j : Fin l, ∃ y ∈ sh s (piLat k n), (j = 0 → y = 0) ∧ (1 + vv k) ^ (j : ℕ) • semiOp (gamPi k l) H y - y = w j`. Introduce `j`. Distinguish the cases in `hj : j = 0`. Conclude with `⟨0, Submodule.zero_mem _, fun _ => rfl, by simp [hj, h0]⟩`.

Take `⟨y, hy, h⟩` from `(twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).2.2 (mem_sh_piLat.2 fun i => mem_of_assemble_mem k l (hs i) j)`. Conclude with `⟨y, hy, fun e => absurd e hj, h⟩`. Use `choose y h1 h2 h3 using this`. Use `⟨fun i => assemble k l fun j => y j i, fun i => ?_, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[psi_assemble, h2 0 rfl]`.

Both sides reduce to the same expression. Conclude with `assemble_mem k l fun j => mem_sh_piLat.1 (h1 j) i`. Rewrite using `[op_assemble]`. Simplify using `only [h3]`.
-/
theorem core_surj {s : ℤ} (z : Fin n → k⸨X⸩) (hz : ∀ i, psiPi k l (z i) = 0) (hs : ∀ i, z i ∈ Dp k (l * (s + 1))) :
    ∃ x : Fin n → k⸨X⸩, (∀ i, psiPi k l (x i) = 0) ∧ (∀ i, x i ∈ Dp k (l * s)) ∧
      ∀ i, ∑ m, phiPi k l (H i m) * gamPi k l (x m) - x i = z i := by
  obtain ⟨w, h0, rfl⟩ := exists_assemble z hz
  have : ∀ j : Fin l, ∃ y ∈ sh s (piLat k n), (j = 0 → y = 0) ∧
      (1 + vv k) ^ (j : ℕ) • semiOp (gamPi k l) H y - y = w j := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, Submodule.zero_mem _, fun _ => rfl, by simp [hj, h0]⟩
    obtain ⟨y, hy, h⟩ := (twist_bij h5 H hH (Nat.pos_of_ne_zero (by simpa using hj)) j.2 s).2.2
      (mem_sh_piLat.2 fun i => mem_of_assemble_mem k l (hs i) j)
    exact ⟨y, hy, fun e => absurd e hj, h⟩
  choose y h1 h2 h3 using this
  refine ⟨fun i => assemble k l fun j => y j i, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [psi_assemble, h2 0 rfl]; rfl
  · exact assemble_mem k l fun j => mem_sh_piLat.1 (h1 j) i
  · rw [op_assemble]; simp only [h3]

end Core

end GlobalTheory.PsiShiftProof
