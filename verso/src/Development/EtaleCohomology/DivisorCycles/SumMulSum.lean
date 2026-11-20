import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

/- English proof (translation)
Rewrite using `[Finset.sum_mul, Finset.sum_eq_single k]`. Rewrite using `[smul_mul_assoc, (hS.1.idem k).eq]`. Introduce `j _ hj`. Rewrite using `[smul_mul_assoc, hS.1.ortho hj, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem sum_mul_p {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    (∑ j, d j • p j) * p k = d k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hS.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hS.1.ortho hj, smul_zero]
  · simp

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.sum_eq_single k]`. Rewrite using `[mul_smul_comm, (hS.1.idem k).eq]`. Introduce `j _ hj`. Rewrite using `[mul_smul_comm, hS.1.ortho (Ne.symm hj), smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem p_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    p k * (∑ j, d j • p j) = d k • p k := by
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [mul_smul_comm, (hS.1.idem k).eq]
  · intro j _ hj; rw [mul_smul_comm, hS.1.ortho (Ne.symm hj), smul_zero]
  · simp

/- English proof (translation)
Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, p_mul_sum hS, smul_smul]`.
-/
theorem sum_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d d' : Fin n → C) :
    (∑ j, d j • p j) * (∑ j, d' j • p j) = ∑ j, (d j * d' j) • p j := by
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, p_mul_sum hS, smul_smul]

/- English proof (translation)
Rewrite using `[sum_mul_sum hS, sum_mul_sum hS]`. Simplify using `only [mul_inv_cancel₀ (hd _), inv_mul_cancel₀ (hd _), one_smul, hS.1.complete, and_self]`.
-/
theorem sum_inv {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (hd : ∀ j, d j ≠ 0) :
    (∑ j, d j • p j) * (∑ j, (d j)⁻¹ • p j) = 1 ∧ (∑ j, (d j)⁻¹ • p j) * (∑ j, d j • p j) = 1 := by
  rw [sum_mul_sum hS, sum_mul_sum hS]
  simp only [mul_inv_cancel₀ (hd _), inv_mul_cancel₀ (hd _), one_smul, hS.1.complete, and_self]

/- English proof (translation)
The claim follows from `Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (hp j) _`.
-/
theorem sum_mem {p : Fin n → Mat C N} (A : Subalgebra C (Mat C N)) (hp : ∀ i, p i ∈ A) (d : Fin n → C) :
    (∑ j, d j • p j) ∈ A :=
  Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (hp j) _

/- English proof (translation)
Set `a : A` to `⟨v, hvA⟩`. Establish `hinj : Function.Injective A.val` using `Subtype.val_injective`. Establish `ha : a ∈ nonZeroDivisors A` using `comap_nonZeroDivisors_le_of_injective hinj hv.mem_nonZeroDivisors`. Use `haveI : Module.Finite C A := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule A)`. Establish `hu : IsUnit a` using `IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := C) ha`.

Take `⟨b, hb⟩` from `hu`. Use `⟨((b⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A).2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val b.mul_inv` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `this`.
-/
theorem inv_in (A : Subalgebra C (Mat C N)) {v : Mat C N} (hvA : v ∈ A) (hv : IsUnit v) :
    ∃ w ∈ A, v * w = 1 := by
  let a : A := ⟨v, hvA⟩
  have hinj : Function.Injective A.val := Subtype.val_injective
  have ha : a ∈ nonZeroDivisors A := comap_nonZeroDivisors_le_of_injective hinj hv.mem_nonZeroDivisors
  haveI : Module.Finite C A := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule A)
  have hu : IsUnit a := IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := C) ha
  obtain ⟨b, hb⟩ := hu
  refine ⟨((b⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A).2, ?_⟩
  have := congrArg Subtype.val b.mul_inv
  rw [hb] at this; exact this

/- English proof (translation)
Introduce `x hx _ hf` and use `hf x hx`.
-/
theorem zcl_sub (S : Set (Mat C N)) : S ⊆ Zcl S := fun x hx _ hf => hf x hx

/- English proof (translation)
Introduce `y hy f hf` and use `hy f fun x hx => hf x (h hx)`.
-/
theorem zcl_mono {S T : Set (Mat C N)} (h : S ⊆ T) : Zcl S ⊆ Zcl T :=
  fun y hy f hf => hy f fun x hx => hf x (h hx)

end LateralTheory.DivDb.KeyPf

namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb
variable {C : Type} [Field C] {N n : ℕ}

/- English proof (translation)
Establish `h2' : ∀ X, Ri * (R * X) = X` using `h2`. Use `⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i h => hS.2 i ?_⟩` and prove the remaining obligations. Use `show Ri * p i * R * (Ri * p i * R) = Ri * p i * R`. Simplify using `only [mul_assoc, h1]`. Rewrite using `[← mul_assoc (p i), (hS.1.idem i).eq]`.

Use `show Ri * p i * R * (Ri * p j * R) = 0`. Simplify using `only [mul_assoc, h1]`. Rewrite using `[← mul_assoc (p i), hS.1.ortho hij]`. Simplify using the standard rewrite rules. Rewrite using `[← Finset.sum_mul, ← Finset.mul_sum, hS.1.complete, mul_one]`.

Use `h2 1` as an intermediate fact. Simplify using `using this`. Use `congrArg (fun Y => R * Y * Ri) h` as an intermediate fact. Simplify using `only [mul_assoc, h1, mul_zero, zero_mul] at this`. Establish `e' : R * Ri = 1` using `by simpa using h1 1`.

Rewrite `this` using `[e', mul_one]`. Then use the resulting hypothesis.
-/
theorem sys_conj {p : Fin n → Mat C N} (hS : Sys p) (R Ri : Mat C N) (h1 : ∀ X, R * (Ri * X) = X)
    (h2 : ∀ X, Ri * (R * X) = X) : Sys (fun j => Ri * p j * R) := by
  have h2' : ∀ X, Ri * (R * X) = X := h2
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i h => hS.2 i ?_⟩
  · show Ri * p i * R * (Ri * p i * R) = Ri * p i * R
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), (hS.1.idem i).eq]
  · show Ri * p i * R * (Ri * p j * R) = 0
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), hS.1.ortho hij]; simp
  · rw [← Finset.sum_mul, ← Finset.mul_sum, hS.1.complete, mul_one]
    have := h2 1; simpa using this
  · have := congrArg (fun Y => R * Y * Ri) h
    simp only [mul_assoc, h1, mul_zero, zero_mul] at this
    have e' : R * Ri = 1 := by simpa using h1 1
    rwa [e', mul_one] at this

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, j, k, hjk, rfl⟩` from `hx`. Apply `hUn C N ρS _ (hT a ha j k hjk)` to reduce the goal to its premises.

Establish `: p k * p j = 0` using `hS.1.ortho (Ne.symm hjk)`. Combine the equalities or inequalities in the displayed calculation. Consider the case `one => exact zcl_sub _ ρS.one_mem`. Consider the case `mul x y _ _ hx hy => exact hZM C N ρS x hx y hy`.
-/
theorem tv_zcl {ρS : Submonoid (Mat C N)} (hZM : ZclMul) (hUn : Unip) [CharZero C]
    (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (hS : Sys p)
    (hT : ∀ a ∈ A, ∀ j k, j ≠ k → p j * a * p k ∈ Tan (ρS : Set (Mat C N))) :
    ∀ u ∈ Tv A p, u ∈ Zcl (ρS : Set (Mat C N)) := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, j, k, hjk, rfl⟩ := hx
    apply hUn C N ρS _ (hT a ha j k hjk)
    have : p k * p j = 0 := hS.1.ortho (Ne.symm hjk)
    calc p j * a * p k * (p j * a * p k) = p j * a * (p k * p j) * a * p k := by simp only [mul_assoc]
      _ = 0 := by rw [this]; simp
  | one => exact zcl_sub _ ρS.one_mem
  | mul x y _ _ hx hy => exact hZM C N ρS x hx y hy

/- English proof (translation)
Introduce `Γ C _ _ _ _ N n ρ e p hDeg hLac hG U hU hUf g`. Take `⟨hS, hX, hCo, hNN, hNo, _hKe, hOff⟩` from `hG`. Establish `hRiR : (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `hRRi : (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1`.

Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`. Use `set R : Mat C N := (ρ g : Mat C N) with hRdef`. Use `set Ri : Mat C N := (ρ g⁻¹ : Mat C N) with hRidef`. Establish `h1 : ∀ X, R * (Ri * X) = X` using `fun X => by rw [← mul_assoc, hRRi, one_mul]`. Establish `h2 : ∀ X, Ri * (R * X) = X` using `fun X => by rw [← mul_assoc, hRiR, one_mul]`.

Use `set A := env ρ`. Establish `hSq` using `sys_conj hS R Ri h1 h2`. Establish `hCq : Corner A (fun j => Ri * p j * R)`. Use `⟨fun i => ?_, fun a ha i => ?_⟩` and prove the remaining obligations. Use `hNo g⁻¹ (p i) (hCo.1 i)` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `hCo.2 _ (hNo g a ha) i`. Use `⟨c, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = c • (Ri * p i * R) := by rw [hc]; simp only [mul_smul_comm, smul_mul_assoc]`. Take `⟨v, hvA, hvU, π, hvπ, hπ⟩` from `hIC C N n A p _ hS hCo hSq hCq hNN`. Take `⟨E, hE⟩` from `hMU C N n A p hS hCo hNN`. Take `⟨u, huT, d, hd, hvud⟩` from `hUF C N n A p E hS hE v hvA hvU`. Take `⟨hDD', hD'D⟩` from `sum_inv hS d hd`.

Establish `hu : u = v * ∑ j, (d j)⁻¹ • p j` using `by rw [hvud, mul_assoc, hDD', mul_one]`. Establish `hup : ∀ j, u * p j = Ri * p (π j) * R * u`. Introduce `j`. Establish `e1 : u * p j = v * ((d j)⁻¹ • p j)` using `by rw [hu, mul_assoc, sum_mul_p hS]`. Establish `e2 : Ri * p (π j) * R * u = v * ((d j)⁻¹ • p j)`.

Rewrite using `[hu, ← mul_assoc, ← hvπ j, mul_assoc, p_mul_sum hS]`. Rewrite using `[e1, e2]`. Establish `hxp : ∀ j, R * u * p j = p (π j) * (R * u)`. Introduce `j`. Rewrite using `[mul_assoc, hup]`.

Simplify using `only [mul_assoc, h1]`. Establish `hD'U : IsUnit (∑ j, (d j)⁻¹ • p j)` using `⟨⟨_, _, hD'D, hDD'⟩, rfl⟩`. Establish `huU : IsUnit u` using `by rw [hu]; exact hvU.mul hD'U`. Establish `hxU : IsUnit (R * u)` using `(Units.isUnit (ρ g)).mul huU`. Take `⟨B, hBf, hB⟩` from `hGS C N n p (R * u) π hS hxU hxp`.

Establish `hXT` using `hTI Γ C N ρ U hU hUf hX`. Take `⟨τ, hτ, htZ, hτB⟩` from `hTP C N n (img ρ U) p e hS hLac hXT B hBf`. Establish `hdisj` using `hB τ hτ hτB`. Take `⟨hTT', hT'T⟩` from `sum_inv hS τ hτ`. Use `set t := ∑ j, τ j • p j with htdef`.

Establish `huZ : u ∈ Zcl (img ρ U : Set (Mat C N))` using `tv_zcl hZM hUn A p hS (fun a ha j k hjk => hTI Γ C N ρ U hU hUf (hOff a ha j k hjk)) u huT`. Establish `hmZ` using `hZM C N (img ρ U) u huZ t htZ`. Establish `htU : IsUnit t` using `⟨⟨_, _, hTT', hT'T⟩, rfl⟩`. Establish `hyU : IsUnit (R * u * t)` using `hxU.mul htU`. Establish `hyp : ∀ j, R * u * t * p j = p (π j) * (R * u * t)`.

Introduce `j`. Rewrite using `[mul_assoc, sum_mul_p hS, ← mul_assoc (p _), ← hxp, mul_assoc, mul_assoc, p_mul_sum hS]`. Simplify using `only [mul_assoc]`. Establish `himg : ∀ y ∈ img ρ U, y ∈ img ρ ⊤` using `fun y hy => by`. Take `⟨w, -, rfl⟩` from `Submonoid.mem_map.mp hy`.

Conclude with `Submonoid.mem_map.mpr ⟨w, by simp, rfl⟩`. Establish `hdegS : ∀ x ∈ img ρ ⊤, Deg n x` using `fun x hx => by`. Take `⟨w, -, rfl⟩` from `Submonoid.mem_map.mp hx`. Conclude with `hDeg w`. Establish `hRZ : R ∈ Zcl (img ρ ⊤ : Set (Mat C N))` using `zcl_sub _ (Submonoid.mem_map.mpr ⟨g, by simp, rfl⟩)`.

Establish `hyZ : R * u * t ∈ Zcl (img ρ ⊤ : Set (Mat C N))`. Rewrite using `[mul_assoc]`. Conclude with `hZM C N _ R hRZ _ (zcl_mono himg hmZ)`. Establish `hyDeg` using `(hTD C N n (img ρ ⊤) hdegS).1 _ hyZ`. Take `⟨hEig, hfix⟩` from `hCC C N n p (R * u * t) π hS hyU hyp hyDeg hdisj`.

Use `⟨⟨u * t, hmZ, by rw [← mul_assoc]; exact hEig⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `i ⟨a, haA, hne⟩`. Establish `ha' : Ri * a * R ∈ A` using `by have := hNo g⁻¹ a haA; rwa [inv_inv] at this`. Establish `hπi : π i = i`. Use `hπ i ⟨Ri * a * R, ha', fun h => hne ?_⟩` and prove the remaining obligations.

Use `congrArg (fun Y => R * Y) h` as an intermediate fact. Simplify using `only [mul_assoc, h1, mul_zero] at this`. Simplify `this` using `[mul_assoc]`. Take `⟨c, hc⟩` from `hfix i hπi`. Establish `hpy : p i * (R * u * t) = c • p i` using `by rw [← hc, hyp i, hπi]`.

Take `⟨vi, hviA, hvvi⟩` from `inv_in A hvA hvU`. Use `set D := ∑ j, d j • p j`. Use `set T' := ∑ j, (τ j)⁻¹ • p j`. Establish `hm1 : u * t * (T' * D * vi) = 1`. Establish `ht' : ∀ X, t * (T' * X) = X` using `fun X => by rw [← mul_assoc, hTT', one_mul]`.

Establish `hd' : ∀ X, (∑ j, (d j)⁻¹ • p j) * (D * X) = X` using `fun X => by rw [← mul_assoc, hD'D, one_mul]`. Rewrite using `[hu]`. Simplify using `only [mul_assoc, ht', hd', hvvi]`. Use `⟨c • (T' * D * vi), Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (sum_mem A hCo.1 _) (sum_mem A hCo.1 _)) hviA) _, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Key_of (hIC : IdemConj) (hMU : MatrixUnits₂) (hUF : UnitFactorization) (hTI : TanIndex) (hUn : Unip)
    (hZM : ZclMul) (hGS : GenSpec) (hTP : TorusPt) (hTD : TanDeg) (hCC : CycleCount) : Key := by
  intro Γ C _ _ _ _ N n ρ e p hDeg hLac hG U hU hUf g
  obtain ⟨hS, hX, hCo, hNN, hNo, _hKe, hOff⟩ := hG
  have hRiR : (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hRRi : (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  set R : Mat C N := (ρ g : Mat C N) with hRdef
  set Ri : Mat C N := (ρ g⁻¹ : Mat C N) with hRidef
  have h1 : ∀ X, R * (Ri * X) = X := fun X => by rw [← mul_assoc, hRRi, one_mul]
  have h2 : ∀ X, Ri * (R * X) = X := fun X => by rw [← mul_assoc, hRiR, one_mul]
  set A := env ρ
  have hSq := sys_conj hS R Ri h1 h2
  have hCq : Corner A (fun j => Ri * p j * R) := by
    refine ⟨fun i => ?_, fun a ha i => ?_⟩
    · have := hNo g⁻¹ (p i) (hCo.1 i); rwa [inv_inv] at this
    · obtain ⟨c, hc⟩ := hCo.2 _ (hNo g a ha) i
      refine ⟨c, ?_⟩
      calc Ri * p i * R * a * (Ri * p i * R) = Ri * (p i * (R * a * Ri) * p i) * R := by
            simp only [mul_assoc]
        _ = c • (Ri * p i * R) := by rw [hc]; simp only [mul_smul_comm, smul_mul_assoc]
  obtain ⟨v, hvA, hvU, π, hvπ, hπ⟩ := hIC C N n A p _ hS hCo hSq hCq hNN
  obtain ⟨E, hE⟩ := hMU C N n A p hS hCo hNN
  obtain ⟨u, huT, d, hd, hvud⟩ := hUF C N n A p E hS hE v hvA hvU
  obtain ⟨hDD', hD'D⟩ := sum_inv hS d hd
  have hu : u = v * ∑ j, (d j)⁻¹ • p j := by rw [hvud, mul_assoc, hDD', mul_one]
  have hup : ∀ j, u * p j = Ri * p (π j) * R * u := by
    intro j
    have e1 : u * p j = v * ((d j)⁻¹ • p j) := by rw [hu, mul_assoc, sum_mul_p hS]
    have e2 : Ri * p (π j) * R * u = v * ((d j)⁻¹ • p j) := by
      rw [hu, ← mul_assoc, ← hvπ j, mul_assoc, p_mul_sum hS]
    rw [e1, e2]
  have hxp : ∀ j, R * u * p j = p (π j) * (R * u) := by
    intro j; rw [mul_assoc, hup]; simp only [mul_assoc, h1]
  have hD'U : IsUnit (∑ j, (d j)⁻¹ • p j) := ⟨⟨_, _, hD'D, hDD'⟩, rfl⟩
  have huU : IsUnit u := by rw [hu]; exact hvU.mul hD'U
  have hxU : IsUnit (R * u) := (Units.isUnit (ρ g)).mul huU
  obtain ⟨B, hBf, hB⟩ := hGS C N n p (R * u) π hS hxU hxp
  have hXT := hTI Γ C N ρ U hU hUf hX
  obtain ⟨τ, hτ, htZ, hτB⟩ := hTP C N n (img ρ U) p e hS hLac hXT B hBf
  have hdisj := hB τ hτ hτB
  obtain ⟨hTT', hT'T⟩ := sum_inv hS τ hτ
  set t := ∑ j, τ j • p j with htdef
  have huZ : u ∈ Zcl (img ρ U : Set (Mat C N)) :=
    tv_zcl hZM hUn A p hS (fun a ha j k hjk => hTI Γ C N ρ U hU hUf (hOff a ha j k hjk)) u huT
  have hmZ := hZM C N (img ρ U) u huZ t htZ
  have htU : IsUnit t := ⟨⟨_, _, hTT', hT'T⟩, rfl⟩
  have hyU : IsUnit (R * u * t) := hxU.mul htU
  have hyp : ∀ j, R * u * t * p j = p (π j) * (R * u * t) := by
    intro j
    rw [mul_assoc, sum_mul_p hS, ← mul_assoc (p _), ← hxp, mul_assoc, mul_assoc, p_mul_sum hS]
    simp only [mul_assoc]
  have himg : ∀ y ∈ img ρ U, y ∈ img ρ ⊤ := fun y hy => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hy
    exact Submonoid.mem_map.mpr ⟨w, by simp, rfl⟩
  have hdegS : ∀ x ∈ img ρ ⊤, Deg n x := fun x hx => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hx
    exact hDeg w
  have hRZ : R ∈ Zcl (img ρ ⊤ : Set (Mat C N)) :=
    zcl_sub _ (Submonoid.mem_map.mpr ⟨g, by simp, rfl⟩)
  have hyZ : R * u * t ∈ Zcl (img ρ ⊤ : Set (Mat C N)) := by
    rw [mul_assoc]; exact hZM C N _ R hRZ _ (zcl_mono himg hmZ)
  have hyDeg := (hTD C N n (img ρ ⊤) hdegS).1 _ hyZ
  obtain ⟨hEig, hfix⟩ := hCC C N n p (R * u * t) π hS hyU hyp hyDeg hdisj
  refine ⟨⟨u * t, hmZ, by rw [← mul_assoc]; exact hEig⟩, ?_⟩
  rintro i ⟨a, haA, hne⟩
  have ha' : Ri * a * R ∈ A := by have := hNo g⁻¹ a haA; rwa [inv_inv] at this
  have hπi : π i = i := by
    refine hπ i ⟨Ri * a * R, ha', fun h => hne ?_⟩
    have := congrArg (fun Y => R * Y) h
    simp only [mul_assoc, h1, mul_zero] at this
    simpa [mul_assoc] using this
  obtain ⟨c, hc⟩ := hfix i hπi
  have hpy : p i * (R * u * t) = c • p i := by rw [← hc, hyp i, hπi]
  obtain ⟨vi, hviA, hvvi⟩ := inv_in A hvA hvU
  set D := ∑ j, d j • p j
  set T' := ∑ j, (τ j)⁻¹ • p j
  have hm1 : u * t * (T' * D * vi) = 1 := by
    have ht' : ∀ X, t * (T' * X) = X := fun X => by rw [← mul_assoc, hTT', one_mul]
    have hd' : ∀ X, (∑ j, (d j)⁻¹ • p j) * (D * X) = X := fun X => by rw [← mul_assoc, hD'D, one_mul]
    rw [hu]; simp only [mul_assoc, ht', hd', hvvi]
  refine ⟨c • (T' * D * vi), Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (sum_mem A hCo.1 _) (sum_mem A hCo.1 _)) hviA) _, ?_⟩
  calc p i * R = p i * R * (u * t * (T' * D * vi)) := by rw [hm1, mul_one]
    _ = p i * (R * u * t) * (T' * D * vi) := by simp only [mul_assoc]
    _ = p i * (c • (T' * D * vi)) := by rw [hpy, smul_mul_assoc, mul_smul_comm]

end LateralTheory.DivDb.KeyPf
