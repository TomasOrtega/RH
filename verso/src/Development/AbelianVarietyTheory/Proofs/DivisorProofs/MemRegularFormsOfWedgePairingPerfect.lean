import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebraStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section Wedge

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, v, hv, rfl⟩` from `hz`. Conclude with `Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩`. Consider the case `zero => rw [smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem omB_smul_mem (B : Subalgebra k K) (q : ℕ) {c : K} (hc : c ∈ B) {z : DR k K}
    (hz : z ∈ omB k K B q) : c • z ∈ omB k K B q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

def topCoefBasis {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) : DR k K →ₗ[K] K :=
  ExteriorAlgebra.liftAlternating (fun i => if h : i = n then h ▸ b.det else 0)

/- English proof (translation)
Simplify using `[topCoefBasis, ExteriorAlgebra.liftAlternating_apply_ιMulti]`.
-/
theorem topCoefBasis_ιMulti {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (v : Fin n → Ω[K⁄k]) :
    topCoefBasis b (ExteriorAlgebra.ιMulti K n v) = b.det v := by
  simp [topCoefBasis, ExteriorAlgebra.liftAlternating_apply_ιMulti]

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b0, hb0, v, hv, rfl⟩` from `hz`. Use `choose M hM using fun i j => hf ⟨v j, hv j⟩ i`. Establish `hmat : f • b.toMatrix (fun j => D k K (v j)) = (B.val : B →+* K).mapMatrix (Matrix.of M)`.

Use extensionality with `i j`. Simplify using `[Module.Basis.toMatrix_apply, ← hM]`. Establish `hdet` using `congrArg Matrix.det hmat`. Rewrite `hdet` using `[Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det]`. Use `⟨⟨b0, hb0⟩ * (Matrix.of M).det, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, topCoefBasis_ιMulti, Module.Basis.det_apply, smul_eq_mul, mul_left_comm, hdet]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨e1, h1⟩` from `hx`.

Take `⟨e2, h2⟩` from `hy`. Conclude with `⟨e1 + e2, by rw [map_add, mul_add, h1, h2]; simp⟩`. Consider the case `smul r x _ hx`. Take `⟨e, he⟩` from `hx`. Conclude with `⟨r • e, by rw [LinearMap.map_smul_of_tower, mul_smul_comm, he]; simp⟩`.
-/
theorem topCoefBasis_mem (B : Subalgebra k K) {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (f : K)
    (hf : ∀ (v : B) (j : Fin n), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    {z : DR k K} (hz : z ∈ omB k K B n) : ∃ e : B, f ^ n * topCoefBasis b z = e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b0, hb0, v, hv, rfl⟩ := hz
    choose M hM using fun i j => hf ⟨v j, hv j⟩ i
    have hmat : f • b.toMatrix (fun j => D k K (v j)) = (B.val : B →+* K).mapMatrix (Matrix.of M) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, ← hM]
    have hdet := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at hdet
    refine ⟨⟨b0, hb0⟩ * (Matrix.of M).det, ?_⟩
    rw [map_smul, topCoefBasis_ιMulti, Module.Basis.det_apply, smul_eq_mul, mul_left_comm, hdet]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e1, h1⟩ := hx
    obtain ⟨e2, h2⟩ := hy
    exact ⟨e1 + e2, by rw [map_add, mul_add, h1, h2]; simp⟩
  | smul r x _ hx =>
    obtain ⟨e, he⟩ := hx
    exact ⟨r • e, by rw [LinearMap.map_smul_of_tower, mul_smul_comm, he]; simp⟩

/- English proof (translation)
Use `conv_lhs => rw [← (b.exteriorPower q).sum_repr Y]`. Simplify using `[exteriorPower.coe_basis, exteriorPower.ιMulti_family]`.
-/
theorem eq_sum_exteriorPower_basis {n q : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (Y : ⋀[K]^q Ω[K⁄k]) :
    (Y : DR k K) = ∑ t, (b.exteriorPower q).repr Y t •
      ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t)) := by
  conv_lhs => rw [← (b.exteriorPower q).sum_repr Y]
  simp [exteriorPower.coe_basis, exteriorPower.ιMulti_family]

/- English proof (translation)
Establish `hcard : (s.val)ᶜ.card = p`. Rewrite using `[Finset.card_compl, Fintype.card_fin, s.prop]`. Use linear arithmetic over natural numbers and integers. Use `set g := Finset.orderEmbOfFin (s.val)ᶜ hcard with hg`. Use `set a : DR k K := ExteriorAlgebra.ιMulti K p (b ∘ g) with ha_def`.

Establish `ha : a ∈ omB k K B p` using `Submodule.subset_span ⟨1, B.one_mem, fun j => (u (g j) : K), fun j => (u (g j)).2, by simp [a, Function.comp_def, hb]⟩`. Take `⟨e, he⟩` from `topCoefBasis_mem B b f hf (hmul a ha)`. Establish `happ : ∀ h : Fin q → Fin (p + q), Fin.append (b ∘ g) (b ∘ h) = b ∘ Fin.append (fun i => g i) h`. Introduce `h`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp`. Establish `hterm : ∀ t, t ≠ s → topCoefBasis b (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t))) = 0`. Introduce `t hts`. Take `⟨i, hit, his⟩` from `(Set.powersetCard.exists_mem_notMem_iff_ne t s).mp hts`. Establish `hi1 : i ∈ Set.range g`.

Rewrite using `[hg, Finset.range_orderEmbOfFin]`. Simplify using `using his`. Establish `hi2 : i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm t)` using `(Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit`. Take `⟨a1, ha1⟩` from `hi1`. Take `⟨a2, ha2⟩` from `hi2`.

Rewrite using `[ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]`. Use `b.det.map_eq_zero_of_eq _ (i := Fin.castAdd q a1) (j := Fin.natAdd p a2) ?_ ?_` and prove the remaining obligations. Simplify using `[ha1, ha2]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `hdiag : ∃ ε : ℤˣ, topCoefBasis b (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))) = ((ε : ℤ) : K)` using `by set h := Fin.append (fun i => g i) (Set.powersetCard.ofFinEmbEquiv.symm s) with hh`. Establish `hinj : Function.Injective h`. Rewrite using `[hh, Fin.append_injective_iff]`.

Use `⟨g.injective, (Set.powersetCard.ofFinEmbEquiv.symm s).injective, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `h1 : g i ∈ (s.val)ᶜ`. Rewrite using `[← Finset.mem_coe, ← Finset.range_orderEmbOfFin (s.val)ᶜ hcard]`. Conclude with `⟨i, rfl⟩`. Establish `h2 : Set.powersetCard.ofFinEmbEquiv.symm s j ∈ s.val` using `(Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩`.

Rewrite `h1` using `[hij]`. Conclude with `(Finset.mem_compl.mp h1) h2`. Use `set σ := Equiv.ofBijective h (Finite.injective_iff_bijective.mp hinj)`. Use `⟨Equiv.Perm.sign σ, ?_⟩` and prove the remaining obligations. Rewrite using `[ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]`.

Establish `: b ∘ h = b ∘ σ` using `rfl`. Rewrite using `[this, b.det.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]`. Take `⟨ε, hε⟩` from `hdiag`. Establish `hsum : topCoefBasis b (a * (Y : DR k K)) = (b.exteriorPower q).repr Y s * ((ε : ℤ) : K)`. Rewrite using `[eq_sum_exteriorPower_basis b Y, Finset.mul_sum, map_sum, Finset.sum_eq_single s]`.

Rewrite using `[mul_smul_comm, map_smul, hε, smul_eq_mul]`. Introduce `t _ hts`. Rewrite using `[mul_smul_comm, map_smul, hterm t hts, smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`.

Use `⟨e * ((ε : ℤ) : B), ?_⟩` and prove the remaining obligations. Establish `hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`. Use `push_cast`. Rewrite using `[← he, hsum]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem wedge_coef_mem (B : Subalgebra k K) {p q : ℕ} (b : Module.Basis (Fin (p + q)) K Ω[K⁄k])
    (u : Fin (p + q) → B) (hb : ∀ j, b j = D k K (u j : K)) (f : K)
    (hf : ∀ (v : B) (j : Fin (p + q)), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    (Y : ⋀[K]^q Ω[K⁄k]) (hmul : ∀ a ∈ omB k K B p, a * (Y : DR k K) ∈ omB k K B (p + q))
    (s : Set.powersetCard (Fin (p + q)) q) :
    ∃ e : B, f ^ (p + q) * (b.exteriorPower q).repr Y s = e := by
  classical
  have hcard : (s.val)ᶜ.card = p := by
    rw [Finset.card_compl, Fintype.card_fin, s.prop]; omega
  set g := Finset.orderEmbOfFin (s.val)ᶜ hcard with hg
  set a : DR k K := ExteriorAlgebra.ιMulti K p (b ∘ g) with ha_def
  have ha : a ∈ omB k K B p :=
    Submodule.subset_span ⟨1, B.one_mem, fun j => (u (g j) : K), fun j => (u (g j)).2,
      by simp [a, Function.comp_def, hb]⟩
  obtain ⟨e, he⟩ := topCoefBasis_mem B b f hf (hmul a ha)
  have happ : ∀ h : Fin q → Fin (p + q),
      Fin.append (b ∘ g) (b ∘ h) = b ∘ Fin.append (fun i => g i) h := by
    intro h; funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hterm : ∀ t, t ≠ s → topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t))) = 0 := by
    intro t hts
    obtain ⟨i, hit, his⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp hts
    have hi1 : i ∈ Set.range g := by
      rw [hg, Finset.range_orderEmbOfFin]; simpa using his
    have hi2 : i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm t) :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
    obtain ⟨a1, ha1⟩ := hi1
    obtain ⟨a2, ha2⟩ := hi2
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    refine b.det.map_eq_zero_of_eq _ (i := Fin.castAdd q a1) (j := Fin.natAdd p a2) ?_ ?_
    · simp [ha1, ha2]
    · intro h; have := congrArg Fin.val h; simp at this; omega
  have hdiag : ∃ ε : ℤˣ, topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))) = ((ε : ℤ) : K) := by
    set h := Fin.append (fun i => g i) (Set.powersetCard.ofFinEmbEquiv.symm s) with hh
    have hinj : Function.Injective h := by
      rw [hh, Fin.append_injective_iff]
      refine ⟨g.injective, (Set.powersetCard.ofFinEmbEquiv.symm s).injective, fun i j hij => ?_⟩
      have h1 : g i ∈ (s.val)ᶜ := by
        rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (s.val)ᶜ hcard]; exact ⟨i, rfl⟩
      have h2 : Set.powersetCard.ofFinEmbEquiv.symm s j ∈ s.val :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩
      rw [hij] at h1
      exact (Finset.mem_compl.mp h1) h2
    set σ := Equiv.ofBijective h (Finite.injective_iff_bijective.mp hinj)
    refine ⟨Equiv.Perm.sign σ, ?_⟩
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    have : b ∘ h = b ∘ σ := rfl
    rw [this, b.det.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]
  obtain ⟨ε, hε⟩ := hdiag
  have hsum : topCoefBasis b (a * (Y : DR k K)) = (b.exteriorPower q).repr Y s * ((ε : ℤ) : K) := by
    rw [eq_sum_exteriorPower_basis b Y, Finset.mul_sum, map_sum, Finset.sum_eq_single s]
    · rw [mul_smul_comm, map_smul, hε, smul_eq_mul]
    · intro t _ hts; rw [mul_smul_comm, map_smul, hterm t hts, smul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  refine ⟨e * ((ε : ℤ) : B), ?_⟩
  have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  push_cast
  rw [← he, hsum]
  calc f ^ (p + q) * (b.exteriorPower q).repr Y s
      = f ^ (p + q) * (b.exteriorPower q).repr Y s * (((ε : ℤ) : K) * ((ε : ℤ) : K)) := by rw [hεε, mul_one]
    _ = _ := by ring

/- English proof (translation)
Introduce `k K _ _ _ B _ _ d p q hd hpq y hy hmul`. Substitute `hpq` using the available equality. Set `I : Ideal B` to `{ carrier := {c | (c : K) • y ∈ omB k K B q} add_mem' := fun {a c} ha hc => by`. Simplify using `only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *`. Conclude with `Submodule.add_mem _ ha hc`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun a c hc => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *`. Conclude with `omB_smul_mem B q a.2 hc }`. Establish `hI : I = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hIP⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨f, u, b, hfP, hb, hf⟩` from `GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B (p + q) hd P`. Apply `hfP` to reduce the goal to its premises. Use `hP.isPrime.mem_of_pow_mem (p + q) (hIP ?_)` and prove the remaining obligations.

Use `show ((f ^ (p + q) : B) : K) • y ∈ omB k K B q`. Establish `hy'` using `eq_sum_exteriorPower_basis b ⟨y, hy⟩`. Simplify using `only at hy'`. Rewrite using `[hy', Finset.smul_sum]`. Use `Submodule.sum_mem _ fun t _ => ?_` and prove the remaining obligations.

Take `⟨e, he⟩` from `wedge_coef_mem B b u hb (f : K) hf ⟨y, hy⟩ hmul t`. Rewrite using `[smul_smul, SubmonoidClass.coe_pow, he]`. Conclude with `Submodule.subset_span ⟨e, e.2, fun j => (u (Set.powersetCard.ofFinEmbEquiv.symm t j) : K), fun j => (u _).2, by simp [Function.comp_def, hb]⟩`. Establish `h1 : (1 : B) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify `h1` using `[I]`.
-/
theorem mem_omB_of_mul_mem_omB :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K]
      [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d →
      ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  intro k K _ _ _ B _ _ d p q hd hpq y hy hmul
  classical
  subst hpq
  let I : Ideal B :=
    { carrier := {c | (c : K) • y ∈ omB k K B q}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact Submodule.add_mem _ ha hc
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact omB_smul_mem B q a.2 hc }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨f, u, b, hfP, hb, hf⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B (p + q) hd P
    apply hfP
    refine hP.isPrime.mem_of_pow_mem (p + q) (hIP ?_)
    show ((f ^ (p + q) : B) : K) • y ∈ omB k K B q
    have hy' := eq_sum_exteriorPower_basis b ⟨y, hy⟩
    simp only at hy'
    rw [hy', Finset.smul_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨e, he⟩ := wedge_coef_mem B b u hb (f : K) hf ⟨y, hy⟩ hmul t
    rw [smul_smul, SubmonoidClass.coe_pow, he]
    exact Submodule.subset_span ⟨e, e.2, fun j => (u (Set.powersetCard.ofFinEmbEquiv.symm t j) : K),
      fun j => (u _).2,
      by simp [Function.comp_def, hb]⟩
  have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

/- English proof (translation)
The claim follows from `mem_omB_of_mul_mem_omB`.
-/
example : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K]
    [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d →
    ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q :=
  mem_omB_of_mul_mem_omB

end Wedge

end GlobalTheory.PD
