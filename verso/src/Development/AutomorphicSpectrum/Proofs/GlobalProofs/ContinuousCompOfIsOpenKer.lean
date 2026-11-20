import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply

noncomputable section

open ReciprocityTheory.Gal Representation

namespace GlobalTheory.CompanionTheory.Hypotheses₂.UnrOrth

section Geo

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def geo (f : Module.End R M) (m : M) (k : ℕ) : M := ∑ i ∈ Finset.range k, (f ^ i) m

/- English proof (translation)
Simplify using `[geo]`.
-/
@[simp] theorem geo_zero (f : Module.End R M) (m : M) : geo f m 0 = 0 := by simp [geo]

/- English proof (translation)
Simplify using `[geo, Finset.sum_range_succ]`.
-/
theorem geo_succ (f : Module.End R M) (m : M) (k : ℕ) :
    geo f m (k + 1) = geo f m k + (f ^ k) m := by
  simp [geo, Finset.sum_range_succ]

/- English proof (translation)
Simplify using `only [geo, Finset.sum_range_add, map_sum, pow_add, Module.End.mul_apply]`.
-/
theorem geo_add (f : Module.End R M) (m : M) (a b : ℕ) :
    geo f m (a + b) = geo f m a + (f ^ a) (geo f m b) := by
  simp only [geo, Finset.sum_range_add, map_sum, pow_add, Module.End.mul_apply]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Rewrite using `[add_mul, one_mul, geo_add, ih, pow_mul', hN, one_pow, Module.End.one_apply, add_smul, one_smul]`.
-/
theorem geo_mul (f : Module.End R M) (m : M) {N : ℕ} (hN : f ^ N = 1) (a : ℕ) :
    geo f m (a * N) = a • geo f m N := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [add_mul, one_mul, geo_add, ih, pow_mul', hN, one_pow, Module.End.one_apply, add_smul,
      one_smul]

/- English proof (translation)
Introduce `k` and use `by rw [geo_add, hS, map_zero, add_zero]`.
-/
theorem geo_periodic (f : Module.End R M) (m : M) {N : ℕ} (hS : geo f m N = 0) :
    Function.Periodic (geo f m) N := fun k => by
  rw [geo_add, hS, map_zero, add_zero]

end Geo

section Deg

variable {D : Type*} [Group D] {N : ℕ}

def deg (d : D →* Multiplicative (ZMod N)) (g : D) : ℕ := (Multiplicative.toAdd (d g)).val

/- English proof (translation)
Simplify using `only [deg, map_mul, toAdd_mul, ZMod.val_add]`.
-/
theorem deg_mul [NeZero N] (d : D →* Multiplicative (ZMod N)) (g h : D) :
    deg d (g * h) = (deg d g + deg d h) % N := by
  simp only [deg, map_mul, toAdd_mul, ZMod.val_add]

/- English proof (translation)
Simplify using `[deg, h]`.
-/
theorem deg_of_eq_one (d : D →* Multiplicative (ZMod N)) {g : D} (h : d g = 1) : deg d g = 0 := by
  simp [deg, h]

/- English proof (translation)
Use `IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)` and prove the remaining obligations. Use `⟨(fun x => g⁻¹ * x) ⁻¹' (d.ker : Set D), hd.preimage (continuous_mul_left _), ?_, ?_⟩` and prove the remaining obligations. Simplify using `[MonoidHom.mem_ker]`. Introduce `x hx`. Establish `hx' : d (g⁻¹ * x) = 1` using `hx`.

Rewrite `hx'` using `[map_mul, map_inv, inv_mul_eq_one]`. Simplify using `[hx']`.
-/
theorem continuous_comp_of_isOpen_ker [TopologicalSpace D] [IsTopologicalGroup D]
    {X : Type*} [TopologicalSpace X]
    (d : D →* Multiplicative (ZMod N)) (hd : IsOpen (d.ker : Set D))
    (F : Multiplicative (ZMod N) → X) : Continuous fun g => F (d g) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (d.ker : Set D), hd.preimage (continuous_mul_left _), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro x hx
    have hx' : d (g⁻¹ * x) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at hx'
    simp [hx']

end Deg

section Cocycles

variable {R : Type*} [CommRing R] {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {I : Subgroup D} {φ : D}

/- English proof (translation)
Rewrite using `[eq_top_iff, ← hgen]`. Conclude with `Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 h1) h2) hc`.
-/
theorem eq_top_of_gen (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) (S : Subgroup D)
    (hc : IsClosed (S : Set D)) (h1 : φ ∈ S) (h2 : I ≤ S) : S = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 h1) h2) hc

variable {rho : Representation R D M}

/- English proof (translation)
Establish `hone : w 1 = 0`. Use `hw.2 1 1` as an intermediate fact. Simplify using `using this`. Set `S : Subgroup D` to `{ carrier := {g | w g = 0} mul_mem' := fun {a b} ha hb => by`. Establish `ha' : w a = 0` using `ha`.

Establish `hb' : w b = 0` using `hb`. Use `show w (a * b) = 0`. Rewrite using `[hw.2, ha', hb', map_zero, add_zero]`. Use the proof step `one_mem' := hone`. Use the proof step `inv_mem' := fun {a} ha => by`.

Establish `ha' : w a = 0` using `ha`. Use `hw.2 a⁻¹ a` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, hone, ha', map_zero, add_zero]`. Conclude with `this.symm }`. Establish `hS : S = ⊤` using `eq_top_of_gen hgen S ((isClosed_discrete ({0} : Set M)).preimage hw.1) h1 h2`.

Establish `: g ∈ S` using `hS ▸ Subgroup.mem_top g`. Conclude with `this`.
-/
theorem cocycle_eq_zero (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) {w : D → M}
    (hw : w ∈ Z1 rho) (h1 : w φ = 0) (h2 : ∀ σ ∈ I, w σ = 0) (g : D) : w g = 0 := by
  have hone : w 1 = 0 := by
    have := hw.2 1 1
    simpa using this
  let S : Subgroup D :=
    { carrier := {g | w g = 0}
      mul_mem' := fun {a b} ha hb => by
        have ha' : w a = 0 := ha
        have hb' : w b = 0 := hb
        show w (a * b) = 0
        rw [hw.2, ha', hb', map_zero, add_zero]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        have ha' : w a = 0 := ha
        have := hw.2 a⁻¹ a
        rw [inv_mul_cancel, hone, ha', map_zero, add_zero] at this
        exact this.symm }
  have hS : S = ⊤ := eq_top_of_gen hgen S
    ((isClosed_discrete ({0} : Set M)).preimage hw.1) h1 h2
  have : g ∈ S := hS ▸ Subgroup.mem_top g
  exact this

/- English proof (translation)
Establish `hm : ∀ a b, rho φ ^ deg d (a * b) = rho φ ^ deg d a * rho φ ^ deg d b` using `fun a b => by`. Rewrite using `[deg_mul, ← pow_add, ← pow_eq_pow_mod _ hN]`. Establish `h1 : deg d (1 : D) = 0` using `deg_of_eq_one d (map_one d)`. Set `S : Subgroup D` to `{ carrier := {g | rho g = rho φ ^ deg d g} mul_mem' := fun {a b} ha hb => by`. Establish `ha' : rho a = _` using `ha`.

Establish `hb' : rho b = _` using `hb`. Use `show rho (a * b) = _`. Rewrite using `[map_mul, ha', hb', hm]`. Use the proof step `one_mem' := by show rho 1 = _`. Rewrite using `[h1, map_one, pow_zero]`.

Use the proof step `inv_mem' := fun {a} ha => by`. Establish `ha' : rho a = _` using `ha`. Use `show rho a⁻¹ = _`. Establish `e : rho φ ^ deg d a * rho φ ^ deg d a⁻¹ = 1`. Rewrite using `[← hm, mul_inv_cancel, h1, pow_zero]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcl : IsClosed (S : Set D)`. Establish `: (S : Set D) = ⋂ m : M, {g | rho g m = (rho φ ^ deg d g) m}`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`.

Conclude with `⟨fun h m => by rw [show rho g = _ from h], fun h => LinearMap.ext h⟩`. Rewrite using `[this]`. Use `isClosed_iInter fun m => isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) ?_` and prove the remaining obligations. Conclude with `continuous_comp_of_isOpen_ker d hd (fun z => (rho φ ^ (Multiplicative.toAdd z).val) m)`. Establish `h2 : φ ∈ S` using `by show rho φ = rho φ ^ deg d φ`.

Establish `: deg d φ = 1 % N` using `by simp [deg, hdφ, ZMod.val_one_eq_one_mod]`. Rewrite using `[this, ← pow_eq_pow_mod _ hN, pow_one]`. Establish `h3 : I ≤ S` using `fun σ hσ => by show rho σ = _`. Rewrite using `[deg_of_eq_one d (hdI σ hσ), hI σ hσ, pow_zero]`. Establish `hS : S = ⊤` using `eq_top_of_gen hgen S hcl h2 h3`.

Establish `: g ∈ S` using `hS ▸ Subgroup.mem_top g`. Conclude with `this`.
-/
theorem rho_eq_pow (hc : ContAction rho) (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hI : ∀ σ ∈ I, rho σ = 1) {N : ℕ} [NeZero N] (d : D →* Multiplicative (ZMod N))
    (hd : IsOpen (d.ker : Set D)) (hdI : ∀ σ ∈ I, d σ = 1)
    (hdφ : d φ = Multiplicative.ofAdd 1) (hN : rho φ ^ N = 1) (g : D) :
    rho g = rho φ ^ deg d g := by
  have hm : ∀ a b, rho φ ^ deg d (a * b) = rho φ ^ deg d a * rho φ ^ deg d b := fun a b => by
    rw [deg_mul, ← pow_add, ← pow_eq_pow_mod _ hN]
  have h1 : deg d (1 : D) = 0 := deg_of_eq_one d (map_one d)
  let S : Subgroup D :=
    { carrier := {g | rho g = rho φ ^ deg d g}
      mul_mem' := fun {a b} ha hb => by
        have ha' : rho a = _ := ha
        have hb' : rho b = _ := hb
        show rho (a * b) = _
        rw [map_mul, ha', hb', hm]
      one_mem' := by
        show rho 1 = _
        rw [h1, map_one, pow_zero]
      inv_mem' := fun {a} ha => by
        have ha' : rho a = _ := ha
        show rho a⁻¹ = _
        have e : rho φ ^ deg d a * rho φ ^ deg d a⁻¹ = 1 := by
          rw [← hm, mul_inv_cancel, h1, pow_zero]
        calc rho a⁻¹ = rho a⁻¹ * (rho φ ^ deg d a * rho φ ^ deg d a⁻¹) := by rw [e, mul_one]
          _ = (rho a⁻¹ * rho a) * rho φ ^ deg d a⁻¹ := by rw [ha', mul_assoc]
          _ = rho φ ^ deg d a⁻¹ := by rw [← map_mul, inv_mul_cancel, map_one, one_mul] }
  have hcl : IsClosed (S : Set D) := by
    have : (S : Set D) = ⋂ m : M, {g | rho g m = (rho φ ^ deg d g) m} := by
      ext g
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact ⟨fun h m => by rw [show rho g = _ from h], fun h => LinearMap.ext h⟩
    rw [this]
    refine isClosed_iInter fun m => isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) ?_
    exact continuous_comp_of_isOpen_ker d hd
      (fun z => (rho φ ^ (Multiplicative.toAdd z).val) m)
  have h2 : φ ∈ S := by
    show rho φ = rho φ ^ deg d φ
    have : deg d φ = 1 % N := by simp [deg, hdφ, ZMod.val_one_eq_one_mod]
    rw [this, ← pow_eq_pow_mod _ hN, pow_one]
  have h3 : I ≤ S := fun σ hσ => by
    show rho σ = _
    rw [deg_of_eq_one d (hdI σ hσ), hI σ hσ, pow_zero]
  have hS : S = ⊤ := eq_top_of_gen hgen S hcl h2 h3
  have : g ∈ S := hS ▸ Subgroup.mem_top g
  exact this

/- English proof (translation)
Use `⟨continuous_comp_of_isOpen_ker d hd (fun z => geo (rho φ) m (Multiplicative.toAdd z).val), fun g h => ?_⟩` and prove the remaining obligations. Use `show geo (rho φ) m (deg d (g * h)) = geo (rho φ) m (deg d g) + rho g (geo (rho φ) m (deg d h))`. Rewrite using `[deg_mul, (geo_periodic _ _ hS).map_mod_nat, geo_add, rho_eq_pow hc hgen hI d hd hdI hdφ hN g]`.
-/
theorem geometric_sum_mem_cocycles (hc : ContAction rho) (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hI : ∀ σ ∈ I, rho σ = 1) {N : ℕ} [NeZero N] (d : D →* Multiplicative (ZMod N))
    (hd : IsOpen (d.ker : Set D)) (hdI : ∀ σ ∈ I, d σ = 1)
    (hdφ : d φ = Multiplicative.ofAdd 1) (hN : rho φ ^ N = 1) (m : M)
    (hS : geo (rho φ) m N = 0) : (fun g => geo (rho φ) m (deg d g)) ∈ Z1 rho := by
  refine ⟨continuous_comp_of_isOpen_ker d hd (fun z => geo (rho φ) m (Multiplicative.toAdd z).val),
    fun g h => ?_⟩
  show geo (rho φ) m (deg d (g * h)) = geo (rho φ) m (deg d g) + rho g (geo (rho φ) m (deg d h))
  rw [deg_mul, (geo_periodic _ _ hS).map_mod_nat, geo_add,
    rho_eq_pow hc hgen hI d hd hdI hdφ hN g]

/- English proof (translation)
Establish `: deg d φ = 1 % N` using `by simp [deg, hdφ, ZMod.val_one_eq_one_mod]`. Rewrite using `[this, (geo_periodic _ _ hS).map_mod_nat]`. Simplify using `[geo]`.
-/
theorem geo_deg_gen {N : ℕ} (d : D →* Multiplicative (ZMod N))
    (hdφ : d φ = Multiplicative.ofAdd 1) (f : Module.End R M) (m : M)
    (hS : geo f m N = 0) : geo f m (deg d φ) = m := by
  have : deg d φ = 1 % N := by simp [deg, hdφ, ZMod.val_one_eq_one_mod]
  rw [this, (geo_periodic _ _ hS).map_mod_nat]
  simp [geo]

/- English proof (translation)
Establish `hg` using `geometric_sum_mem_cocycles hc hgen hI d hd hdI hdφ hN (z φ) hS`. Use `cocycle_eq_zero (φ := φ) (I := I) hgen ((Z1 rho).sub_mem hz hg) ?_ ?_ g` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Simplify using `[geo_deg_gen d hdφ _ _ hS]`. Introduce `σ hσ`.

Simplify using `[hzI σ hσ, deg_of_eq_one d (hdI σ hσ)]`.
-/
theorem eq_geo (hc : ContAction rho) (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hI : ∀ σ ∈ I, rho σ = 1) {N : ℕ} [NeZero N] (d : D →* Multiplicative (ZMod N))
    (hd : IsOpen (d.ker : Set D)) (hdI : ∀ σ ∈ I, d σ = 1)
    (hdφ : d φ = Multiplicative.ofAdd 1) (hN : rho φ ^ N = 1) {z : D → M} (hz : z ∈ Z1 rho)
    (hzI : ∀ σ ∈ I, z σ = 0) (hS : geo (rho φ) (z φ) N = 0) (g : D) :
    z g = geo (rho φ) (z φ) (deg d g) := by
  have hg := geometric_sum_mem_cocycles hc hgen hI d hd hdI hdφ hN (z φ) hS
  have := cocycle_eq_zero (φ := φ) (I := I) hgen ((Z1 rho).sub_mem hz hg) ?_ ?_ g
  · exact sub_eq_zero.1 this
  · simp [geo_deg_gen d hdφ _ _ hS]
  · intro σ hσ
    simp [hzI σ hσ, deg_of_eq_one d (hdI σ hσ)]

/- English proof (translation)
Establish `: Finite (Module.End R M)` using `DFunLike.finite _`. Establish `h` using `isOfFinOrder_of_finite (rho.asGroupHom φ)`. Use `⟨orderOf (rho.asGroupHom φ), h.orderOf_pos, ?_⟩` and prove the remaining obligations. Use `congrArg Units.val (pow_orderOf_eq_one (rho.asGroupHom φ))` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val, Units.val_one, Representation.asGroupHom_apply]`. Then use the resulting hypothesis.
-/
theorem exists_pow_eq_one [Finite M] (rho : Representation R D M) (φ : D) :
    ∃ N : ℕ, 0 < N ∧ rho φ ^ N = 1 := by
  have : Finite (Module.End R M) := DFunLike.finite _
  have h := isOfFinOrder_of_finite (rho.asGroupHom φ)
  refine ⟨orderOf (rho.asGroupHom φ), h.orderOf_pos, ?_⟩
  have := congrArg Units.val (pow_orderOf_eq_one (rho.asGroupHom φ))
  rwa [Units.val_pow_eq_pow_val, Units.val_one, Representation.asGroupHom_apply] at this

/- English proof (translation)
Rewrite using `[geo_mul f m hN, hn]`.
-/
theorem geo_eq_zero (f : Module.End R M) {n N : ℕ} (hn : ∀ m : M, n • m = 0) (hN : f ^ N = 1)
    (m : M) : geo f m (n * N) = 0 := by
  rw [geo_mul f m hN, hn]

end Cocycles

section Count

variable {R : Type*} [CommRing R] {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {I : Subgroup D} {φ : D} {rho : Representation R D M}

/- English proof (translation)
Establish `e : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho I ↔ (restrictCocycles1 rho I.subtype continuous_subtype_val z).1 ∈ B1 (rho.comp I.subtype)`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (restrictCocycles1 rho I.subtype continuous_subtype_val z) : H1 (rho.comp I.subtype)) = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression. Rewrite using `[e, mem_coboundaries1]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩ σ hσ`. Establish `h2 : z.1 σ = rho σ m - m` using `hm ⟨σ, hσ⟩`. Simplify `h2` using `[hI σ hσ]`. Introduce `h`.

Use `⟨0, fun σ => ?_⟩` and prove the remaining obligations. Establish `h2` using `h σ.1 σ.2`. Use `show z.1 σ.1 = (rho.comp I.subtype) σ 0 - 0`. Simplify using `[h2]`.
-/
theorem mk_mem_H1ur (hI : ∀ σ ∈ I, rho σ = 1) (z : Z1 rho) :
    (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho I ↔ ∀ σ ∈ I, z.1 σ = 0 := by
  have e : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho I ↔
      (restrictCocycles1 rho I.subtype continuous_subtype_val z).1 ∈ B1 (rho.comp I.subtype) := by
    change (Submodule.Quotient.mk (restrictCocycles1 rho I.subtype continuous_subtype_val z) :
      H1 (rho.comp I.subtype)) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  rw [e, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    have h2 : z.1 σ = rho σ m - m := hm ⟨σ, hσ⟩
    simpa [hI σ hσ] using h2
  · intro h
    refine ⟨0, fun σ => ?_⟩
    have h2 := h σ.1 σ.2
    show z.1 σ.1 = (rho.comp I.subtype) σ 0 - 0
    simp [h2]

def evalH (rho : Representation R D M) (φ : D) :
    H1 rho →ₗ[R] M ⧸ LinearMap.range (rho φ - 1) :=
  Submodule.mapQ _ _ ((LinearMap.proj φ).comp (Z1 rho).subtype) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    exact ⟨m, by simpa using (hm φ).symm⟩

/- English proof (translation)
Establish `e1` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)`. Establish `e2` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)`. Rewrite `e2` using `[Nat.card_congr u.quotKerEquivRange.toEquiv]`. Establish `hpos : 0 < Nat.card (LinearMap.range u)` using `Nat.card_pos`. Rewrite `e2` using `[e1, mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_right hpos e2`.
-/
theorem card_quot_range_eq_card_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite M] (u : M →ₗ[R] M) :
    Nat.card (M ⧸ LinearMap.range u) = Nat.card (LinearMap.ker u) := by
  have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)
  have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)
  rw [Nat.card_congr u.quotKerEquivRange.toEquiv] at e2
  have hpos : 0 < Nat.card (LinearMap.range u) := Nat.card_pos
  rw [e1, mul_comm] at e2
  exact Nat.eq_of_mul_eq_mul_right hpos e2

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[mem_riemannRochSpace_iff_regularAt_everywhere, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `[h φ]`.

Introduce `h g`. Establish `hφ : rho φ m = m` using `by simpa [sub_eq_zero] using h`. Establish `hfix : ∀ a, rho a m = m → rho a⁻¹ m = m` using `fun a ha => by conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Set `S : Subgroup D` to `{ carrier := {g | rho g m = m} mul_mem' := fun {a b} ha hb => by`.

Establish `ha' : rho a m = m` using `ha`. Establish `hb' : rho b m = m` using `hb`. Use `show rho (a * b) m = m`. Rewrite using `[map_mul, Module.End.mul_apply, hb', ha']`. Use the proof step `one_mem' := by show rho 1 m = m`.

Simplify using the standard rewrite rules. Use the proof step `inv_mem' := fun {a} ha => hfix a ha }`. Establish `hcl : IsClosed (S : Set D)` using `isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const`. Establish `hS : S = ⊤` using `eq_top_of_gen hgen S hcl hφ fun σ hσ => by show rho σ m = m`. Simplify using `[hI σ hσ]`.

Establish `: g ∈ S` using `hS ▸ Subgroup.mem_top g`. Conclude with `this`.
-/
theorem H0_eq_ker_frobenius_sub_one (hc : ContAction rho) (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hI : ∀ σ ∈ I, rho σ = 1) : H0 rho = LinearMap.ker (rho φ - 1) := by
  ext m
  rw [mem_riemannRochSpace_iff_regularAt_everywhere, LinearMap.mem_ker]
  constructor
  · intro h
    simp [h φ]
  · intro h g
    have hφ : rho φ m = m := by simpa [sub_eq_zero] using h
    have hfix : ∀ a, rho a m = m → rho a⁻¹ m = m := fun a ha => by
      conv_lhs => rw [← ha]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    let S : Subgroup D :=
      { carrier := {g | rho g m = m}
        mul_mem' := fun {a b} ha hb => by
          have ha' : rho a m = m := ha
          have hb' : rho b m = m := hb
          show rho (a * b) m = m
          rw [map_mul, Module.End.mul_apply, hb', ha']
        one_mem' := by
          show rho 1 m = m
          simp
        inv_mem' := fun {a} ha => hfix a ha }
    have hcl : IsClosed (S : Set D) :=
      isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
    have hS : S = ⊤ := eq_top_of_gen hgen S hcl hφ fun σ hσ => by
      show rho σ m = m
      simp [hI σ hσ]
    have : g ∈ S := hS ▸ Subgroup.mem_top g
    exact this

/- English proof (translation)
Take `⟨N₁, hN₁, hf⟩` from `exists_pow_eq_one rho φ`. Establish `hNpos : 0 < n * N₁` using `Nat.mul_pos hn0 hN₁`. Take `⟨d, hd, hdI, hdφ⟩` from `hdeg (n * N₁) hNpos`. Use `haveI : NeZero (n * N₁) := ⟨hNpos.ne'⟩`. Establish `hfN : rho φ ^ (n * N₁) = 1` using `by rw [mul_comm, pow_mul, hf, one_pow]`.

Establish `hS : ∀ m, geo (rho φ) m (n * N₁) = 0` using `geo_eq_zero _ hn hf`. Rewrite using `[H0_eq_ker_frobenius_sub_one hc hgen hI, ← card_quot_range_eq_card_ker]`. Use `Nat.card_eq_of_bijective (((evalH rho φ).domRestrict (H1ur rho I))) ⟨?_, ?_⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩ h0`.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hzI` using `(mk_mem_H1ur hI z).1 hx`. Establish `h1 : z.1 φ ∈ LinearMap.range (rho φ - 1)` using `(Submodule.Quotient.mk_eq_zero _).1 h0`. Take `⟨m, hm⟩` from `h1`. Establish `hb : d0 rho m ∈ Z1 rho`.

Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Conclude with `(hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const`. Simplify using `only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Establish `hw` using `cocycle_eq_zero (φ := φ) (I := I) hgen ((Z1 rho).sub_mem z.2 hb) ?_ ?_`.

Use `Subtype.ext ?_ show (Submodule.Quotient.mk z : H1 rho) = 0` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `(mem_coboundaries1 rho _).2 ⟨m, fun g => ?_⟩` and prove the remaining obligations. Conclude with `sub_eq_zero.1 (hw g)`. Simplify using `[← hm]`.

Introduce `σ hσ`. Simplify using `[hzI σ hσ, hI σ hσ]`. Introduce `y`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Establish `hz` using `geometric_sum_mem_cocycles hc hgen hI d hd hdI hdφ hfN m (hS m)`.

Use `⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, (mk_mem_H1ur hI _).2 fun σ hσ => ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `[deg_of_eq_one d (hdI σ hσ)]`. Use `show Submodule.Quotient.mk (geo (rho φ) m (deg d φ)) = _`. Rewrite using `[geo_deg_gen d hdφ _ _ (hS m)]`.
-/
theorem card_H1ur [Finite M] {n : ℕ} (hn0 : 0 < n) (hn : ∀ m : M, n • m = 0)
    (hc : ContAction rho) (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hdeg : ∀ N : ℕ, 0 < N → ∃ d : D →* Multiplicative (ZMod N), IsOpen (d.ker : Set D) ∧
      (∀ σ ∈ I, d σ = 1) ∧ d φ = Multiplicative.ofAdd 1)
    (hI : ∀ σ ∈ I, rho σ = 1) : Nat.card (H1ur rho I) = Nat.card (H0 rho) := by
  obtain ⟨N₁, hN₁, hf⟩ := exists_pow_eq_one rho φ
  have hNpos : 0 < n * N₁ := Nat.mul_pos hn0 hN₁
  obtain ⟨d, hd, hdI, hdφ⟩ := hdeg (n * N₁) hNpos
  haveI : NeZero (n * N₁) := ⟨hNpos.ne'⟩
  have hfN : rho φ ^ (n * N₁) = 1 := by rw [mul_comm, pow_mul, hf, one_pow]
  have hS : ∀ m, geo (rho φ) m (n * N₁) = 0 := geo_eq_zero _ hn hf
  rw [H0_eq_ker_frobenius_sub_one hc hgen hI, ← card_quot_range_eq_card_ker]
  refine Nat.card_eq_of_bijective (((evalH rho φ).domRestrict (H1ur rho I))) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨x, hx⟩ h0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hzI := (mk_mem_H1ur hI z).1 hx
    have h1 : z.1 φ ∈ LinearMap.range (rho φ - 1) :=
      (Submodule.Quotient.mk_eq_zero _).1 h0
    obtain ⟨m, hm⟩ := h1
    have hb : d0 rho m ∈ Z1 rho := by
      refine ⟨?_, fun g h => ?_⟩
      · exact (hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const
      · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
        abel
    have hw := cocycle_eq_zero (φ := φ) (I := I) hgen ((Z1 rho).sub_mem z.2 hb) ?_ ?_
    · refine Subtype.ext ?_
      show (Submodule.Quotient.mk z : H1 rho) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 rho _).2 ⟨m, fun g => ?_⟩
      exact sub_eq_zero.1 (hw g)
    · simp [← hm]
    · intro σ hσ
      simp [hzI σ hσ, hI σ hσ]
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hz := geometric_sum_mem_cocycles hc hgen hI d hd hdI hdφ hfN m (hS m)
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, (mk_mem_H1ur hI _).2 fun σ hσ => ?_⟩, ?_⟩
    · simp [deg_of_eq_one d (hdI σ hσ)]
    · show Submodule.Quotient.mk (geo (rho φ) m (deg d φ)) = _
      rw [geo_deg_gen d hdφ _ _ (hS m)]

end Count

section Cup

variable {R : Type*} [CommRing R] {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  {M₁ M₂ P : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup P] [Module R P]

/- English proof (translation)
Rewrite using `[mul_comm, pow_mul, h, one_pow]`.
-/
theorem pow_mul_eq_one' {X : Type*} [Monoid X] {f : X} (a : ℕ) {b : ℕ} (h : f ^ b = 1) :
    f ^ (a * b) = 1 := by
  rw [mul_comm, pow_mul, h, one_pow]

def tri (f₁ : Module.End R M₁) (f₂ : Module.End R M₂) (b : M₁ →ₗ[R] M₂ →ₗ[R] P) (m₁ : M₁) (m₂ : M₂)
    (k : ℕ) : P := ∑ t ∈ Finset.range k, b (geo f₁ m₁ t) ((f₂ ^ t) m₂)

/- English proof (translation)
Proceed by induction on `a generalizing x y with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Simplify using `only [pow_succ, Module.End.mul_apply]`. Rewrite using `[ih, hb]`.
-/
theorem b_pow (f₁ : Module.End R M₁) (f₂ : Module.End R M₂) (fP : Module.End R P)
    (b : M₁ →ₗ[R] M₂ →ₗ[R] P) (hb : ∀ x y, b (f₁ x) (f₂ y) = fP (b x y)) (a : ℕ) (x : M₁) (y : M₂) :
    b ((f₁ ^ a) x) ((f₂ ^ a) y) = (fP ^ a) (b x y) := by
  induction a generalizing x y with
  | zero => simp
  | succ a ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hb]

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => simp [tri]`. Consider the case `succ c ih`. Establish `e1 : tri f₁ f₂ b m₁ m₂ (a + (c + 1)) = tri f₁ f₂ b m₁ m₂ (a + c) + b (geo f₁ m₁ (a + c)) ((f₂ ^ (a + c)) m₂)`. Simplify using `[tri, ← add_assoc, Finset.sum_range_succ]`.

Establish `e2 : tri f₁ f₂ b m₁ m₂ (c + 1) = tri f₁ f₂ b m₁ m₂ c + b (geo f₁ m₁ c) ((f₂ ^ c) m₂)`. Simplify using `[tri, Finset.sum_range_succ]`. Rewrite using `[e1, ih, e2, geo_add, geo_succ, pow_add, Module.End.mul_apply]`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[b_pow f₁ f₂ fP b hb]`.

Normalize the expressions using the abelian group laws.
-/
theorem tri_add (f₁ : Module.End R M₁) (f₂ : Module.End R M₂) (fP : Module.End R P)
    (b : M₁ →ₗ[R] M₂ →ₗ[R] P) (hb : ∀ x y, b (f₁ x) (f₂ y) = fP (b x y)) (m₁ : M₁) (m₂ : M₂)
    (a c : ℕ) :
    tri f₁ f₂ b m₁ m₂ (a + c) = tri f₁ f₂ b m₁ m₂ a + (fP ^ a) (tri f₁ f₂ b m₁ m₂ c) +
      b (geo f₁ m₁ a) ((f₂ ^ a) (geo f₂ m₂ c)) := by
  induction c with
  | zero => simp [tri]
  | succ c ih =>
    have e1 : tri f₁ f₂ b m₁ m₂ (a + (c + 1)) = tri f₁ f₂ b m₁ m₂ (a + c) +
        b (geo f₁ m₁ (a + c)) ((f₂ ^ (a + c)) m₂) := by
      simp [tri, ← add_assoc, Finset.sum_range_succ]
    have e2 : tri f₁ f₂ b m₁ m₂ (c + 1) = tri f₁ f₂ b m₁ m₂ c +
        b (geo f₁ m₁ c) ((f₂ ^ c) m₂) := by
      simp [tri, Finset.sum_range_succ]
    rw [e1, ih, e2, geo_add, geo_succ, pow_add, Module.End.mul_apply]
    simp only [map_add, LinearMap.add_apply]
    rw [b_pow f₁ f₂ fP b hb]
    abel

variable [TopologicalSpace M₁] [DiscreteTopology M₁] [TopologicalSpace M₂] [DiscreteTopology M₂]
  [TopologicalSpace P] [DiscreteTopology P] [Finite M₁] [Finite M₂] [Finite P]
  {I : Subgroup D} {φ : D}

/- English proof (translation)
Take `⟨A₁, hA₁, e₁⟩` from `exists_pow_eq_one rho₁ φ`. Take `⟨A₂, hA₂, e₂⟩` from `exists_pow_eq_one rho₂ φ`. Take `⟨A₃, hA₃, e₃⟩` from `exists_pow_eq_one rhoP φ`. Use `set N₁ := A₁ * A₂ * A₃ with hN₁`. Establish `hN₁pos : 0 < N₁` using `Nat.mul_pos (Nat.mul_pos hA₁ hA₂) hA₃`.

Establish `f₁N : rho₁ φ ^ N₁ = 1`. Rewrite using `[hN₁, mul_assoc, pow_mul, e₁, one_pow]`. Establish `f₂N : rho₂ φ ^ N₁ = 1`. Rewrite using `[hN₁, mul_comm A₁, mul_assoc, pow_mul, e₂, one_pow]`. Establish `fPN : rhoP φ ^ N₁ = 1`.

Rewrite using `[hN₁, mul_comm, pow_mul, e₃, one_pow]`. Use `set N₀ := n * N₁ with hN₀`. Establish `f₁0 : rho₁ φ ^ N₀ = 1` using `pow_mul_eq_one' n f₁N`. Establish `f₂0 : rho₂ φ ^ N₀ = 1` using `pow_mul_eq_one' n f₂N`. Establish `fP0 : rhoP φ ^ N₀ = 1` using `pow_mul_eq_one' n fPN`.

Use `set N := n * N₀ with hN`. Establish `hNpos : 0 < N` using `Nat.mul_pos hn0 (Nat.mul_pos hn0 hN₁pos)`. Use `haveI : NeZero N := ⟨hNpos.ne'⟩`. Establish `f₁F : rho₁ φ ^ N = 1` using `pow_mul_eq_one' n f₁0`. Establish `f₂F : rho₂ φ ^ N = 1` using `pow_mul_eq_one' n f₂0`.

Establish `fPF : rhoP φ ^ N = 1` using `pow_mul_eq_one' n fP0`. Take `⟨d, hd, hdI, hdφ⟩` from `hdeg N hNpos`. Use `set m₁ := z₁.1 φ`. Use `set m₂ := z₂.1 φ`. Establish `g₁ : geo (rho₁ φ) m₁ N = 0` using `geo_eq_zero _ hn₁ f₁0 _`.

Establish `g₂ : geo (rho₂ φ) m₂ N = 0` using `geo_eq_zero _ hn₂ f₂0 _`. Establish `g₂0 : geo (rho₂ φ) m₂ N₀ = 0` using `geo_eq_zero _ hn₂ f₂N _`. Establish `hb : ∀ x y, b (rho₁ φ x) (rho₂ φ y) = rhoP φ (b x y)` using `hbe φ`. Use `set T := tri (rho₁ φ) (rho₂ φ) b m₁ m₂ with hT`. Establish `hadd : ∀ a c, T (a + c) = T a + (rhoP φ ^ a) (T c) + b (geo (rho₁ φ) m₁ a) ((rho₂ φ ^ a) (geo (rho₂ φ) m₂ c))` using `tri_add (rho₁ φ) (rho₂ φ) (rhoP φ) b hb m₁ m₂`.

Establish `hmul : ∀ a, T (a * N₀) = a • T N₀` using `fun a => by`. Proceed by induction on `a with`. Consider the case `zero => simp [hT, tri]`. Consider the case `succ a ih`. Rewrite using `[add_mul, one_mul, hadd, ih, g₂0, pow_mul', fP0, one_pow, Module.End.one_apply, map_zero, map_zero, add_zero, add_smul, one_smul]`.

Establish `hTN : T N = 0`. Rewrite using `[hN, hmul, hnP]`. Establish `hper : Function.Periodic T N` using `fun k => by`. Rewrite using `[hadd, hTN, g₂, map_zero, map_zero, map_zero, add_zero, add_zero]`. Use `⟨fun g => - T (deg d g), continuous_comp_of_isOpen_ker d hd (fun z => - T (Multiplicative.toAdd z).val), fun g h => ?_⟩` and prove the remaining obligations.

Establish `r₂` using `rho_eq_pow hc₂ hgen hI₂ d hd hdI hdφ f₂F g`. Establish `rP` using `rho_eq_pow hcP hgen hIP d hd hdI hdφ fPF g`. Establish `y₁` using `eq_geo hc₁ hgen hI₁ d hd hdI hdφ f₁F z₁.2 h₁ g₁ g`. Establish `y₂` using `eq_geo hc₂ hgen hI₂ d hd hdI hdφ f₂F z₂.2 h₂ g₂ h`. Simplify using `only []`.

Rewrite using `[deg_mul, hper.map_mod_nat, hadd, y₁, y₂, r₂, rP, map_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_cochain {rho₁ : Representation R D M₁} {rho₂ : Representation R D M₂}
    {rhoP : Representation R D P} (b : M₁ →ₗ[R] M₂ →ₗ[R] P)
    (hbe : ∀ g x y, b (rho₁ g x) (rho₂ g y) = rhoP g (b x y))
    {n : ℕ} (hn0 : 0 < n) (hn₁ : ∀ m : M₁, n • m = 0) (hn₂ : ∀ m : M₂, n • m = 0)
    (hnP : ∀ m : P, n • m = 0)
    (hc₁ : ContAction rho₁) (hc₂ : ContAction rho₂) (hcP : ContAction rhoP)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hdeg : ∀ N : ℕ, 0 < N → ∃ d : D →* Multiplicative (ZMod N), IsOpen (d.ker : Set D) ∧
      (∀ σ ∈ I, d σ = 1) ∧ d φ = Multiplicative.ofAdd 1)
    (hI₁ : ∀ σ ∈ I, rho₁ σ = 1) (hI₂ : ∀ σ ∈ I, rho₂ σ = 1) (hIP : ∀ σ ∈ I, rhoP σ = 1)
    (z₁ : Z1 rho₁) (z₂ : Z1 rho₂) (h₁ : ∀ σ ∈ I, z₁.1 σ = 0) (h₂ : ∀ σ ∈ I, z₂.1 σ = 0) :
    ∃ c : D → P, Continuous c ∧
      ∀ g h, rhoP g (c h) - c (g * h) + c g = b (z₁.1 g) (rho₂ g (z₂.1 h)) := by
  obtain ⟨A₁, hA₁, e₁⟩ := exists_pow_eq_one rho₁ φ
  obtain ⟨A₂, hA₂, e₂⟩ := exists_pow_eq_one rho₂ φ
  obtain ⟨A₃, hA₃, e₃⟩ := exists_pow_eq_one rhoP φ
  set N₁ := A₁ * A₂ * A₃ with hN₁
  have hN₁pos : 0 < N₁ := Nat.mul_pos (Nat.mul_pos hA₁ hA₂) hA₃
  have f₁N : rho₁ φ ^ N₁ = 1 := by
    rw [hN₁, mul_assoc, pow_mul, e₁, one_pow]
  have f₂N : rho₂ φ ^ N₁ = 1 := by
    rw [hN₁, mul_comm A₁, mul_assoc, pow_mul, e₂, one_pow]
  have fPN : rhoP φ ^ N₁ = 1 := by
    rw [hN₁, mul_comm, pow_mul, e₃, one_pow]
  set N₀ := n * N₁ with hN₀
  have f₁0 : rho₁ φ ^ N₀ = 1 := pow_mul_eq_one' n f₁N
  have f₂0 : rho₂ φ ^ N₀ = 1 := pow_mul_eq_one' n f₂N
  have fP0 : rhoP φ ^ N₀ = 1 := pow_mul_eq_one' n fPN
  set N := n * N₀ with hN
  have hNpos : 0 < N := Nat.mul_pos hn0 (Nat.mul_pos hn0 hN₁pos)
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have f₁F : rho₁ φ ^ N = 1 := pow_mul_eq_one' n f₁0
  have f₂F : rho₂ φ ^ N = 1 := pow_mul_eq_one' n f₂0
  have fPF : rhoP φ ^ N = 1 := pow_mul_eq_one' n fP0
  obtain ⟨d, hd, hdI, hdφ⟩ := hdeg N hNpos
  set m₁ := z₁.1 φ
  set m₂ := z₂.1 φ
  have g₁ : geo (rho₁ φ) m₁ N = 0 := geo_eq_zero _ hn₁ f₁0 _
  have g₂ : geo (rho₂ φ) m₂ N = 0 := geo_eq_zero _ hn₂ f₂0 _
  have g₂0 : geo (rho₂ φ) m₂ N₀ = 0 := geo_eq_zero _ hn₂ f₂N _
  have hb : ∀ x y, b (rho₁ φ x) (rho₂ φ y) = rhoP φ (b x y) := hbe φ
  set T := tri (rho₁ φ) (rho₂ φ) b m₁ m₂ with hT
  have hadd : ∀ a c, T (a + c) = T a + (rhoP φ ^ a) (T c) +
      b (geo (rho₁ φ) m₁ a) ((rho₂ φ ^ a) (geo (rho₂ φ) m₂ c)) :=
    tri_add (rho₁ φ) (rho₂ φ) (rhoP φ) b hb m₁ m₂
  have hmul : ∀ a, T (a * N₀) = a • T N₀ := fun a => by
    induction a with
    | zero => simp [hT, tri]
    | succ a ih =>
      rw [add_mul, one_mul, hadd, ih, g₂0, pow_mul', fP0, one_pow, Module.End.one_apply, map_zero,
        map_zero, add_zero, add_smul, one_smul]
  have hTN : T N = 0 := by
    rw [hN, hmul, hnP]
  have hper : Function.Periodic T N := fun k => by
    rw [hadd, hTN, g₂, map_zero, map_zero, map_zero, add_zero, add_zero]
  refine ⟨fun g => - T (deg d g),
    continuous_comp_of_isOpen_ker d hd (fun z => - T (Multiplicative.toAdd z).val), fun g h => ?_⟩
  have r₂ := rho_eq_pow hc₂ hgen hI₂ d hd hdI hdφ f₂F g
  have rP := rho_eq_pow hcP hgen hIP d hd hdI hdφ fPF g
  have y₁ := eq_geo hc₁ hgen hI₁ d hd hdI hdφ f₁F z₁.2 h₁ g₁ g
  have y₂ := eq_geo hc₂ hgen hI₂ d hd hdI hdφ f₂F z₂.2 h₂ g₂ h
  simp only []
  rw [deg_mul, hper.map_mod_nat, hadd, y₁, y₂, r₂, rP, map_neg]
  abel

end Cup

section Annihilators

/- English proof (translation)
Establish `hb` using `(Submodule.inclusion_injective h).bijective_of_nat_card_le hc`. Use `le_antisymm h fun x hx => ?_` and prove the remaining obligations. Take `⟨⟨y, hy⟩, e⟩` from `hb.2 ⟨x, hx⟩`. Establish `: y = x` using `congrArg Subtype.val e`. Conclude with `this ▸ hy`.
-/
theorem eq_of_le_of_card {R X : Type*} [Semiring R] [AddCommMonoid X] [Module R X] [Finite X]
    {S T : Submodule R X} (h : S ≤ T) (hc : Nat.card T ≤ Nat.card S) : S = T := by
  have hb := (Submodule.inclusion_injective h).bijective_of_nat_card_le hc
  refine le_antisymm h fun x hx => ?_
  obtain ⟨⟨y, hy⟩, e⟩ := hb.2 ⟨x, hx⟩
  have : y = x := congrArg Subtype.val e
  exact this ▸ hy

/- English proof (translation)
Set `e : Q ≃ₗ[ZMod n] Module.Dual (ZMod n) P` to `LinearEquiv.ofBijective B hB`. Establish `h1 : Nat.card (U.dualAnnihilator.comap B) = Nat.card U.dualAnnihilator`. Use `Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Establish `h2 : Nat.card U.dualAnnihilator = Nat.card (P ⧸ U)`.

Establish `: Finite (P ⧸ U)` using `Finite.of_surjective _ (Submodule.mkQ_surjective U)`. Rewrite using `[← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]`. Conclude with `GlobalTheory.ZModDual.card_dual_eq n (P ⧸ U)`. Rewrite using `[h1, h2]`. Conclude with `(Submodule.card_eq_card_quotient_mul_card U).symm`.
-/
theorem card_mul_card_perp (n : ℕ) [NeZero n] {Q P : Type} [AddCommGroup Q] [Module (ZMod n) Q]
    [AddCommGroup P] [Module (ZMod n) P] [Finite P]
    (B : Q →ₗ[ZMod n] Module.Dual (ZMod n) P) (hB : Function.Bijective B)
    (U : Submodule (ZMod n) P) :
    Nat.card U * Nat.card (U.dualAnnihilator.comap B) = Nat.card P := by
  let e : Q ≃ₗ[ZMod n] Module.Dual (ZMod n) P := LinearEquiv.ofBijective B hB
  have h1 : Nat.card (U.dualAnnihilator.comap B) = Nat.card U.dualAnnihilator := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)
    rfl
  have h2 : Nat.card U.dualAnnihilator = Nat.card (P ⧸ U) := by
    have : Finite (P ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
    rw [← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]
    exact GlobalTheory.ZModDual.card_dual_eq n (P ⧸ U)
  rw [h1, h2]
  exact (Submodule.card_eq_card_quotient_mul_card U).symm

/- English proof (translation)
Establish `hQP : Nat.card Q = Nat.card P` using `(Nat.card_eq_of_bijective B hB).trans (GlobalTheory.ZModDual.card_dual_eq n P)`. Establish `c1` using `card_mul_card_perp n B hB U`. Establish `c2` using `card_mul_card_perp n B.flip hB' V`. Establish `hUpos : 0 < Nat.card U` using `Nat.card_pos`. Establish `hVpos : 0 < Nat.card V` using `Nat.card_pos`.

Establish `eV : V = U.dualAnnihilator.comap B`. Use `eq_of_le_of_card (fun y hy => ?_) ?_` and prove the remaining obligations. Conclude with `(Submodule.mem_dualAnnihilator _).2 fun x hx => hUV y hy x hx`. Conclude with `(Nat.eq_of_mul_eq_mul_left hUpos (c1.trans hcard.symm)).le`. Establish `eU : U = V.dualAnnihilator.comap B.flip`.

Use `eq_of_le_of_card (fun x hx => ?_) ?_` and prove the remaining obligations. Conclude with `(Submodule.mem_dualAnnihilator _).2 fun y hy => hUV y hy x hx`. Rewrite `hcard` using `[mul_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_left hVpos (c2.trans (hQP.trans hcard.symm))).le`. Use `⟨fun x => ?_, fun y => ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [eU]`. Conclude with `Submodule.mem_dualAnnihilator _`. Use `conv_lhs => rw [eV]`. Conclude with `Submodule.mem_dualAnnihilator _`.
-/
theorem exact_annihilators (n : ℕ) [NeZero n] {Q P : Type} [AddCommGroup Q] [Module (ZMod n) Q]
    [Finite Q] [AddCommGroup P] [Module (ZMod n) P] [Finite P]
    (B : Q →ₗ[ZMod n] P →ₗ[ZMod n] ZMod n) (hB : Function.Bijective B)
    (hB' : Function.Bijective B.flip) (U : Submodule (ZMod n) P) (V : Submodule (ZMod n) Q)
    (hUV : ∀ y ∈ V, ∀ x ∈ U, B y x = 0) (hcard : Nat.card U * Nat.card V = Nat.card P) :
    (∀ x, x ∈ U ↔ ∀ y ∈ V, B y x = 0) ∧ (∀ y, y ∈ V ↔ ∀ x ∈ U, B y x = 0) := by
  have hQP : Nat.card Q = Nat.card P :=
    (Nat.card_eq_of_bijective B hB).trans (GlobalTheory.ZModDual.card_dual_eq n P)
  have c1 := card_mul_card_perp n B hB U
  have c2 := card_mul_card_perp n B.flip hB' V
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have eV : V = U.dualAnnihilator.comap B := by
    refine eq_of_le_of_card (fun y hy => ?_) ?_
    · exact (Submodule.mem_dualAnnihilator _).2 fun x hx => hUV y hy x hx
    · exact (Nat.eq_of_mul_eq_mul_left hUpos (c1.trans hcard.symm)).le
  have eU : U = V.dualAnnihilator.comap B.flip := by
    refine eq_of_le_of_card (fun x hx => ?_) ?_
    · exact (Submodule.mem_dualAnnihilator _).2 fun y hy => hUV y hy x hx
    · rw [mul_comm] at hcard
      exact (Nat.eq_of_mul_eq_mul_left hVpos (c2.trans (hQP.trans hcard.symm))).le
  refine ⟨fun x => ?_, fun y => ?_⟩
  · conv_lhs => rw [eU]
    exact Submodule.mem_dualAnnihilator _
  · conv_lhs => rw [eV]
    exact Submodule.mem_dualAnnihilator _

end Annihilators

section Main

/- English proof (translation)
The claim follows from `((LinearEquiv.congrRight (M := B) j).bijective.of_comp_iff' b).2 h`.
-/
theorem bijective_compr₂ {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (b : A →ₗ[R] B →ₗ[R] C)
    (j : C ≃ₗ[R] R) (h : Function.Bijective b) : Function.Bijective (b.compr₂ j.toLinearMap) :=
  ((LinearEquiv.congrRight (M := B) j).bijective.of_comp_iff' b).2 h

variable {n : ℕ} [NeZero n] {D M : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]`.
-/
theorem nsmul_eq_zero' {X : Type*} [AddCommGroup X] [Module (ZMod n) X] (x : X) : n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

/- English proof (translation)
Establish `fT : Finite (TDual (ZMod n) M)` using `GlobalTheory.DualSide.finite_TDual`. Establish `hcT : ContAction (twDual χ rho)` using `GlobalTheory.DualSide.contAction_twDual hχ hrho`. Establish `hIT : ∀ σ ∈ I, twDual χ rho σ = 1` using `fun σ hσ => by`. Establish `hinv : rho σ⁻¹ = 1` using `hI _ (I.inv_mem hσ)`. Use `LinearMap.ext fun f => TDual.ext fun m => ?_` and prove the remaining obligations.

Simplify using `[twDual_apply, hχI σ hσ, hinv]`. Establish `hIP : ∀ σ ∈ I, charRep χ σ = 1` using `fun σ hσ => by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `[charRep_apply, hχI σ hσ]`. Establish `cU` using `card_H1ur (n := n) (NeZero.pos n) nsmul_eq_zero' hrho hgen hdeg hI`.

Establish `cV` using `card_H1ur (n := n) (NeZero.pos n) nsmul_eq_zero' hcT hgen hdeg hIT`. Establish `c2 : Nat.card (H2 rho) = Nat.card (H0 (twDual χ rho))`. Establish `e1` using `Nat.card_eq_of_bijective _ h20`. Establish `e2` using `Nat.card_congr (LinearEquiv.congrRight (M := H0 (twDual χ rho)) inv).toEquiv`. Conclude with `e1.trans (e2.trans (GlobalTheory.ZModDual.card_dual_eq n _))`.

Set `C` to `cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)`. Set `B` to `C.compr₂ inv.toLinearMap`. Establish `hB : Function.Bijective B` using `bijective_compr₂ C inv hb`. Establish `hB' : Function.Bijective B.flip` using `bijective_compr₂ C.flip inv hb'`. Establish `hz : ∀ y ∈ H1ur (twDual χ rho) I, ∀ x ∈ H1ur rho I, C y x = 0`.

Introduce `y hy x hx`. Take `⟨y', rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨x', rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `(GlobalTheory.TameQuot.cup_product_class_eq_zero_iff _ _ _ _ _ _ _ _ _).2 ?_` and prove the remaining obligations. Conclude with `exists_cochain (φ := φ) (I := I) evalPair.flip (fun g y x => evalPair_equiv χ rho g x y) (NeZero.pos n) nsmul_eq_zero' nsmul_eq_zero' nsmul_eq_zero' hcT hrho hχ hgen hdeg hIT hI hIP y' x' ((mk_mem_H1ur hIT y').1 hy) ((mk_mem_H1ur hI x').1 hx)`.

Establish `h` using `exact_annihilators n B hB hB' (H1ur rho I) (H1ur (twDual χ rho) I) (fun y hy x hx => by show inv (C y x) = 0`. Rewrite using `[hz y hy x hx, map_zero]) (by`. Use `show Nat.card (H1ur rho I) * Nat.card (H1ur (twDual χ rho) I) = Nat.card (H1 rho)`. Rewrite using `[cU, cV, hE, c2])`. Conclude with `⟨fun x => (h.1 x).trans (forall₂_congr fun _ _ => inv.map_eq_zero_iff), fun y => (h.2 y).trans (forall₂_congr fun _ _ => inv.map_eq_zero_iff)⟩`.
-/
theorem annihilators_of (χ : D →* (ZMod n)ˣ) (hχ : ContAction (charRep χ))
    (rho : Representation (ZMod n) D M) (hrho : ContAction rho) (I : Subgroup D) (φ : D)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hdeg : ∀ N : ℕ, 0 < N → ∃ d : D →* Multiplicative (ZMod N), IsOpen (d.ker : Set D) ∧
      (∀ σ ∈ I, d σ = 1) ∧ d φ = Multiplicative.ofAdd 1)
    (hχI : ∀ σ ∈ I, χ σ = 1) (hI : ∀ σ ∈ I, rho σ = 1)
    (f1 : Finite (H1 rho)) (f1' : Finite (H1 (twDual χ rho)))
    (inv : H2 (charRep χ) ≃ₗ[ZMod n] ZMod n)
    (hb : Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)))
    (hb' : Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip)
    (h20 : Function.Bijective (cup20 χ rho (MonoidHom.id _)))
    (hE : Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho)) :
    (∀ x : H1 rho, x ∈ H1ur rho I ↔ ∀ y ∈ H1ur (twDual χ rho) I,
      cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id) y x = 0) ∧
    (∀ y : H1 (twDual χ rho), y ∈ H1ur (twDual χ rho) I ↔ ∀ x ∈ H1ur rho I,
      cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id) y x = 0) := by
  have fT : Finite (TDual (ZMod n) M) := GlobalTheory.DualSide.finite_TDual
  have hcT : ContAction (twDual χ rho) := GlobalTheory.DualSide.contAction_twDual hχ hrho
  have hIT : ∀ σ ∈ I, twDual χ rho σ = 1 := fun σ hσ => by
    have hinv : rho σ⁻¹ = 1 := hI _ (I.inv_mem hσ)
    refine LinearMap.ext fun f => TDual.ext fun m => ?_
    simp [twDual_apply, hχI σ hσ, hinv]
  have hIP : ∀ σ ∈ I, charRep χ σ = 1 := fun σ hσ => by
    refine LinearMap.ext fun x => ?_
    simp [charRep_apply, hχI σ hσ]
  have cU := card_H1ur (n := n) (NeZero.pos n) nsmul_eq_zero' hrho hgen hdeg hI
  have cV := card_H1ur (n := n) (NeZero.pos n) nsmul_eq_zero' hcT hgen hdeg hIT
  have c2 : Nat.card (H2 rho) = Nat.card (H0 (twDual χ rho)) := by
    have e1 := Nat.card_eq_of_bijective _ h20
    have e2 := Nat.card_congr (LinearEquiv.congrRight (M := H0 (twDual χ rho)) inv).toEquiv
    exact e1.trans (e2.trans (GlobalTheory.ZModDual.card_dual_eq n _))
  let C := cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)
  let B := C.compr₂ inv.toLinearMap
  have hB : Function.Bijective B := bijective_compr₂ C inv hb
  have hB' : Function.Bijective B.flip := bijective_compr₂ C.flip inv hb'
  have hz : ∀ y ∈ H1ur (twDual χ rho) I, ∀ x ∈ H1ur rho I, C y x = 0 := by
    intro y hy x hx
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (GlobalTheory.TameQuot.cup_product_class_eq_zero_iff _ _ _ _ _ _ _ _ _).2 ?_
    exact exists_cochain (φ := φ) (I := I) evalPair.flip (fun g y x => evalPair_equiv χ rho g x y)
      (NeZero.pos n) nsmul_eq_zero' nsmul_eq_zero' nsmul_eq_zero' hcT hrho hχ hgen hdeg hIT hI hIP
      y' x' ((mk_mem_H1ur hIT y').1 hy) ((mk_mem_H1ur hI x').1 hx)
  have h := exact_annihilators n B hB hB' (H1ur rho I) (H1ur (twDual χ rho) I)
    (fun y hy x hx => by
      show inv (C y x) = 0
      rw [hz y hy x hx, map_zero]) (by
      show Nat.card (H1ur rho I) * Nat.card (H1ur (twDual χ rho) I) = Nat.card (H1 rho)
      rw [cU, cV, hE, c2])
  exact ⟨fun x => (h.1 x).trans (forall₂_congr fun _ _ => inv.map_eq_zero_iff),
    fun y => (h.2 y).trans (forall₂_congr fun _ _ => inv.map_eq_zero_iff)⟩

end Main

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.TameQuot GlobalTheory.WeilDeligne in

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hl hI hc`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Take `⟨φ, hφ⟩` from `exists_isFrob hA`. Establish `hgen` using `closure_frob_sup_Ine F Ω A v hA ⟨φ, hφ.1⟩ hφ`. Establish `hdeg : ∀ N : ℕ, 0 < N → ∃ d : Dec (F` using `F) A →* Multiplicative (ZMod N), IsOpen (d.ker : Set (Dec (F := F) A)) ∧ (∀ σ ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A), d σ = 1) ∧ d ⟨φ, hφ.1⟩ = Multiplicative.ofAdd 1 := fun N hN => by`.

Take `⟨d, h1, h2, h3⟩` from `exists_degMod F Ω A v hA (closure_frob_sup_Ine F Ω A v hA) N hN`. Conclude with `⟨d, h1, fun σ hσ => h2 σ hσ, h3 _ hφ⟩`. Establish `hχ : ContAction (charRep ((cycMod F Ω l r).comp (Dec (F` using `F) A).subtype)) := contAction_muDec A l r`. Establish `hχI : ∀ σ ∈ (Ine (F` using `F) A).subgroupOf (Dec (F := F) A), ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) σ = 1 := fun σ hσ => by`. Use `Units.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `PadicInt.toZModPow r ((cycZ F Ω l σ.1 : ℤ_[l]ˣ) : ℤ_[l]) = 1`. Rewrite using `[cycZ_of_mem_Ine hA hl (σ := σ.1) hσ]`. Simplify using the standard rewrite rules. Establish `: Finite (TDual (ZMod (l ^ r)) M)` using `GlobalTheory.DualSide.finite_TDual`. Establish `hcT` using `GlobalTheory.DualSide.contAction_twDual hχ hc`.

Take `⟨-, f1, -, -⟩` from `hF F Ω l r M A rho v hr hA hc`. Take `⟨-, f1', -, -⟩` from `hF F Ω l r _ A _ v hr hA hcT`. Take `⟨⟨inv⟩, -, hb, hb', h20⟩` from `hD F Ω l r M A rho v hr hA hc`. Conclude with `annihilators_of _ hχ rho hc _ ⟨φ, hφ.1⟩ hgen hdeg hχI (fun σ hσ => hI σ hσ) f1 f1' inv hb hb' h20 ((hE F Ω l r M A rho v hr hA hc).2 hl)`.
-/
theorem unramifiedOrthogonality_of (hF : LocalFiniteness) (hD : LocalTateDuality)
    (hE : LocalEulerChar) : UnramifiedOrthogonality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hl hI hc
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨φ, hφ⟩ := exists_isFrob hA
  have hgen := closure_frob_sup_Ine F Ω A v hA ⟨φ, hφ.1⟩ hφ
  have hdeg : ∀ N : ℕ, 0 < N → ∃ d : Dec (F := F) A →* Multiplicative (ZMod N),
      IsOpen (d.ker : Set (Dec (F := F) A)) ∧
      (∀ σ ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A), d σ = 1) ∧
      d ⟨φ, hφ.1⟩ = Multiplicative.ofAdd 1 := fun N hN => by
    obtain ⟨d, h1, h2, h3⟩ := exists_degMod F Ω A v hA (closure_frob_sup_Ine F Ω A v hA) N hN
    exact ⟨d, h1, fun σ hσ => h2 σ hσ, h3 _ hφ⟩
  have hχ : ContAction (charRep ((cycMod F Ω l r).comp (Dec (F := F) A).subtype)) :=
    contAction_muDec A l r
  have hχI : ∀ σ ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A),
      ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) σ = 1 := fun σ hσ => by
    refine Units.ext ?_
    change PadicInt.toZModPow r ((cycZ F Ω l σ.1 : ℤ_[l]ˣ) : ℤ_[l]) = 1
    rw [cycZ_of_mem_Ine hA hl (σ := σ.1) hσ]
    simp
  have : Finite (TDual (ZMod (l ^ r)) M) := GlobalTheory.DualSide.finite_TDual
  have hcT := GlobalTheory.DualSide.contAction_twDual hχ hc
  obtain ⟨-, f1, -, -⟩ := hF F Ω l r M A rho v hr hA hc
  obtain ⟨-, f1', -, -⟩ := hF F Ω l r _ A _ v hr hA hcT
  obtain ⟨⟨inv⟩, -, hb, hb', h20⟩ := hD F Ω l r M A rho v hr hA hc
  exact annihilators_of _ hχ rho hc _ ⟨φ, hφ.1⟩ hgen hdeg hχI (fun σ hσ => hI σ hσ) f1 f1' inv
    hb hb' h20 ((hE F Ω l r M A rho v hr hA hc).2 hl)

end GlobalTheory.CompanionTheory.Hypotheses₂.UnrOrth
