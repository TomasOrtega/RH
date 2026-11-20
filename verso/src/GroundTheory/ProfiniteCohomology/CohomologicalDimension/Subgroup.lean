import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
import GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/- English proof (translation)
Rewrite using `[cdp_le_iff]`. Introduce `A _ hA q hq`. Choose the witnesses or unpack the hypotheses as in `⟨q', rfl⟩ : ∃ q', q = q' + 1 := by`. Consider the cases of `q with`. Consider the case `zero => simp at hq`.

Consider the case `succ q => exact ⟨q, rfl⟩`. Establish `h0` using `primaryComponent_cohomology_eq_bot_of_cdp_lt (Rep.res H.subtype A) hA hq`. Rewrite `h0`, the goal using `[primaryComponent_eq_bot_iff]`. Introduce and unpack `x ⟨k, hk⟩`. Establish `h1 : (cohomologyRes A H (q' + 1)).hom x = 0` using `h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩`.

Take `⟨U, hUo, hHU, hU⟩` from `exists_cohomologyRes_eq_zero A hH q' x h1`. Set `U' : OpenSubgroup G` to `⟨U, hUo⟩`. Establish `: Finite (G ⧸ U)` using `Subgroup.quotient_finite_of_isOpen U hUo`. Establish `hUne : U.index ≠ 0` using `Subgroup.index_ne_zero_of_finite`. Establish `hndvd : ¬ p ∣ U.index`.

Introduce `hpU`. Apply `hdvd` to reduce the goal to its premises. Establish `h2 : superIndex U ∣ superIndex H` using `superIndex_dvd_of_le hHU`. Rewrite `h2` using `[superIndex_of_isOpen hUo]`. Conclude with `((Supernatural.ofNat_dvd_ofNat hp.ne_zero hUne).2 hpU).trans h2`.

Establish `hU' : (cohomologyRes A (U' : Subgroup G) (q' + 1)).hom x = 0` using `hU`. Establish `h2 : U.index • x = 0`. Use `congrArg (fun φ => φ.hom x) (cohomologyRes_comp_cohomologyCores U' A (q' + 1))` as an intermediate fact. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply, hU', map_zero] at this`. Conclude with `this.symm`.

Establish `hcop : Nat.Coprime (p ^ k) U.index` using `Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)`. Establish `h3 : addOrderOf x ∣ Nat.gcd (p ^ k) U.index` using `Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk) (addOrderOf_dvd_of_nsmul_eq_zero h2)`. Rewrite `h3` using `[hcop.gcd_eq_one, Nat.dvd_one]`. Conclude with `AddMonoid.addOrderOf_eq_one_iff.1 h3`.
-/
theorem cdp_le_cdp_closedSubgroup {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (hdvd : ¬ Supernatural.ofNat p ∣ superIndex H) :
    cdp p G ≤ cdp p H := by
  rw [cdp_le_iff]
  intro A _ hA q hq
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
    cases q with
    | zero => simp at hq
    | succ q => exact ⟨q, rfl⟩
  have h0 := primaryComponent_cohomology_eq_bot_of_cdp_lt (Rep.res H.subtype A) hA hq
  rw [primaryComponent_eq_bot_iff] at h0 ⊢
  rintro x ⟨k, hk⟩
  have h1 : (cohomologyRes A H (q' + 1)).hom x = 0 :=
    h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  obtain ⟨U, hUo, hHU, hU⟩ := exists_cohomologyRes_eq_zero A hH q' x h1
  let U' : OpenSubgroup G := ⟨U, hUo⟩
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUo
  have hUne : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hndvd : ¬ p ∣ U.index := by
    intro hpU
    apply hdvd
    have h2 : superIndex U ∣ superIndex H := superIndex_dvd_of_le hHU
    rw [superIndex_of_isOpen hUo] at h2
    exact ((Supernatural.ofNat_dvd_ofNat hp.ne_zero hUne).2 hpU).trans h2
  have hU' : (cohomologyRes A (U' : Subgroup G) (q' + 1)).hom x = 0 := hU
  have h2 : U.index • x = 0 := by
    have := congrArg (fun φ => φ.hom x) (cohomologyRes_comp_cohomologyCores U' A (q' + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hU', map_zero] at this
    exact this.symm
  have hcop : Nat.Coprime (p ^ k) U.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
  have h3 : addOrderOf x ∣ Nat.gcd (p ^ k) U.index :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
  exact AddMonoid.addOrderOf_eq_one_iff.1 h3

section Summand

attribute [local instance 2000] Rep.hV2

omit [TotallyDisconnectedSpace G] in

/- English proof (translation)
Distinguish the cases in `hnt : Nontrivial A`. Take `⟨a₀, ha₀⟩` from `exists_ne (0 : A)`. Take `⟨W, hW, hWfin, haW⟩` from `exists_finite_stable_submodule A hp.pos (fun a => ⟨1, by rw [pow_one]; exact hA a⟩) a₀`. Set `W' : Subrepresentation A.ρ` to `⟨W, fun g v hv => hW g hv⟩`. Break down `hsimple.eq_bot_or_eq_top W' with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `: a₀ ∈ W'.toSubmodule` using `haW`. Rewrite `this` using `[h]`. Conclude with `ha₀ ((Submodule.mem_bot _).1 this)`. Establish `hall : ∀ a : A, a ∈ W` using `fun a => by`.

Establish `: a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `this` using `[← h]`. Conclude with `this`. Conclude with `Finite.of_injective (fun x : A => (⟨x, hall x⟩ : W)) fun x y h => congrArg Subtype.val h`. Rewrite `hnt`, `infer_instance` using `[not_nontrivial_iff_subsingleton]`.
-/
theorem finite_of_isSimpleOrder {p : ℕ} (hp : p.Prime) (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] (hsimple : IsSimpleOrder (Subrepresentation A.ρ))
    (hA : ∀ a : A, p • a = 0) : Finite A := by
  by_cases hnt : Nontrivial A
  · obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
    obtain ⟨W, hW, hWfin, haW⟩ := exists_finite_stable_submodule A hp.pos
      (fun a => ⟨1, by rw [pow_one]; exact hA a⟩) a₀
    let W' : Subrepresentation A.ρ := ⟨W, fun g v hv => hW g hv⟩
    rcases hsimple.eq_bot_or_eq_top W' with h | h
    · exfalso
      have : a₀ ∈ W'.toSubmodule := haW
      rw [h] at this
      exact ha₀ ((Submodule.mem_bot _).1 this)
    · have hall : ∀ a : A, a ∈ W := fun a => by
        have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
        rw [← h] at this
        exact this
      exact Finite.of_injective (fun x : A => (⟨x, hall x⟩ : W)) fun x y h => congrArg Subtype.val h
  · rw [not_nontrivial_iff_subsingleton] at hnt
    infer_instance

end Summand

section Coinduction

variable {k : Type u} [CommRing k] (H V : Subgroup G) [hVn : V.Normal] (A : Rep.{u} k H)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def coindFixed : Submodule k (Rep.coind H.subtype A) :=
  Representation.invariants ((Rep.coind H.subtype A).ρ.comp V.subtype)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Introduce `f hf v`. Establish `hv : g⁻¹ * (v : G) * g ∈ V`. Use `hVn.conj_mem _ v.2 g⁻¹` as an intermediate fact. Simplify using `using this`. Establish `h1 : (Rep.coind H.subtype A).ρ (v : G) ((Rep.coind H.subtype A).ρ g f) = (Rep.coind H.subtype A).ρ g ((Rep.coind H.subtype A).ρ (g⁻¹ * (v : G) * g) f)`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use `group`. Express the relevant statement in the definitionally equal form `(Rep.coind H.subtype A).ρ (v : G) ((Rep.coind H.subtype A).ρ g f) = (Rep.coind H.subtype A).ρ g f`. Rewrite using `[h1]`.

Use `congr 1`. Conclude with `hf ⟨_, hv⟩`.
-/
theorem coindFixed_le_comap (g : G) :
    coindFixed H V A ≤ (coindFixed H V A).comap ((Rep.coind H.subtype A).ρ g) := by
  intro f hf v
  have hv : g⁻¹ * (v : G) * g ∈ V := by
    have := hVn.conj_mem _ v.2 g⁻¹
    simpa using this
  have h1 : (Rep.coind H.subtype A).ρ (v : G) ((Rep.coind H.subtype A).ρ g f) =
      (Rep.coind H.subtype A).ρ g ((Rep.coind H.subtype A).ρ (g⁻¹ * (v : G) * g) f) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  change (Rep.coind H.subtype A).ρ (v : G) ((Rep.coind H.subtype A).ρ g f) =
    (Rep.coind H.subtype A).ρ g f
  rw [h1]
  congr 1
  exact hf ⟨_, hv⟩

noncomputable abbrev coindFixedRep : Rep.{u} k G :=
  (Rep.coind H.subtype A).subrepresentation (coindFixed H V A) (coindFixed_le_comap H V A)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun m => Subgroup.isOpen_mono (fun v hv => Subtype.ext (m.2 ⟨v, hv⟩)) hV⟩`.
-/
theorem isDiscreteRep_coindFixedRep (hV : IsOpen (V : Set G)) :
    IsDiscreteRep (coindFixedRep H V A) :=
  ⟨fun m => Subgroup.isOpen_mono (fun v hv => Subtype.ext (m.2 ⟨v, hv⟩)) hV⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] hVn in

noncomputable def coindFixedEval : Rep.res H.subtype (coindFixedRep H V A) ⟶ A :=
  Rep.ofHom ⟨{ toFun := fun m => m.1.1 1
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl },
    fun h => by
      ext m
      change m.1.1 (1 * (h : G)) = A.ρ h (m.1.1 1)
      rw [one_mul]
      simpa using m.1.2 h 1⟩

variable {H V A}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  hVn in
/- English proof (translation)
Establish `e : h₂ = h₁ * (h₁⁻¹ * h₂)` using `by group`. Rewrite using `[e, map_mul, Module.End.mul_apply, hfix (h₁⁻¹ * h₂) (by simpa using h)]`.
-/
theorem rho_eq_of_inv_mul_mem (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) {h₁ h₂ : H}
    (h : (h₁ : G)⁻¹ * h₂ ∈ V) (a : A) : A.ρ h₁ a = A.ρ h₂ a := by
  have e : h₂ = h₁ * (h₁⁻¹ * h₂) := by group
  rw [e, map_mul, Module.End.mul_apply, hfix (h₁⁻¹ * h₂) (by simpa using h)]

variable (H V) in
omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  hVn in
open scoped Classical in

noncomputable def summandFun (a : A) (x : G) : A :=
  if hx : x ∈ H ⊔ V then A.ρ (supSection H V ⟨x, hx⟩) a else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Establish `hmem : (h : G) * x ∈ H ⊔ V ↔ x ∈ H ⊔ V` using `Subgroup.mul_mem_cancel_left _ (le_sup_left (a := H) (b := V) h.2)`. Distinguish the cases in `hx : x ∈ H ⊔ V`. Establish `hx' : (h : G) * x ∈ H ⊔ V` using `hmem.2 hx`. Simplify using `only [summandFun, dif_pos hx, dif_pos hx']`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Apply `rho_eq_of_inv_mul_mem hfix` to reduce the goal to its premises. Use `inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_` and prove the remaining obligations. Use `inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hx' : (h : G) * x ∉ H ⊔ V` using `fun h' => hx (hmem.1 h')`.

Simplify using `only [summandFun, dif_neg hx, dif_neg hx', map_zero]`.
-/
theorem summandFun_mul_left (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) (a : A)
    (h : H) (x : G) : summandFun H V a ((h : G) * x) = A.ρ h (summandFun H V a x) := by
  have hmem : (h : G) * x ∈ H ⊔ V ↔ x ∈ H ⊔ V :=
    Subgroup.mul_mem_cancel_left _ (le_sup_left (a := H) (b := V) h.2)
  by_cases hx : x ∈ H ⊔ V
  · have hx' : (h : G) * x ∈ H ⊔ V := hmem.2 hx
    simp only [summandFun, dif_pos hx, dif_pos hx']
    rw [← Module.End.mul_apply, ← map_mul]
    apply rho_eq_of_inv_mul_mem hfix
    refine inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_
    have := inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)
    simpa [mul_assoc] using this
  · have hx' : (h : G) * x ∉ H ⊔ V := fun h' => hx (hmem.1 h')
    simp only [summandFun, dif_neg hx, dif_neg hx', map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Establish `hmem : x * k' ∈ H ⊔ V ↔ x ∈ H ⊔ V` using `Subgroup.mul_mem_cancel_right _ (le_sup_left (a := H) (b := V) k'.2)`. Distinguish the cases in `hx : x ∈ H ⊔ V`. Establish `hx' : x * k' ∈ H ⊔ V` using `hmem.2 hx`. Simplify using `only [summandFun, dif_pos hx, dif_pos hx']`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Apply `rho_eq_of_inv_mul_mem hfix` to reduce the goal to its premises. Use `inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_` and prove the remaining obligations. Establish `h1` using `inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)`. Establish `h2 : (k' : G)⁻¹ * (x⁻¹ * (supSection H V ⟨x, hx⟩ : G)) * k' ∈ V`. Use `hVn.conj_mem _ h1 (k' : G)⁻¹` as an intermediate fact.

Simplify using `using this`. Simplify `h2` using `[mul_assoc]`. Establish `hx' : x * k' ∉ H ⊔ V` using `fun h' => hx (hmem.1 h')`. Simplify using `only [summandFun, dif_neg hx, dif_neg hx']`.
-/
theorem summandFun_mul_right (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) (a : A)
    (k' : H) (x : G) : summandFun H V a (x * k') = summandFun H V (A.ρ k' a) x := by
  have hmem : x * k' ∈ H ⊔ V ↔ x ∈ H ⊔ V :=
    Subgroup.mul_mem_cancel_right _ (le_sup_left (a := H) (b := V) k'.2)
  by_cases hx : x ∈ H ⊔ V
  · have hx' : x * k' ∈ H ⊔ V := hmem.2 hx
    simp only [summandFun, dif_pos hx, dif_pos hx']
    rw [← Module.End.mul_apply, ← map_mul]
    apply rho_eq_of_inv_mul_mem hfix
    refine inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_
    have h1 := inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)
    have h2 : (k' : G)⁻¹ * (x⁻¹ * (supSection H V ⟨x, hx⟩ : G)) * k' ∈ V := by
      have := hVn.conj_mem _ h1 (k' : G)⁻¹
      simpa using this
    simpa [mul_assoc] using h2
  · have hx' : x * k' ∉ H ⊔ V := fun h' => hx (hmem.1 h')
    simp only [summandFun, dif_neg hx, dif_neg hx']

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Establish `hmem : x * v ∈ H ⊔ V ↔ x ∈ H ⊔ V` using `Subgroup.mul_mem_cancel_right _ (le_sup_right (a := H) (b := V) hv)`. Distinguish the cases in `hx : x ∈ H ⊔ V`. Establish `hx' : x * v ∈ H ⊔ V` using `hmem.2 hx`. Simplify using `only [summandFun, dif_pos hx, dif_pos hx']`. Apply `rho_eq_of_inv_mul_mem hfix` to reduce the goal to its premises.

Use `inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_` and prove the remaining obligations. Establish `h1` using `inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)`. Establish `h2 : v⁻¹ * (x⁻¹ * (supSection H V ⟨x, hx⟩ : G)) ∈ V` using `V.mul_mem (V.inv_mem hv) h1`. Simplify `h2` using `[mul_assoc]`. Establish `hx' : x * v ∉ H ⊔ V` using `fun h' => hx (hmem.1 h')`.

Simplify using `only [summandFun, dif_neg hx, dif_neg hx']`.
-/
theorem summandFun_mul_right_of_mem (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a)
    (a : A) (v : G) (hv : v ∈ V) (x : G) : summandFun H V a (x * v) = summandFun H V a x := by
  have hmem : x * v ∈ H ⊔ V ↔ x ∈ H ⊔ V :=
    Subgroup.mul_mem_cancel_right _ (le_sup_right (a := H) (b := V) hv)
  by_cases hx : x ∈ H ⊔ V
  · have hx' : x * v ∈ H ⊔ V := hmem.2 hx
    simp only [summandFun, dif_pos hx, dif_pos hx']
    apply rho_eq_of_inv_mul_mem hfix
    refine inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_
    have h1 := inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)
    have h2 : v⁻¹ * (x⁻¹ * (supSection H V ⟨x, hx⟩ : G)) ∈ V := V.mul_mem (V.inv_mem hv) h1
    simpa [mul_assoc] using h2
  · have hx' : x * v ∉ H ⊔ V := fun h' => hx (hmem.1 h')
    simp only [summandFun, dif_neg hx, dif_neg hx']

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Establish `h1 : (1 : G) ∈ H ⊔ V` using `one_mem _`. Simplify using `only [summandFun, dif_pos h1]`. Rewrite using `[← rho_eq_of_inv_mul_mem hfix (h₁ := 1) ?_ a, map_one, Module.End.one_apply]`. Use `V.inv_mem (supSection_spec H V ⟨1, h1⟩)` as an intermediate fact. Simplify using `using this`.
-/
theorem summandFun_one (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) (a : A) :
    summandFun H V a 1 = a := by
  have h1 : (1 : G) ∈ H ⊔ V := one_mem _
  simp only [summandFun, dif_pos h1]
  rw [← rho_eq_of_inv_mul_mem hfix (h₁ := 1) ?_ a, map_one, Module.End.one_apply]
  have := V.inv_mem (supSection_spec H V ⟨1, h1⟩)
  simpa using this

end Coinduction

section Splitting

variable {k : Type u} [CommRing k] {H V : Subgroup G} [hVn : V.Normal] {A : Rep.{u} k H}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Simplify using `only [summandFun]`. Apply the tactic sequence `split_ifs <;> simp [map_add]`.
-/
theorem summandFun_add (a b : A) (x : G) :
    summandFun H V (a + b) x = summandFun H V a x + summandFun H V b x := by
  simp only [summandFun]
  split_ifs <;> simp [map_add]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Simplify using `only [summandFun]`. Apply the tactic sequence `split_ifs <;> simp [map_smul]`.
-/
theorem summandFun_smul (r : k) (a : A) (x : G) :
    summandFun H V (r • a) x = r • summandFun H V a x := by
  simp only [summandFun]
  split_ifs <;> simp [map_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def summandMap (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) :
    A ⟶ Rep.res H.subtype (coindFixedRep H V A) :=
  Rep.ofHom ⟨{ toFun := fun a => ⟨⟨summandFun H V a, fun h x => summandFun_mul_left hfix a h x⟩,
                  fun v => Subtype.ext (funext fun x => summandFun_mul_right_of_mem hfix a v v.2 x)⟩
               map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun x => summandFun_add a b x))
               map_smul' := fun r a =>
                 Subtype.ext (Subtype.ext (funext fun x => summandFun_smul r a x)) },
    fun h => LinearMap.ext fun a => Subtype.ext (Subtype.ext (funext fun x =>
      (summandFun_mul_right hfix a h x).symm))⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

/- English proof (translation)
Use extensionality with `a`. Conclude with `summandFun_one hfix a`.
-/
theorem summandMap_comp_coindFixedEval (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) :
    summandMap hfix ≫ coindFixedEval H V A = 𝟙 A := by
  ext a
  exact summandFun_one hfix a

end Splitting

section Main

attribute [local instance 2000] Rep.hV2

/- English proof (translation)
Distinguish the cases in `htop : cdp p G = ⊤`. Rewrite using `[htop]`. Conclude with `le_top`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.1 htop`. Establish `hcd : cdp p G ≤ n` using `hn ▸ le_rfl`.

Rewrite using `[← hn]`. Establish `: CompactSpace H` using `isCompact_iff_compactSpace.mp hH.isCompact`. Rewrite using `[cdp_le_iff_forall_simple hp]`. Introduce `A _ hsimple hA`. Establish `hfin : Finite A` using `finite_of_isSimpleOrder hp A hsimple hA`.

Establish `hdisc` using `(isDiscreteRep_iff_forall_exists_openNormalSubgroup A).1 inferInstance`. Use `choose W hW using hdisc`. Take `⟨W₀, hW₀⟩` from `OpenNormalSubgroup.exists_le_of_finite W`. Take `⟨V, hV⟩` from `exists_subgroupOf_le W₀`. Establish `hfix : ∀ h : H, (h : G) ∈ (V : Subgroup G) → ∀ a : A, A.ρ h a = a`.

Introduce `h hh a`. Establish `hh' : h ∈ (W a : Subgroup H)` using `hW₀ a (hV (Subgroup.mem_subgroupOf.2 hh))`. Conclude with `(Representation.mem_invariants _ _).1 (hW a) ⟨h, hh'⟩`. Establish `hM : IsDiscreteRep (coindFixedRep H (V : Subgroup G) A)` using `isDiscreteRep_coindFixedRep H (V : Subgroup G) A V.isOpen'`. Establish `hMH : IsDiscreteRep (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A))` using `isDiscreteRep_res_subtype _ H`.

Establish `hMp : ∀ m : coindFixedRep H (V : Subgroup G) A, p • m = 0` using `fun m => Subtype.ext (Subtype.ext (funext fun x => hA (m.1.1 x)))`. Establish `hvan : Subsingleton (cohomology (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A)) (n + 1))`. Use `⟨fun y₁ y₂ => ?_⟩` and prove the remaining obligations. It suffices to establish `h0 : ∀ y : cohomology (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A)) (n + 1), y = 0 by rw [h0 y₁, h0 y₂]`. Introduce `y`.

Take `⟨U, hUo, hHU, y', rfl⟩` from `exists_cohomologyResLE_eq _ hH (n + 1) y`. Establish `hU : cdp p U ≤ n` using `(cdp_openSubgroup_le p ⟨U, hUo⟩).trans hcd`. Establish `: IsDiscreteRep (Rep.res U.subtype (coindFixedRep H (V : Subgroup G) A))` using `isDiscreteRep_res_subtype _ U`. Establish `hs` using `subsingleton_cohomology_of_cdp_le hp hU (Rep.res U.subtype (coindFixedRep H (V : Subgroup G) A)) (fun m => hMp m) (Nat.lt_succ_self n)`. Rewrite using `[Subsingleton.elim y' 0, map_zero]`.

Use `⟨fun x₁ x₂ => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : cohomology A (n + 1), x = (cohomologyMap (coindFixedEval H (V : Subgroup G) A) (n + 1)).hom ((cohomologyMap (summandMap hfix) (n + 1)).hom x)`. Introduce `x`. Express the relevant statement in the definitionally equal form `x = (cohomologyMap (summandMap hfix) (n + 1) ≫ cohomologyMap (coindFixedEval H (V : Subgroup G) A) (n + 1)).hom x`. Rewrite using `[← cohomologyMap_comp, summandMap_comp_coindFixedEval, cohomologyMap_id]`.

Both sides reduce to the same expression. Rewrite using `[key x₁, key x₂, Subsingleton.elim ((cohomologyMap (summandMap hfix) (n + 1)).hom x₁)]`.
-/
theorem cdp_closedSubgroup_le {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    cdp p H ≤ cdp p G := by
  by_cases htop : cdp p G = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hcd : cdp p G ≤ n := hn ▸ le_rfl
  rw [← hn]
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  rw [cdp_le_iff_forall_simple hp]
  intro A _ hsimple hA
  have hfin : Finite A := finite_of_isSimpleOrder hp A hsimple hA

  have hdisc := (isDiscreteRep_iff_forall_exists_openNormalSubgroup A).1 inferInstance
  choose W hW using hdisc
  obtain ⟨W₀, hW₀⟩ := OpenNormalSubgroup.exists_le_of_finite W
  obtain ⟨V, hV⟩ := exists_subgroupOf_le W₀
  have hfix : ∀ h : H, (h : G) ∈ (V : Subgroup G) → ∀ a : A, A.ρ h a = a := by
    intro h hh a
    have hh' : h ∈ (W a : Subgroup H) := hW₀ a (hV (Subgroup.mem_subgroupOf.2 hh))
    exact (Representation.mem_invariants _ _).1 (hW a) ⟨h, hh'⟩

  have hM : IsDiscreteRep (coindFixedRep H (V : Subgroup G) A) :=
    isDiscreteRep_coindFixedRep H (V : Subgroup G) A V.isOpen'
  have hMH : IsDiscreteRep (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A)) :=
    isDiscreteRep_res_subtype _ H
  have hMp : ∀ m : coindFixedRep H (V : Subgroup G) A, p • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hA (m.1.1 x)))

  have hvan : Subsingleton (cohomology (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A))
      (n + 1)) := by
    refine ⟨fun y₁ y₂ => ?_⟩
    suffices h0 : ∀ y : cohomology (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A)) (n + 1),
        y = 0 by rw [h0 y₁, h0 y₂]
    intro y
    obtain ⟨U, hUo, hHU, y', rfl⟩ := exists_cohomologyResLE_eq _ hH (n + 1) y
    have hU : cdp p U ≤ n := (cdp_openSubgroup_le p ⟨U, hUo⟩).trans hcd
    have : IsDiscreteRep (Rep.res U.subtype (coindFixedRep H (V : Subgroup G) A)) :=
      isDiscreteRep_res_subtype _ U
    have hs := subsingleton_cohomology_of_cdp_le hp hU
      (Rep.res U.subtype (coindFixedRep H (V : Subgroup G) A)) (fun m => hMp m) (Nat.lt_succ_self n)
    rw [Subsingleton.elim y' 0, map_zero]

  refine ⟨fun x₁ x₂ => ?_⟩
  have key : ∀ x : cohomology A (n + 1), x =
      (cohomologyMap (coindFixedEval H (V : Subgroup G) A) (n + 1)).hom
        ((cohomologyMap (summandMap hfix) (n + 1)).hom x) := by
    intro x
    change x = (cohomologyMap (summandMap hfix) (n + 1) ≫
      cohomologyMap (coindFixedEval H (V : Subgroup G) A) (n + 1)).hom x
    rw [← cohomologyMap_comp, summandMap_comp_coindFixedEval, cohomologyMap_id]
    rfl
  rw [key x₁, key x₂, Subsingleton.elim ((cohomologyMap (summandMap hfix) (n + 1)).hom x₁)]

end Main

/- English proof (translation)
The claim follows from `le_antisymm (cdp_closedSubgroup_le hp hH) (cdp_le_cdp_closedSubgroup hp hH hdvd)`.
-/
theorem cdp_closedSubgroup_eq {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hdvd : ¬ Supernatural.ofNat p ∣ superIndex H) : cdp p H = cdp p G :=
  le_antisymm (cdp_closedSubgroup_le hp hH) (cdp_le_cdp_closedSubgroup hp hH hdvd)

/- English proof (translation)
The claim follows from `cdp_closedSubgroup_eq hp hP.1 hP.2.2`.
-/
theorem cdp_eq_of_isProSylow {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsProSylow p P) :
    cdp p P = cdp p G :=
  cdp_closedSubgroup_eq hp hP.1 hP.2.2

end GroundTheory.ProfCoh
