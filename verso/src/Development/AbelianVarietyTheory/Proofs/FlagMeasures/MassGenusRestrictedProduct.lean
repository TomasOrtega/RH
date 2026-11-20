import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqOfFiniteDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeRelIndexPiUnivEqFinprod
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

def resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A : ∀ i, Subgroup (G i)) :
    Subgroup (∀ i, G i) where
  carrier := {g | {i | g i ∉ A i}.Finite}
  one_mem' := by
    have : {i | (1 : ∀ i, G i) i ∉ A i} = ∅ := by
      ext i; simp [one_mem]
    simp only [Set.mem_setOf_eq, this, Set.finite_empty]
  mul_mem' := by
    intro a b ha hb
    refine (Set.Finite.union ha hb).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (mul_mem h.1 h.2)
  inv_mem' := by
    intro a ha
    refine Set.Finite.subset ha (fun i hi => ?_)
    simpa using hi

/- English proof (translation)
Introduce `g hg`. Use `Set.Finite.subset h (fun i hi hAU => hi ?_)` and prove the remaining obligations. Rewrite using `[hAU]`. Conclude with `hg i (Set.mem_univ i)`.
-/
theorem pi_le_resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A U : ∀ i, Subgroup (G i))
    (h : {i | A i ≠ U i}.Finite) : Subgroup.pi Set.univ U ≤ resPi A := by
  intro g hg
  refine Set.Finite.subset h (fun i hi hAU => hi ?_)
  rw [hAU]
  exact hg i (Set.mem_univ i)

/- English proof (translation)
Use `haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩`. Use `haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _`. Use `⟨Finset.univ.image (fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : G)), ?_⟩` and prove the remaining obligations. Introduce `k hk`. Use `⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨k, hk⟩)), ?_⟩` and prove the remaining obligations.

Establish `h1 : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ L.subgroupOf K) : K) : K ⧸ L.subgroupOf K) = QuotientGroup.mk ⟨k, hk⟩` using `QuotientGroup.out_eq' _`. Establish `h2` using `QuotientGroup.eq.1 h1`. Simplify `h2` using `[Subgroup.mem_subgroupOf]`.
-/
theorem exists_finset_cosets {G : Type} [Group G] (K L : Subgroup G) (h : L.relIndex K ≠ 0) :
    ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, t⁻¹ * k ∈ L := by
  haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : G)), ?_⟩
  intro k hk
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨k, hk⟩)), ?_⟩
  have h1 : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ L.subgroupOf K) : K) :
      K ⧸ L.subgroupOf K) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.1 h1
  simpa [Subgroup.mem_subgroupOf] using h2

/- English proof (translation)
Take `⟨S, hS⟩` from `hS`. Take `⟨T, hT⟩` from `exists_finset_cosets KA K0 h`. Use `⟨Finset.image₂ (· * ·) S T, fun g => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, γ, hγ, κ, hκ, rfl⟩` from `hS g`. Take `⟨t, ht, htκ⟩` from `hT κ hκ`.

Conclude with `⟨a * t, Finset.mem_image₂_of_mem ha ht, γ, hγ, t⁻¹ * κ, htκ, by group⟩`.
-/
theorem double_cosets_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : K0.relIndex KA ≠ 0)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ KA, g = γ * a * κ) :
    ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨T, hT⟩ := exists_finset_cosets KA K0 h
  refine ⟨Finset.image₂ (· * ·) S T, fun g => ?_⟩
  obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
  obtain ⟨t, ht, htκ⟩ := hT κ hκ
  exact ⟨a * t, Finset.mem_image₂_of_mem ha ht, γ, hγ, t⁻¹ * κ, htκ, by group⟩

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_finset_cosets K0 KA h`. Establish `hpiece : ∀ t ∈ T, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ * a) ∈ KA}.Finite`. Introduce `t _`. Distinguish the cases in `hne : ∃ γ₀, γ₀ ∈ Γ ∧ a⁻¹ * γ₀ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ₀ * a) ∈ KA`. Take `⟨γ₀, hγ₀, -, h₀⟩` from `hne`.

Use `((hF a).image (fun δ => γ₀ * δ)).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨hγ, -, h₁⟩`. Use `⟨γ₀⁻¹ * γ, ⟨Γ.mul_mem (Γ.inv_mem hγ₀) hγ, ?_⟩, by group⟩` and prove the remaining obligations. Use `KA.mul_mem (KA.inv_mem h₀) h₁` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `group`. Use `Set.Finite.subset Set.finite_empty ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨h1, h2, h3⟩`. Conclude with `hne ⟨γ, h1, h2, h3⟩`. Use `(T.finite_toSet.biUnion hpiece).subset ?_` and prove the remaining obligations.

Introduce and unpack `γ ⟨hγ, hk⟩`. Take `⟨t, ht, htk⟩` from `hT _ hk`. Conclude with `Set.mem_biUnion ht ⟨hγ, hk, htk⟩`.
-/
theorem finite_conj_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : KA.relIndex K0 ≠ 0) (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ KA}.Finite) (a : G) :
    {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
  obtain ⟨T, hT⟩ := exists_finset_cosets K0 KA h
  have hpiece : ∀ t ∈ T, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ * a) ∈ KA}.Finite := by
    intro t _
    by_cases hne : ∃ γ₀, γ₀ ∈ Γ ∧ a⁻¹ * γ₀ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ₀ * a) ∈ KA
    · obtain ⟨γ₀, hγ₀, -, h₀⟩ := hne
      refine ((hF a).image (fun δ => γ₀ * δ)).subset ?_
      rintro γ ⟨hγ, -, h₁⟩
      refine ⟨γ₀⁻¹ * γ, ⟨Γ.mul_mem (Γ.inv_mem hγ₀) hγ, ?_⟩, by group⟩
      have := KA.mul_mem (KA.inv_mem h₀) h₁
      convert this using 1
      group
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨h1, h2, h3⟩
      exact hne ⟨γ, h1, h2, h3⟩
  refine (T.finite_toSet.biUnion hpiece).subset ?_
  rintro γ ⟨hγ, hk⟩
  obtain ⟨t, ht, htk⟩ := hT _ hk
  exact Set.mem_biUnion ht ⟨hγ, hk, htk⟩

/- English proof (translation)
Simplify using `only [invVol, Subgroup.relIndex_subgroupOf hK, Subgroup.relIndex_subgroupOf hL]`.
-/
theorem invVol_subgroupOf {G : Type} [Group G] (R K L : Subgroup G) (hK : K ≤ R) (hL : L ≤ R) :
    invVol (K.subgroupOf R) (L.subgroupOf R) = invVol K L := by
  simp only [invVol, Subgroup.relIndex_subgroupOf hK, Subgroup.relIndex_subgroupOf hL]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `rfl : r = s.r := by`. Use function extensionality and compare the values at `a b`. Conclude with `propext (hr a b)`. Both sides reduce to the same expression.
-/
theorem tsum_quot_out {Y : Type} (r : Y → Y → Prop) (s : Setoid Y) (hr : ∀ a b, r a b ↔ s.r a b)
    (F : Y → ℝ≥0∞) : ∑' o : Quot r, F o.out = ∑' o : Quotient s, F o.out := by
  obtain rfl : r = s.r := by
    funext a b
    exact propext (hr a b)
  rfl

/- English proof (translation)
Use extensionality with `g`. Simplify using `[MulAction.mem_stabilizer_iff, Subgroup.mem_pi, funext_iff]`.
-/
theorem stabilizer_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] {X : ι → Type}
    [∀ i, MulAction (G i) (X i)] (x : ∀ i, X i) :
    MulAction.stabilizer (∀ i, G i) x =
      Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_pi, funext_iff]

/- English proof (translation)
Use extensionality with `g`. Simplify using `[MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]`.
-/
theorem stabilizer_res {P : Type} [Group P] (R : Subgroup P) {Y : Type} [MulAction P Y] (y : Y) :
    MulAction.stabilizer R y = (MulAction.stabilizer P y).subgroupOf R := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]

end GlobalTheory.HL

namespace GlobalTheory.HL

/- English proof (translation)
Introduce `ι G _ X _ A H _ φ hinj hres hdc hfin x0 hcomm hae`. Use `set R := resPi A with hRdef`. Set `φ' : H →* R` to `φ.codRestrict R hres`. Establish `hφ' : ∀ h, ((φ' h : R) : ∀ i, G i) = φ h` using `fun h => rfl`. Use `set Γ : Subgroup R := φ'.range with hΓ`.

Use `set KA : Subgroup R := (Subgroup.pi Set.univ A).subgroupOf R with hKA`. Use `set K0 : Subgroup R := MulAction.stabilizer R x0 with hK0`. Establish `hAR : Subgroup.pi Set.univ A ≤ R` using `pi_le_resPi A A (by simp)`. Establish `hstab0 : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i)) ≤ R` using `pi_le_resPi A _ hae`. Establish `hK0' : K0 = (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i))).subgroupOf R`.

Rewrite using `[hK0, stabilizer_res, stabilizer_pi]`. Establish `hpi` using `invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i)) A (by simpa [eq_comm] using hae) hcomm`. Establish `hc1 : K0.relIndex KA ≠ 0`. Rewrite using `[hK0', hKA, Subgroup.relIndex_subgroupOf hAR]`. Conclude with `hpi.1`.

Establish `hc2 : KA.relIndex K0 ≠ 0`. Rewrite using `[hK0', hKA, Subgroup.relIndex_subgroupOf hstab0]`. Conclude with `hpi.2.1`. Establish `hDC : ∃ S : Finset R, ∀ g : R, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ`. Use `double_cosets_transfer Γ KA K0 hc1 ?_` and prove the remaining obligations.

Take `⟨S, hSR, hS⟩` from `hdc`. Use `⟨S.subtype (· ∈ R), fun g => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, h, k, hk, hg⟩` from `hS g g.2`. Establish `hkR : k ∈ R` using `hAR (fun i _ => hk i)`. Use `⟨⟨s, hSR s hs⟩, by simpa using hs, φ' h, ⟨h, rfl⟩, ⟨k, hkR⟩, ?_, ?_⟩` and prove the remaining obligations.

Simplify `hk` using `[hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi]`. Use `ext1`. Simplify `hg` using `[hφ']`. Establish `hFin : ∀ a : R, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite`. Use `finite_conj_transfer Γ KA K0 hc2 (fun a => ?_)` and prove the remaining obligations.

Use `((hfin a a.2).image φ').subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨⟨h, rfl⟩, hγ⟩`. Use `⟨h, fun i => ?_, rfl⟩` and prove the remaining obligations. Use `hγ` as an intermediate fact. Simplify using `only [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi, Set.mem_univ, forall_const] at this`.

Simplify `this i` using `[hφ']`. Take `⟨V0, hV0, hmass⟩` from `GlobalTheory.T.orbit_mass_eq_of_finite_double_cosets Γ K0 hDC hFin`. Use `⟨V0, hV0, fun x hx hxae => ?_⟩` and prove the remaining obligations. Establish `hAx : {i | A i ≠ MulAction.stabilizer (G i) (x i)}.Finite`. Use `(hae.union hxae).subset (fun i hi => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h`. Conclude with `hi (by rw [h.1, h.2])`. Establish `hstabx : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) ≤ R` using `pi_le_resPi A _ hAx`. Establish `hSx : MulAction.stabilizer R x = (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i))).subgroupOf R`.

Rewrite using `[stabilizer_res, stabilizer_pi]`. Establish `hpx` using `invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i)) (fun i => MulAction.stabilizer (G i) (x i)) (hxae.subset (fun i hi h => hi (by rw [h]))) hx`. Establish `d1 : K0.relIndex (MulAction.stabilizer R x) ≠ 0`. Rewrite using `[hK0', hSx, Subgroup.relIndex_subgroupOf hstabx]`. Conclude with `hpx.1`.

Establish `d2 : (MulAction.stabilizer R x).relIndex K0 ≠ 0`. Rewrite using `[hK0', hSx, Subgroup.relIndex_subgroupOf hstab0]`. Conclude with `hpx.2.1`. Establish `hm` using `hmass (∀ i, X i) x d1 d2`. Establish `hvol : invVol K0 (MulAction.stabilizer R x) = ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))`.

Rewrite using `[hK0', hSx, invVol_subgroupOf R _ _ hstab0 hstabx]`. Conclude with `hpx.2.2`. Rewrite using `[← hvol, ← hm]`. Establish `hφinj : Function.Injective φ'` using `fun a b hab => hinj (congrArg Subtype.val hab)`. Establish `horb : ∀ y : ∀ i, X i, ((∀ i, ∃ g : G i, g • x i = y i) ∧ {i | y i ≠ x i}.Finite) ↔ y ∈ MulAction.orbit R x`.

Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hall, hf⟩`. Set `g : ∀ i, G i` to `fun i => if y i = x i then 1 else Classical.choose (hall i)`. Establish `hgR : g ∈ R`.

Use `hf.subset (fun i hi hyx => hi ?_)` and prove the remaining obligations. Simplify using `only [g, hyx, if_true]`. Conclude with `one_mem _`. Use `⟨⟨g, hgR⟩, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[Subgroup.smul_def, Pi.smul_apply']`. Distinguish the cases in `hyx : y i = x i`. Simplify using `[g, hyx]`. Simplify using `only [g, hyx, if_false]`. Conclude with `Classical.choose_spec (hall i)`.

Introduce and unpack `⟨g, rfl⟩`. Use `⟨fun i => ⟨(g : ∀ i, G i) i, by dsimp only; rw [Subgroup.smul_def, Pi.smul_apply']⟩, ?_⟩` and prove the remaining obligations. Use `((g.2 : {i | (g : ∀ i, G i) i ∉ A i}.Finite).union hAx).subset (fun i hi => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h`.

Apply `hi` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Subgroup.smul_def, Pi.smul_apply']`. Use `h.1` as an intermediate fact. Rewrite `this` using `[h.2]`.

Conclude with `this`. Establish `henc : ∀ y : ∀ i, X i, {h : H | φ h • y = y}.encard = ((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard`. Introduce `y`. Rewrite using `[← hφinj.encard_image]`. Use `congr 1`.

Use extensionality with `γ`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, rfl⟩`. Conclude with `⟨⟨h, rfl⟩, by rw [Subgroup.smul_def]; exact hh⟩`.

Introduce and unpack `⟨⟨h, rfl⟩, hh⟩`. Conclude with `⟨h, by rw [Subgroup.smul_def] at hh; exact hh, rfl⟩`. Use `(tsum_congr fun o => ?_).trans (tsum_quot_out _ (MulAction.orbitRel Γ (∀ i, X i)) ?_ (fun y => if y ∈ MulAction.orbit R x then ((((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard : ℝ≥0∞))⁻¹ else 0))` and prove the remaining obligations. Use `beta_reduce`. Simplify using `only [henc, horb]`.

Introduce `a b`. Rewrite using `[MulAction.orbitRel_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`. Use `⟨⟨φ' h, h, rfl⟩⁻¹, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Simplify using `[Subgroup.smul_def, hφ']`. Introduce and unpack `⟨⟨γ, h, rfl⟩, hγ⟩`. Use `⟨h⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[← hγ]`.

Simplify using `only`. Simplify using `[Subgroup.smul_def, hφ']`.
-/
theorem mass_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  intro ι G _ X _ A H _ φ hinj hres hdc hfin x0 hcomm hae
  set R := resPi A with hRdef
  let φ' : H →* R := φ.codRestrict R hres
  have hφ' : ∀ h, ((φ' h : R) : ∀ i, G i) = φ h := fun h => rfl
  set Γ : Subgroup R := φ'.range with hΓ
  set KA : Subgroup R := (Subgroup.pi Set.univ A).subgroupOf R with hKA
  set K0 : Subgroup R := MulAction.stabilizer R x0 with hK0
  have hAR : Subgroup.pi Set.univ A ≤ R := pi_le_resPi A A (by simp)
  have hstab0 : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i)) ≤ R :=
    pi_le_resPi A _ hae
  have hK0' : K0 = (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i))).subgroupOf R := by
    rw [hK0, stabilizer_res, stabilizer_pi]
  have hpi := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i)) A
    (by simpa [eq_comm] using hae) hcomm
  have hc1 : K0.relIndex KA ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hAR]; exact hpi.1
  have hc2 : KA.relIndex K0 ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hstab0]; exact hpi.2.1
  have hDC : ∃ S : Finset R, ∀ g : R, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
    refine double_cosets_transfer Γ KA K0 hc1 ?_
    obtain ⟨S, hSR, hS⟩ := hdc
    refine ⟨S.subtype (· ∈ R), fun g => ?_⟩
    obtain ⟨s, hs, h, k, hk, hg⟩ := hS g g.2
    have hkR : k ∈ R := hAR (fun i _ => hk i)
    refine ⟨⟨s, hSR s hs⟩, by simpa using hs, φ' h, ⟨h, rfl⟩, ⟨k, hkR⟩, ?_, ?_⟩
    · simpa [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi] using hk
    · ext1; simpa [hφ'] using hg
  have hFin : ∀ a : R, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
    refine finite_conj_transfer Γ KA K0 hc2 (fun a => ?_)
    refine ((hfin a a.2).image φ').subset ?_
    rintro γ ⟨⟨h, rfl⟩, hγ⟩
    refine ⟨h, fun i => ?_, rfl⟩
    have := hγ
    simp only [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi, Set.mem_univ, forall_const] at this
    simpa [hφ'] using this i
  obtain ⟨V0, hV0, hmass⟩ := GlobalTheory.T.orbit_mass_eq_of_finite_double_cosets Γ K0 hDC hFin
  refine ⟨V0, hV0, fun x hx hxae => ?_⟩

  have hAx : {i | A i ≠ MulAction.stabilizer (G i) (x i)}.Finite := by
    refine (hae.union hxae).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (by rw [h.1, h.2])
  have hstabx : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) ≤ R :=
    pi_le_resPi A _ hAx
  have hSx : MulAction.stabilizer R x =
      (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i))).subgroupOf R := by
    rw [stabilizer_res, stabilizer_pi]
  have hpx := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i))
    (fun i => MulAction.stabilizer (G i) (x i))
    (hxae.subset (fun i hi h => hi (by rw [h]))) hx
  have d1 : K0.relIndex (MulAction.stabilizer R x) ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstabx]; exact hpx.1
  have d2 : (MulAction.stabilizer R x).relIndex K0 ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstab0]; exact hpx.2.1
  have hm := hmass (∀ i, X i) x d1 d2
  have hvol : invVol K0 (MulAction.stabilizer R x) =
      ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i)) := by
    rw [hK0', hSx, invVol_subgroupOf R _ _ hstab0 hstabx]; exact hpx.2.2
  rw [← hvol, ← hm]
  have hφinj : Function.Injective φ' := fun a b hab => hinj (congrArg Subtype.val hab)
  have horb : ∀ y : ∀ i, X i, ((∀ i, ∃ g : G i, g • x i = y i) ∧ {i | y i ≠ x i}.Finite) ↔
      y ∈ MulAction.orbit R x := by
    intro y
    constructor
    · rintro ⟨hall, hf⟩
      let g : ∀ i, G i := fun i => if y i = x i then 1 else Classical.choose (hall i)
      have hgR : g ∈ R := by
        refine hf.subset (fun i hi hyx => hi ?_)
        simp only [g, hyx, if_true]
        exact one_mem _
      refine ⟨⟨g, hgR⟩, funext fun i => ?_⟩
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      by_cases hyx : y i = x i
      · simp [g, hyx]
      · simp only [g, hyx, if_false]
        exact Classical.choose_spec (hall i)
    · rintro ⟨g, rfl⟩
      refine ⟨fun i => ⟨(g : ∀ i, G i) i, by dsimp only; rw [Subgroup.smul_def, Pi.smul_apply']⟩, ?_⟩
      refine ((g.2 : {i | (g : ∀ i, G i) i ∉ A i}.Finite).union hAx).subset (fun i hi => ?_)
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
      apply hi
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      have := h.1
      rw [h.2] at this
      exact this
  have henc : ∀ y : ∀ i, X i, {h : H | φ h • y = y}.encard =
      ((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard := by
    intro y
    rw [← hφinj.encard_image]
    congr 1
    ext γ
    simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, by rw [Subgroup.smul_def]; exact hh⟩
    · rintro ⟨⟨h, rfl⟩, hh⟩
      exact ⟨h, by rw [Subgroup.smul_def] at hh; exact hh, rfl⟩
  refine (tsum_congr fun o => ?_).trans (tsum_quot_out _ (MulAction.orbitRel Γ (∀ i, X i)) ?_ (fun y =>
    if y ∈ MulAction.orbit R x then
      ((((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard : ℝ≥0∞))⁻¹ else 0))
  · beta_reduce
    simp only [henc, horb]
  · intro a b
    rw [MulAction.orbitRel_apply]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨φ' h, h, rfl⟩⁻¹, ?_⟩
      dsimp only
      simp [Subgroup.smul_def, hφ']
    · rintro ⟨⟨γ, h, rfl⟩, hγ⟩
      refine ⟨h⁻¹, ?_⟩
      rw [← hγ]
      dsimp only
      simp [Subgroup.smul_def, hφ']

end GlobalTheory.HL
