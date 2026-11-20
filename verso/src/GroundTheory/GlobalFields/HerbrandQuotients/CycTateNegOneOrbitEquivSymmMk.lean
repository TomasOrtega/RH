import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
import GroundTheory.GlobalFields.HerbrandQuotients.CycTate

namespace GroundTheory.Global

open GroundTheory.GroupCoh

section Orbit

variable {k G X : Type*} [CommRing k] [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)] [∀ x, Module k (M x)]

def PermutesFactors (ρ : Representation k G (∀ x, M x)) : Prop :=
  ∀ (g : G) (f : ∀ x, M x) (x : X), f x = 0 → ρ g f (g • x) = 0

/- English proof (translation)
Use `hρ g (f - f') x (by rw [Pi.sub_apply, h, sub_self])` as an intermediate fact. Rewrite `this` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem PermutesFactors.apply_eq {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ)
    (g : G) {f f' : ∀ x, M x} {x : X} (h : f x = f' x) : ρ g f (g • x) = ρ g f' (g • x) := by
  have := hρ g (f - f') x (by rw [Pi.sub_apply, h, sub_self])
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at this

/- English proof (translation)
Rewrite using `[← smul_inv_smul g y]`. Use `hρ g _ _ (Pi.single_eq_of_ne ?_ a)` and prove the remaining obligations. Introduce `h`. Conclude with `hy (by rw [← h, smul_inv_smul])`.
-/
theorem PermutesFactors.apply_single_of_ne [DecidableEq X] {ρ : Representation k G (∀ x, M x)}
    (hρ : PermutesFactors ρ) (g : G) (x : X) (a : M x) {y : X} (hy : y ≠ g • x) :
    ρ g (Pi.single x a) y = 0 := by
  rw [← smul_inv_smul g y]
  refine hρ g _ _ (Pi.single_eq_of_ne ?_ a)
  intro h
  exact hy (by rw [← h, smul_inv_smul])

/- English proof (translation)
Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z = g • x₀`. Substitute `hz` using the available equality. Rewrite using `[Pi.single_eq_same, hρ.apply_eq g (f' := ρ g⁻¹ f) (Pi.single_eq_same _ _), Representation.self_inv_apply]`. Rewrite using `[Pi.single_eq_of_ne hz, hρ.apply_single_of_ne _ _ _ hz]`.
-/
theorem PermutesFactors.single_eq [DecidableEq X] {ρ : Representation k G (∀ x, M x)}
    (hρ : PermutesFactors ρ) (x₀ : X) (g : G) (f : ∀ x, M x) :
    Pi.single (g • x₀) (f (g • x₀)) = ρ g (Pi.single x₀ (ρ g⁻¹ f x₀)) := by
  funext z
  by_cases hz : z = g • x₀
  · subst hz
    rw [Pi.single_eq_same, hρ.apply_eq g (f' := ρ g⁻¹ f) (Pi.single_eq_same _ _),
      Representation.self_inv_apply]
  · rw [Pi.single_eq_of_ne hz, hρ.apply_single_of_ne _ _ _ hz]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq G x₀ y`. Rewrite using `[← hf g, Pi.zero_apply]`. Conclude with `hρ g f x₀ h0`.
-/
theorem PermutesFactors.eq_zero_of_invariant [MulAction.IsPretransitive G X]
    {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {f : ∀ x, M x}
    (hf : ∀ g, ρ g f = f) (x₀ : X) (h0 : f x₀ = 0) : f = 0 := by
  funext y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ y
  rw [← hf g, Pi.zero_apply]
  exact hρ g f x₀ h0

variable [MulAction.IsPretransitive G X]

variable (G) in

noncomputable def orbitRep (x₀ y : X) : G :=
  (MulAction.exists_smul_eq G x₀ y).choose

/- English proof (translation)
The claim follows from `(MulAction.exists_smul_eq G x₀ y).choose_spec`.
-/
theorem orbitRep_smul (x₀ y : X) : orbitRep G x₀ y • x₀ = y :=
  (MulAction.exists_smul_eq G x₀ y).choose_spec

variable (G) in

/- English proof (translation)
The claim follows from `Finite.of_surjective (fun g : G => g • x₀) fun y => MulAction.exists_smul_eq G x₀ y`.
-/
theorem finite_of_isPretransitive [Finite G] (x₀ : X) : Finite X :=
  Finite.of_surjective (fun g : G => g • x₀) fun y => MulAction.exists_smul_eq G x₀ y

noncomputable def stabProdEquiv (x₀ : X) (D : Subgroup G) (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) :
    D × X ≃ G where
  toFun p := (p.1 : G) * (orbitRep G x₀ p.2)⁻¹
  invFun g := (⟨g * orbitRep G x₀ (g⁻¹ • x₀), (hD _).2 (by
    rw [mul_smul, orbitRep_smul, smul_inv_smul])⟩, g⁻¹ • x₀)
  left_inv p := by
    obtain ⟨d, y⟩ := p
    have hd : (d : G)⁻¹ • x₀ = x₀ := (hD _).1 (inv_mem d.2)
    have hy : ((d : G) * (orbitRep G x₀ y)⁻¹)⁻¹ • x₀ = y := by
      rw [mul_inv_rev, inv_inv, mul_smul, hd, orbitRep_smul]
    refine Prod.ext (Subtype.ext ?_) hy
    show (d : G) * (orbitRep G x₀ y)⁻¹ * orbitRep G x₀ (((d : G) * (orbitRep G x₀ y)⁻¹)⁻¹ • x₀) = d
    rw [hy, inv_mul_cancel_right]
  right_inv g := mul_inv_cancel_right g _

noncomputable def orbitCores [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X) :
    (∀ x, M x) →+ M x₀ where
  toFun f := ∑ y, ρ (orbitRep G x₀ y)⁻¹ f x₀
  map_zero' := by simp
  map_add' f f' := by simp [Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orbitCores_apply [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X)
    (f : ∀ x, M x) : orbitCores ρ x₀ f = ∑ y, ρ (orbitRep G x₀ y)⁻¹ f x₀ :=
  rfl

/- English proof (translation)
Rewrite using `[cycNorm_apply, cycNorm_apply, Finset.sum_apply, orbitCores_apply]`. Rewrite using `[show (∑ g : G, ρ g f x₀) = ∑ p : D × X, ρ ((p.1 : G) * (orbitRep G x₀ p.2)⁻¹) f x₀ from (Fintype.sum_equiv (stabProdEquiv x₀ D hD) (fun p => ρ ((p.1 : G) * (orbitRep G x₀ p.2)⁻¹) f x₀) (fun g => ρ g f x₀) fun p => rfl).symm]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply, hρ₀]`.
-/
theorem cycNorm_apply_base [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (f : ∀ x, M x) :
    cycNorm ρ f x₀ = cycNorm ρ₀ (orbitCores ρ x₀ f) := by
  rw [cycNorm_apply, cycNorm_apply, Finset.sum_apply, orbitCores_apply]
  rw [show (∑ g : G, ρ g f x₀) = ∑ p : D × X, ρ ((p.1 : G) * (orbitRep G x₀ p.2)⁻¹) f x₀ from
    (Fintype.sum_equiv (stabProdEquiv x₀ D hD)
      (fun p => ρ ((p.1 : G) * (orbitRep G x₀ p.2)⁻¹) f x₀) (fun g => ρ g f x₀) fun p => rfl).symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, Module.End.mul_apply, hρ₀]

omit [MulAction.IsPretransitive G X] in
/- English proof (translation)
Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y = x₀`. Substitute `hy` using the available equality. Rewrite using `[hρ₀, Pi.single_eq_same, Pi.single_eq_same]`. Rewrite using `[Pi.single_eq_of_ne hy, hρ.apply_single_of_ne]`.

Rewrite using `[(hD d).1 d.2]`. Conclude with `hy`.
-/
theorem apply_single_base [DecidableEq X] {ρ : Representation k G (∀ x, M x)}
    (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (d : D) (b : M x₀) : ρ d (Pi.single x₀ b) = Pi.single x₀ (ρ₀ d b) := by
  funext y
  by_cases hy : y = x₀
  · subst hy
    rw [hρ₀, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hy, hρ.apply_single_of_ne]
    rw [(hD d).1 d.2]
    exact hy

omit [MulAction.IsPretransitive G X] in
/- English proof (translation)
Establish `hm : g'⁻¹ * g ∈ D` using `(hD _).2 (by rw [mul_smul, h, inv_smul_smul])`. Establish `hg : g = g' * ((⟨g'⁻¹ * g, hm⟩ : D) : G)` using `by simp`. Rewrite using `[hg, map_mul, Module.End.mul_apply, apply_single_base hρ hD hρ₀, hb]`.
-/
theorem apply_single_eq_of_smul_eq [DecidableEq X] {ρ : Representation k G (∀ x, M x)}
    (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    {b : M x₀} (hb : ∀ d : D, ρ₀ d b = b) {g g' : G} (h : g • x₀ = g' • x₀) :
    ρ g (Pi.single x₀ b) = ρ g' (Pi.single x₀ b) := by
  have hm : g'⁻¹ * g ∈ D := (hD _).2 (by rw [mul_smul, h, inv_smul_smul])
  have hg : g = g' * ((⟨g'⁻¹ * g, hm⟩ : D) : G) := by simp
  rw [hg, map_mul, Module.End.mul_apply, apply_single_base hρ hD hρ₀, hb]

/- English proof (translation)
Rewrite using `[orbitCores_apply, Finset.sum_eq_single x₀]`. Conclude with `(hρ₀ ⟨_, (hD _).2 (by rw [inv_smul_eq_iff, orbitRep_smul])⟩ _).trans (by rw [Pi.single_eq_same])`. Introduce `y _ hy`. Apply `hρ.apply_single_of_ne` to reduce the goal to its premises. Introduce `h`.

Rewrite `h` using `[eq_inv_smul_iff, orbitRep_smul]`. Conclude with `hy h`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem orbitCores_single [Fintype X] [DecidableEq X] {ρ : Representation k G (∀ x, M x)}
    (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (b : M x₀) :
    orbitCores ρ x₀ (Pi.single x₀ b) =
      ρ₀ ⟨(orbitRep G x₀ x₀)⁻¹, (hD _).2 (by rw [inv_smul_eq_iff, orbitRep_smul])⟩ b := by
  rw [orbitCores_apply, Finset.sum_eq_single x₀]
  · exact (hρ₀ ⟨_, (hD _).2 (by rw [inv_smul_eq_iff, orbitRep_smul])⟩ _).trans
      (by rw [Pi.single_eq_same])
  · intro y _ hy
    apply hρ.apply_single_of_ne
    intro h
    rw [eq_inv_smul_iff, orbitRep_smul] at h
    exact hy h
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hmem : ∀ y, (orbitRep G x₀ y)⁻¹ * g * orbitRep G x₀ (g⁻¹ • y) ∈ D` using `fun y => (hD _).2 (by rw [mul_smul, mul_smul, orbitRep_smul, smul_inv_smul, inv_smul_eq_iff, orbitRep_smul])`. Establish `hterm : ∀ y, ρ (orbitRep G x₀ y)⁻¹ (ρ g h) x₀ = ρ₀ ⟨_, hmem y⟩ (ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀)`. Introduce `y`. Rewrite using `[← hρ₀ ⟨_, hmem y⟩, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using `[mul_assoc]`.

Establish `e1 : orbitCores ρ x₀ (ρ g h) = ∑ y, ρ₀ ⟨_, hmem y⟩ (ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀)` using `Finset.sum_congr rfl fun y _ => hterm y`. Establish `e2 : orbitCores ρ x₀ h = ∑ y, ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀` using `(Fintype.sum_equiv (MulAction.toPerm g⁻¹) (fun y => ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀) (fun y => ρ (orbitRep G x₀ y)⁻¹ h x₀) fun y => rfl).symm`. Rewrite using `[e1, e2, ← Finset.sum_sub_distrib]`. Conclude with `sum_mem fun y _ => apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _`.
-/
theorem orbitCores_apply_sub_mem [Fintype X] {ρ : Representation k G (∀ x, M x)} {x₀ : X}
    {D : Subgroup G} [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) {ρ₀ : Representation k D (M x₀)}
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) {τ : D}
    (hτ : ∀ d, d ∈ Subgroup.zpowers τ) (g : G) (h : ∀ x, M x) :
    orbitCores ρ x₀ (ρ g h) - orbitCores ρ x₀ h ∈ (cycSubOne ρ₀ τ).range := by
  have hmem : ∀ y, (orbitRep G x₀ y)⁻¹ * g * orbitRep G x₀ (g⁻¹ • y) ∈ D := fun y =>
    (hD _).2 (by rw [mul_smul, mul_smul, orbitRep_smul, smul_inv_smul, inv_smul_eq_iff,
      orbitRep_smul])
  have hterm : ∀ y, ρ (orbitRep G x₀ y)⁻¹ (ρ g h) x₀ =
      ρ₀ ⟨_, hmem y⟩ (ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀) := by
    intro y
    rw [← hρ₀ ⟨_, hmem y⟩, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  have e1 : orbitCores ρ x₀ (ρ g h) =
      ∑ y, ρ₀ ⟨_, hmem y⟩ (ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀) :=
    Finset.sum_congr rfl fun y _ => hterm y
  have e2 : orbitCores ρ x₀ h = ∑ y, ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀ :=
    (Fintype.sum_equiv (MulAction.toPerm g⁻¹) (fun y => ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀)
      (fun y => ρ (orbitRep G x₀ y)⁻¹ h x₀) fun y => rfl).symm
  rw [e1, e2, ← Finset.sum_sub_distrib]
  exact sum_mem fun y _ => apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _

omit [MulAction G X] [MulAction.IsPretransitive G X] in
/- English proof (translation)
Rewrite using `[AddMonoidHom.mem_ker, cycSubOne_apply, ← hρ₀, (mem_ker_cycSubOne_iff ρ hσ _).1 f.2 τ, sub_self]`.
-/
theorem base_mem_ker_cycSubOne {ρ : Representation k G (∀ x, M x)} {x₀ : X} {D : Subgroup G}
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (f : (cycSubOne ρ σ).ker) :
    (f : ∀ x, M x) x₀ ∈ (cycSubOne ρ₀ τ).ker := by
  rw [AddMonoidHom.mem_ker, cycSubOne_apply, ← hρ₀,
    (mem_ker_cycSubOne_iff ρ hσ _).1 f.2 τ, sub_self]

noncomputable def orbitZeroMap (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G)
    [Fintype D] (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) :
    (cycSubOne ρ σ).ker →+ CycTateZero ρ₀ τ :=
  (QuotientAddGroup.mk' _).comp
    (((Pi.evalAddMonoidHom M x₀).comp (cycSubOne ρ σ).ker.subtype).codRestrict _
      (base_mem_ker_cycSubOne hρ₀ hσ τ))

omit [MulAction G X] [MulAction.IsPretransitive G X] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orbitZeroMap_apply (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G)
    [Fintype D] (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (f : (cycSubOne ρ σ).ker) :
    orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ f =
      QuotientAddGroup.mk ⟨(f : ∀ x, M x) x₀, base_mem_ker_cycSubOne hρ₀ hσ τ f⟩ :=
  rfl

/- English proof (translation)
Use `finite_of_isPretransitive G x₀` as an intermediate fact. Use `Fintype.ofFinite X` as an intermediate fact. Introduce `c`. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H b`.

Take `⟨b, hb⟩` from `b`. Establish `hbD : ∀ d : D, ρ₀ d b = b`. Rewrite `hb` using `[AddMonoidHom.mem_ker, cycSubOne_apply, sub_eq_zero]`. Conclude with `apply_eq_self_of_generator ρ₀ hτ hb`. Set `F : ∀ x, M x` to `∑ y, ρ (orbitRep G x₀ y) (Pi.single x₀ b)`.

Establish `hF : ∀ g, ρ g F = F`. Introduce `g`. Rewrite using `[map_sum]`. Use `(Finset.sum_congr rfl fun y _ => ?_).trans (Fintype.sum_equiv (MulAction.toPerm g) (fun y => ρ (orbitRep G x₀ (g • y)) (Pi.single x₀ b)) (fun y => ρ (orbitRep G x₀ y) (Pi.single x₀ b)) fun y => rfl)` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Conclude with `apply_single_eq_of_smul_eq hρ hD hρ₀ hbD (by rw [mul_smul, orbitRep_smul, orbitRep_smul])`. Establish `hF0 : F x₀ = b`. Simplify using `only [F, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_single x₀]`. Establish `hm : orbitRep G x₀ x₀ ∈ D` using `(hD _).2 (orbitRep_smul x₀ x₀)`.

Conclude with `(hρ₀ ⟨_, hm⟩ _).trans (by rw [Pi.single_eq_same, hbD])`. Introduce `y _ hy`. Apply `hρ.apply_single_of_ne` to reduce the goal to its premises. Rewrite using `[orbitRep_smul]`. Conclude with `Ne.symm hy`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `⟨⟨F, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.mem_ker, cycSubOne_apply, hF, sub_self]`. Rewrite using `[orbitZeroMap_apply]`.

Conclude with `congrArg QuotientAddGroup.mk (Subtype.ext hF0)`.
-/
theorem orbitZeroMap_surjective [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    Function.Surjective (orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ) := by
  classical
  have := finite_of_isPretransitive G x₀
  have := Fintype.ofFinite X
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H b =>
  obtain ⟨b, hb⟩ := b
  have hbD : ∀ d : D, ρ₀ d b = b := by
    rw [AddMonoidHom.mem_ker, cycSubOne_apply, sub_eq_zero] at hb
    exact apply_eq_self_of_generator ρ₀ hτ hb
  let F : ∀ x, M x := ∑ y, ρ (orbitRep G x₀ y) (Pi.single x₀ b)
  have hF : ∀ g, ρ g F = F := by
    intro g
    rw [map_sum]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans (Fintype.sum_equiv (MulAction.toPerm g)
      (fun y => ρ (orbitRep G x₀ (g • y)) (Pi.single x₀ b))
      (fun y => ρ (orbitRep G x₀ y) (Pi.single x₀ b)) fun y => rfl)
    rw [← Module.End.mul_apply, ← map_mul]
    exact apply_single_eq_of_smul_eq hρ hD hρ₀ hbD
      (by rw [mul_smul, orbitRep_smul, orbitRep_smul])
  have hF0 : F x₀ = b := by
    simp only [F, Finset.sum_apply]
    rw [Finset.sum_eq_single x₀]
    · have hm : orbitRep G x₀ x₀ ∈ D := (hD _).2 (orbitRep_smul x₀ x₀)
      exact (hρ₀ ⟨_, hm⟩ _).trans (by rw [Pi.single_eq_same, hbD])
    · intro y _ hy
      apply hρ.apply_single_of_ne
      rw [orbitRep_smul]
      exact Ne.symm hy
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨⟨F, ?_⟩, ?_⟩
  · rw [AddMonoidHom.mem_ker, cycSubOne_apply, hF, sub_self]
  · rw [orbitZeroMap_apply]
    exact congrArg QuotientAddGroup.mk (Subtype.ext hF0)

/- English proof (translation)
Use `finite_of_isPretransitive G x₀` as an intermediate fact. Use `Fintype.ofFinite X` as an intermediate fact. Establish `hf : ∀ g, ρ g f = f` using `(mem_ker_cycSubOne_iff ρ hσ _).1 f.2`. Rewrite using `[orbitZeroMap_apply, KerModRange.mk_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, hb⟩`. Use `⟨Pi.single x₀ b, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ g, ρ g (cycNorm ρ (Pi.single x₀ b)) = cycNorm ρ (Pi.single x₀ b)` using `fun g => ρ.self_norm_apply g _`. Establish `h2 : cycNorm ρ (Pi.single x₀ b) x₀ = (f : ∀ x, M x) x₀`. Rewrite using `[cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, orbitCores_single hρ hD hρ₀]`.

Conclude with `(ρ₀.norm_self_apply _ b).trans hb`. Use `hρ.eq_zero_of_invariant (f := cycNorm ρ (Pi.single x₀ b) - f) (fun g => by rw [map_sub, h1, hf]) x₀ (by rw [Pi.sub_apply, h2, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Introduce and unpack `⟨h, hh⟩`. Use `⟨orbitCores ρ x₀ h, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, hh]`.
-/
theorem orbitZeroMap_eq_zero_iff [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (f : (cycSubOne ρ σ).ker) :
    orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ f = 0 ↔ (f : ∀ x, M x) ∈ (cycNorm ρ).range := by
  classical
  have := finite_of_isPretransitive G x₀
  have := Fintype.ofFinite X
  have hf : ∀ g, ρ g f = f := (mem_ker_cycSubOne_iff ρ hσ _).1 f.2
  rw [orbitZeroMap_apply, KerModRange.mk_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Pi.single x₀ b, ?_⟩
    have h1 : ∀ g, ρ g (cycNorm ρ (Pi.single x₀ b)) = cycNorm ρ (Pi.single x₀ b) :=
      fun g => ρ.self_norm_apply g _
    have h2 : cycNorm ρ (Pi.single x₀ b) x₀ = (f : ∀ x, M x) x₀ := by
      rw [cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, orbitCores_single hρ hD hρ₀]
      exact (ρ₀.norm_self_apply _ b).trans hb
    have := hρ.eq_zero_of_invariant (f := cycNorm ρ (Pi.single x₀ b) - f)
      (fun g => by rw [map_sub, h1, hf]) x₀ (by rw [Pi.sub_apply, h2, sub_self])
    exact sub_eq_zero.1 this
  · rintro ⟨h, hh⟩
    refine ⟨orbitCores ρ x₀ h, ?_⟩
    rw [← cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, hh]

noncomputable def cycTateZeroOrbitEquiv [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateZero ρ σ ≃+ CycTateZero ρ₀ τ :=
  kerModRangeEquivOfSurjective (orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ)
    (orbitZeroMap_surjective ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ)
    (orbitZeroMap_eq_zero_iff ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cycTateZeroOrbitEquiv_mk [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (f : (cycSubOne ρ σ).ker) :
    cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨(f : ∀ x, M x) x₀, base_mem_ker_cycSubOne hρ₀ hσ τ f⟩ :=
  rfl

/- English proof (translation)
Rewrite using `[AddMonoidHom.mem_ker, ← cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, AddMonoidHom.mem_ker.1 f.2, Pi.zero_apply]`.
-/
theorem orbitCores_mem_ker_cycNorm [Fintype G] [Fintype X] {ρ : Representation k G (∀ x, M x)}
    {x₀ : X} {D : Subgroup G} [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (f : (cycNorm ρ).ker) : orbitCores ρ x₀ f ∈ (cycNorm ρ₀).ker := by
  rw [AddMonoidHom.mem_ker, ← cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, AddMonoidHom.mem_ker.1 f.2,
    Pi.zero_apply]

noncomputable def orbitNegOneMap [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x))
    (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    (ρ₀ : Representation k D (M x₀)) (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (τ : D) : (cycNorm ρ).ker →+ CycTateNegOne ρ₀ τ :=
  (QuotientAddGroup.mk' _).comp
    (((orbitCores ρ x₀).comp (cycNorm ρ).ker.subtype).codRestrict _
      (orbitCores_mem_ker_cycNorm hD hρ₀))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orbitNegOneMap_apply [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x))
    (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    (ρ₀ : Representation k D (M x₀)) (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (τ : D) (f : (cycNorm ρ).ker) :
    orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ f =
      QuotientAddGroup.mk ⟨orbitCores ρ x₀ f, orbitCores_mem_ker_cycNorm hD hρ₀ f⟩ :=
  rfl

/- English proof (translation)
Use `finite_of_isPretransitive G x₀` as an intermediate fact. Use `Fintype.ofFinite X` as an intermediate fact. Rewrite using `[AddMonoidHom.mem_ker]`. Use `hρ.eq_zero_of_invariant (fun g => ρ.self_norm_apply g _) x₀ ?_` and prove the remaining obligations. Rewrite using `[cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, orbitCores_single hρ hD hρ₀]`.

Conclude with `(ρ₀.norm_self_apply _ b).trans (AddMonoidHom.mem_ker.1 hb)`.
-/
theorem single_mem_ker_cycNorm [Fintype G] [DecidableEq X] {ρ : Representation k G (∀ x, M x)}
    (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) {ρ₀ : Representation k D (M x₀)}
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) {b : M x₀}
    (hb : b ∈ (cycNorm ρ₀).ker) : Pi.single x₀ b ∈ (cycNorm ρ).ker := by
  have := finite_of_isPretransitive G x₀
  have := Fintype.ofFinite X
  rw [AddMonoidHom.mem_ker]
  refine hρ.eq_zero_of_invariant (fun g => ρ.self_norm_apply g _) x₀ ?_
  rw [cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, orbitCores_single hρ hD hρ₀]
  exact (ρ₀.norm_self_apply _ b).trans (AddMonoidHom.mem_ker.1 hb)

/- English proof (translation)
Introduce `c`. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H b`. Take `⟨b, hb⟩` from `b`. Use `⟨⟨_, single_mem_ker_cycNorm hρ hD hρ₀ hb⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]`. Use `show orbitCores ρ x₀ (Pi.single x₀ b) - b ∈ _`. Rewrite using `[orbitCores_single hρ hD hρ₀]`. Conclude with `apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _`.
-/
theorem orbitNegOneMap_surjective [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (τ : D)
    (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    Function.Surjective (orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ) := by
  classical
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H b =>
  obtain ⟨b, hb⟩ := b
  refine ⟨⟨_, single_mem_ker_cycNorm hρ hD hρ₀ hb⟩, ?_⟩
  rw [orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]
  show orbitCores ρ x₀ (Pi.single x₀ b) - b ∈ _
  rw [orbitCores_single hρ hD hρ₀]
  exact apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _

/- English proof (translation)
Rewrite using `[orbitNegOneMap_apply, KerModRange.mk_eq_zero_iff]`. Use `show orbitCores ρ x₀ f ∈ _ ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `e1 : (f : ∀ x, M x) = ∑ y, ρ (orbitRep G x₀ y) (Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀))` using `by conv_lhs => rw [← Finset.univ_sum_single (f : ∀ x, M x)]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Use `hρ.single_eq x₀ (orbitRep G x₀ y) f` as an intermediate fact. Rewrite `this` using `[orbitRep_smul]`. Then use the resulting hypothesis. Establish `e2 : Pi.single x₀ (orbitCores ρ x₀ f) = ∑ y, Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)` using `map_sum (AddMonoidHom.single M x₀) _ _`. Establish `step1 : (f : ∀ x, M x) - Pi.single x₀ (orbitCores ρ x₀ f) ∈ (cycSubOne ρ σ).range`.

Establish `: (f : ∀ x, M x) - Pi.single x₀ (orbitCores ρ x₀ f) = ∑ y, (ρ (orbitRep G x₀ y) (Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) - Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀))`. Rewrite using `[Finset.sum_sub_distrib, ← e1, ← e2]`. Rewrite using `[this]`. Conclude with `sum_mem fun y _ => apply_sub_self_mem_range_cycSubOne ρ hσ _ _`. Establish `step2 : Pi.single x₀ (orbitCores ρ x₀ f) ∈ (cycSubOne ρ σ).range`.

Rewrite using `[← hc, cycSubOne_apply, Pi.single_sub, ← apply_single_base hρ hD hρ₀ τ]`. Conclude with `apply_sub_self_mem_range_cycSubOne ρ hσ _ _`. Use `add_mem step1 step2` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce and unpack `⟨h, hh⟩`.

Rewrite using `[← hh, cycSubOne_apply, map_sub]`. Conclude with `orbitCores_apply_sub_mem hD hρ₀ hτ σ h`.
-/
theorem orbitNegOneMap_eq_zero_iff [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (f : (cycNorm ρ).ker) :
    orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ f = 0 ↔ (f : ∀ x, M x) ∈ (cycSubOne ρ σ).range := by
  classical
  rw [orbitNegOneMap_apply, KerModRange.mk_eq_zero_iff]
  show orbitCores ρ x₀ f ∈ _ ↔ _
  constructor
  · rintro ⟨c, hc⟩
    have e1 : (f : ∀ x, M x) =
        ∑ y, ρ (orbitRep G x₀ y) (Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) := by
      conv_lhs => rw [← Finset.univ_sum_single (f : ∀ x, M x)]
      refine Finset.sum_congr rfl fun y _ => ?_
      have := hρ.single_eq x₀ (orbitRep G x₀ y) f
      rwa [orbitRep_smul] at this
    have e2 : Pi.single x₀ (orbitCores ρ x₀ f) =
        ∑ y, Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀) :=
      map_sum (AddMonoidHom.single M x₀) _ _
    have step1 : (f : ∀ x, M x) - Pi.single x₀ (orbitCores ρ x₀ f) ∈ (cycSubOne ρ σ).range := by
      have : (f : ∀ x, M x) - Pi.single x₀ (orbitCores ρ x₀ f) =
          ∑ y, (ρ (orbitRep G x₀ y) (Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) -
            Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) := by
        rw [Finset.sum_sub_distrib, ← e1, ← e2]
      rw [this]
      exact sum_mem fun y _ => apply_sub_self_mem_range_cycSubOne ρ hσ _ _
    have step2 : Pi.single x₀ (orbitCores ρ x₀ f) ∈ (cycSubOne ρ σ).range := by
      rw [← hc, cycSubOne_apply, Pi.single_sub, ← apply_single_base hρ hD hρ₀ τ]
      exact apply_sub_self_mem_range_cycSubOne ρ hσ _ _
    have := add_mem step1 step2
    rwa [sub_add_cancel] at this
  · rintro ⟨h, hh⟩
    rw [← hh, cycSubOne_apply, map_sub]
    exact orbitCores_apply_sub_mem hD hρ₀ hτ σ h

noncomputable def cycTateNegOneOrbitEquiv [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateNegOne ρ σ ≃+ CycTateNegOne ρ₀ τ :=
  letI : Finite X := finite_of_isPretransitive G x₀
  letI : Fintype X := Fintype.ofFinite X
  kerModRangeEquivOfSurjective (orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ)
    (orbitNegOneMap_surjective ρ hρ x₀ D hD ρ₀ hρ₀ τ hτ)
    (orbitNegOneMap_eq_zero_iff ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ)

/- English proof (translation)
Rewrite using `[AddEquiv.symm_apply_eq, eq_comm]`. Set `_ : Finite X` to `finite_of_isPretransitive G x₀`. Set `_ : Fintype X` to `Fintype.ofFinite X`. Use `show orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ _ = _`. Rewrite using `[orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]`.

Use `show orbitCores ρ x₀ (Pi.single x₀ (b : M x₀)) - (b : M x₀) ∈ (cycSubOne ρ₀ τ).range`. Rewrite using `[orbitCores_single hρ hD hρ₀]`. Conclude with `apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _`.
-/
theorem cycTateNegOneOrbitEquiv_symm_mk [Fintype G] [DecidableEq X]
    (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (b : (cycNorm ρ₀).ker) :
    (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).symm (QuotientAddGroup.mk b) =
      QuotientAddGroup.mk ⟨Pi.single x₀ (b : M x₀), single_mem_ker_cycNorm hρ hD hρ₀ b.2⟩ := by
  rw [AddEquiv.symm_apply_eq, eq_comm]
  let _ : Finite X := finite_of_isPretransitive G x₀
  let _ : Fintype X := Fintype.ofFinite X
  show orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ _ = _
  rw [orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]
  show orbitCores ρ x₀ (Pi.single x₀ (b : M x₀)) - (b : M x₀) ∈ (cycSubOne ρ₀ τ).range
  rw [orbitCores_single hρ hD hρ₀]
  exact apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _

/- English proof (translation)
Rewrite using `[cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr (cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv, Nat.card_congr (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv]`.
-/
theorem cycHerbrand_orbit [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand ρ σ = cycHerbrand ρ₀ τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq,
    Nat.card_congr (cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv,
    Nat.card_congr (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv]

end Orbit

end GroundTheory.Global
