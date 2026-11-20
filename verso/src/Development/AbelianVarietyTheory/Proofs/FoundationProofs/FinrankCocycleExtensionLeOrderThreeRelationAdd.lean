import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def rightDefect (ρ : G → E →ₗ[ℂ] E) (t : G) : (G → E) →ₗ[ℂ] (G → E) where
  toFun u := fun x => u (x * t) - ρ t (u x)
  map_add' u v := by
    funext x
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rightDefect_apply (ρ : G → E →ₗ[ℂ] E) (t : G) (u : G → E) (x : G) :
    rightDefect ρ t u x = u (x * t) - ρ t (u x) := rfl

/- English proof (translation)
Simplify using `only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu`. Take `⟨ha, hb⟩` from `hu`. Establish `hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v` using `fun g h v => (hρ g h v).symm`. Establish `ha' : ∀ γ ∈ Γ, ∀ x, u (γ * x) = u x + ρ x (u γ - u 1)`. Introduce `γ hγ x`.

Rewrite using `[← ha γ hγ x]`. Normalize the expressions using the abelian group laws. Establish `hs2 : ∀ x, u (x * t ^ 3) = ρ (t ^ 3) (u x)`. Introduce `x`. Rewrite using `[← hst, pow_two, ← mul_assoc, hb, hb, hρc]`.

Establish `p2 : t * t = t ^ 2` using `(pow_two t).symm`. Establish `p3 : t ^ 2 * t = t ^ 3` using `(pow_succ t 2).symm`. Establish `p3' : t * t ^ 2 = t ^ 3` using `(pow_succ' t 2).symm`. Simplify using `only [relThree, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, rightDefect_apply]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show (∀ h ∈ Γ, ∀ g : G, rightDefect ρ t u (h * g) = rightDefect ρ t u g) ∧ ∀ g : G, rightDefect ρ t u (g * t ^ 3) = ρ (t ^ 3) (rightDefect ρ t u g)`. Simplify using `only [rightDefect_apply]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h hh g`. Rewrite using `[mul_assoc, ha' h hh (g * t), ha' h hh g, map_add, hρc]`.

Normalize the expressions using the abelian group laws. Introduce `g`. Establish `e : g * t ^ 3 * t = g * t * t ^ 3`. Rewrite using `[mul_assoc, mul_assoc, (Commute.self_pow t 3).eq]`. Rewrite using `[e, hs2, hs2, map_sub, hρc, hρc, (Commute.self_pow t 3).eq]`.

Introduce `x`. Establish `e1 : x * t * t = x * t ^ 2` using `by rw [mul_assoc, p2]`. Establish `e2 : x * t ^ 2 * t = x * t ^ 3` using `by rw [mul_assoc, p3]`. Rewrite using `[e1, e2, hs2, map_sub, map_sub, hρc, hρc, p3', p2]`. Normalize the expressions using the abelian group laws.
-/
theorem rightDefect_mem_relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hst : s ^ 2 = t ^ 3) (u : G → E)
    (hu : u ∈ extn Γ ρ s) : rightDefect ρ t u ∈ relThree Γ ρ t := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨ha, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have ha' : ∀ γ ∈ Γ, ∀ x, u (γ * x) = u x + ρ x (u γ - u 1) := by
    intro γ hγ x
    rw [← ha γ hγ x]
    abel
  have hs2 : ∀ x, u (x * t ^ 3) = ρ (t ^ 3) (u x) := by
    intro x
    rw [← hst, pow_two, ← mul_assoc, hb, hb, hρc]
  have p2 : t * t = t ^ 2 := (pow_two t).symm
  have p3 : t ^ 2 * t = t ^ 3 := (pow_succ t 2).symm
  have p3' : t * t ^ 2 = t ^ 3 := (pow_succ' t 2).symm
  simp only [relThree, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, rightDefect_apply]
  refine ⟨?_, ?_⟩
  · show (∀ h ∈ Γ, ∀ g : G, rightDefect ρ t u (h * g) = rightDefect ρ t u g) ∧
      ∀ g : G, rightDefect ρ t u (g * t ^ 3) = ρ (t ^ 3) (rightDefect ρ t u g)
    simp only [rightDefect_apply]
    refine ⟨?_, ?_⟩
    · intro h hh g
      rw [mul_assoc, ha' h hh (g * t), ha' h hh g, map_add, hρc]
      abel
    · intro g
      have e : g * t ^ 3 * t = g * t * t ^ 3 := by
        rw [mul_assoc, mul_assoc, (Commute.self_pow t 3).eq]
      rw [e, hs2, hs2, map_sub, hρc, hρc, (Commute.self_pow t 3).eq]
  · intro x
    have e1 : x * t * t = x * t ^ 2 := by rw [mul_assoc, p2]
    have e2 : x * t ^ 2 * t = x * t ^ 3 := by rw [mul_assoc, p3]
    rw [e1, e2, hs2, map_sub, map_sub, hρc, hρc, p3', p2]
    abel

/- English proof (translation)
Simplify using `only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu`. Take `⟨-, hb⟩` from `hu`. Establish `hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v` using `fun g h v => (hρ g h v).symm`. Establish `hw : ∀ x, u (x * t) = ρ t (u x)`. Introduce `x`.

Establish `hx` using `congrFun hΦ x`. Rewrite `hx` using `[rightDefect_apply, Pi.zero_apply, sub_eq_zero]`. Conclude with `hx`. Set `H : Subgroup G` to `{ carrier := {g | ∀ x, u (x * g) = ρ g (u x)} mul_mem' := by`. Introduce `a b ha hb'`.

Simplify using `only [Set.mem_ofPred_eq] at ha hb' ⊢`. Introduce `x`. Rewrite using `[← mul_assoc, hb', ha, hρc]`. Use the proof step `one_mem' := by`. Simplify using `only [Set.mem_ofPred_eq]`.

Introduce `x`. Rewrite using `[mul_one, h1]`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_ofPred_eq] at ha ⊢`.

Introduce `x`. Establish `hx` using `ha (x * a⁻¹)`. Rewrite `hx` using `[inv_mul_cancel_right]`. Rewrite using `[hx, hρc, mul_inv_cancel, h1] }`. Establish `hle : Subgroup.closure ({s, t} : Set G) ≤ H`.

Rewrite using `[Subgroup.closure_le]`. Introduce `g hg`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg`. Break down `hg with rfl | rfl` into its components or cases. Conclude with `hb`.

Conclude with `hw`. Rewrite `hle` using `[hgen]`. Use function extensionality and compare the values at `g`. Establish `hg : g ∈ H` using `hle (Subgroup.mem_top g)`. Establish `h1g` using `(show ∀ x, u (x * g) = ρ g (u x) from hg) 1`.

Rewrite `h1g` using `[one_mul, hu1, map_zero]`. Conclude with `h1g`.
-/
theorem eq_zero_of_rightDefect_eq_zero (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (u : G → E)
    (hu : u ∈ extn Γ ρ s) (hΦ : rightDefect ρ t u = 0) (hu1 : u 1 = 0) : u = 0 := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨-, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have hw : ∀ x, u (x * t) = ρ t (u x) := by
    intro x
    have hx := congrFun hΦ x
    rw [rightDefect_apply, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  let H : Subgroup G :=
    { carrier := {g | ∀ x, u (x * g) = ρ g (u x)}
      mul_mem' := by
        intro a b ha hb'
        simp only [Set.mem_ofPred_eq] at ha hb' ⊢
        intro x
        rw [← mul_assoc, hb', ha, hρc]
      one_mem' := by
        simp only [Set.mem_ofPred_eq]
        intro x
        rw [mul_one, h1]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro x
        have hx := ha (x * a⁻¹)
        rw [inv_mul_cancel_right] at hx
        rw [hx, hρc, mul_inv_cancel, h1] }
  have hle : Subgroup.closure ({s, t} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hb
    · exact hw
  rw [hgen] at hle
  funext g
  have hg : g ∈ H := hle (Subgroup.mem_top g)
  have h1g := (show ∀ x, u (x * g) = ρ g (u x) from hg) 1
  rw [one_mul, hu1, map_zero] at h1g
  exact h1g

/- English proof (translation)
Use `hE` as an intermediate fact. Use `hR` as an intermediate fact. Establish `hmem : ∀ u : extn Γ ρ s, ((rightDefect ρ t).comp (extn Γ ρ s).subtype) u ∈ relThree Γ ρ t` using `fun u => rightDefect_mem_relThree Γ ρ s t hρ hst u.1 u.2`. Set `Φ : extn Γ ρ s →ₗ[ℂ] relThree Γ ρ t × E` to `LinearMap.prod (LinearMap.codRestrict (relThree Γ ρ t) ((rightDefect ρ t).comp (extn Γ ρ s).subtype) hmem) ((LinearMap.proj (R := ℂ) (φ := fun _ : G => E) (1 : G)).comp (extn Γ ρ s).subtype)`. Establish `hinj : Function.Injective Φ`.

Use `(injective_iff_map_eq_zero Φ).2 ?_` and prove the remaining obligations. Introduce `u hu`. Establish `h1'` using `congrArg (fun p : relThree Γ ρ t × E => (p.1 : G → E)) hu`. Establish `h2'` using `congrArg Prod.snd hu`. Conclude with `Subtype.ext (eq_zero_of_rightDefect_eq_zero Γ ρ s t hρ h1 hgen u.1 u.2 h1' h2')`.

Establish `hfin : FiniteDimensional ℂ (extn Γ ρ s)` using `FiniteDimensional.of_injective Φ hinj`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hinj`. Rewrite `hle` using `[Module.finrank_prod]`. Then use the resulting hypothesis.
-/
theorem finrank_extn_le {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v) (hst : s ^ 2 = t ^ 3)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (hE : FiniteDimensional ℂ E)
    (hR : FiniteDimensional ℂ (relThree Γ ρ t)) :
    FiniteDimensional ℂ (extn Γ ρ s) ∧
      Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  have := hE
  have := hR
  have hmem : ∀ u : extn Γ ρ s, ((rightDefect ρ t).comp (extn Γ ρ s).subtype) u ∈ relThree Γ ρ t :=
    fun u => rightDefect_mem_relThree Γ ρ s t hρ hst u.1 u.2
  let Φ : extn Γ ρ s →ₗ[ℂ] relThree Γ ρ t × E :=
    LinearMap.prod (LinearMap.codRestrict (relThree Γ ρ t) ((rightDefect ρ t).comp (extn Γ ρ s).subtype) hmem)
      ((LinearMap.proj (R := ℂ) (φ := fun _ : G => E) (1 : G)).comp (extn Γ ρ s).subtype)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro u hu
    have h1' := congrArg (fun p : relThree Γ ρ t × E => (p.1 : G → E)) hu
    have h2' := congrArg Prod.snd hu
    exact Subtype.ext (eq_zero_of_rightDefect_eq_zero Γ ρ s t hρ h1 hgen u.1 u.2 h1' h2')
  have hfin : FiniteDimensional ℂ (extn Γ ρ s) := FiniteDimensional.of_injective Φ hinj
  refine ⟨hfin, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod] at hle

end GlobalTheory.HeckeFamilyMatrices.CocBound
