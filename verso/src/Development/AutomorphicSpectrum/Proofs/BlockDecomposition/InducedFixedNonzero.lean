import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SmInd

def bump {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G)
    (σ : Representation ℂ P W) (K : Subgroup G) (x : W) (g : G) : W :=
  if h : ∃ p : P, (p : G)⁻¹ * g ∈ K then σ h.choose x else 0

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] {P : Subgroup G}
  {σ : Representation ℂ P W} {K : Subgroup G} {x : W}

/- English proof (translation)
Establish `h : ∃ p : P, (p : G)⁻¹ * g ∈ K` using `⟨p, hp⟩`. Establish `hq` using `h.choose_spec`. Rewrite using `[bump, dif_pos h]`. Use `set q := h.choose`. Establish `hm : ((q⁻¹ * p : P) : G) ∈ K`.

Use `K.mul_mem hq (K.inv_mem hp)` as an intermediate fact. Establish `e : (q : G)⁻¹ * g * ((p : G)⁻¹ * g)⁻¹ = ((q⁻¹ * p : P) : G)`. Simplify using `[mul_assoc]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `h2` using `hx _ hm`.

Establish `h3 : σ p x = σ q (σ (q⁻¹ * p) x)`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Rewrite using `[h3, h2]`.
-/
theorem bump_eq (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {p : P} {g : G}
    (hp : (p : G)⁻¹ * g ∈ K) : bump P σ K x g = σ p x := by
  have h : ∃ p : P, (p : G)⁻¹ * g ∈ K := ⟨p, hp⟩
  have hq := h.choose_spec
  rw [bump, dif_pos h]
  set q := h.choose
  have hm : ((q⁻¹ * p : P) : G) ∈ K := by
    have := K.mul_mem hq (K.inv_mem hp)
    have e : (q : G)⁻¹ * g * ((p : G)⁻¹ * g)⁻¹ = ((q⁻¹ * p : P) : G) := by
      simp [mul_assoc]
    rwa [e] at this
  have h2 := hx _ hm
  have h3 : σ p x = σ q (σ (q⁻¹ * p) x) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [h3, h2]

/- English proof (translation)
Rewrite using `[bump, dif_neg h]`.
-/
theorem bump_of_not {g : G} (h : ¬ ∃ p : P, (p : G)⁻¹ * g ∈ K) : bump P σ K x g = 0 := by
  rw [bump, dif_neg h]

/- English proof (translation)
Distinguish the cases in `h : ∃ q : P, (q : G)⁻¹ * g ∈ K`. Take `⟨q, hq⟩` from `h`. Establish `hq' : (((p * q : P) : G))⁻¹ * ((p : G) * g) ∈ K`. Establish `e : (((p * q : P) : G))⁻¹ * ((p : G) * g) = (q : G)⁻¹ * g`. Simplify using `[mul_assoc]`.

Rewrite using `[e]` and apply the resulting hypothesis. Rewrite using `[bump_eq hx hq', bump_eq hx hq, map_mul, Module.End.mul_apply]`. Establish `h' : ¬ ∃ r : P, (r : G)⁻¹ * ((p : G) * g) ∈ K`. Introduce and unpack `⟨r, hr⟩`. Use `h ⟨p⁻¹ * r, ?_⟩` and prove the remaining obligations.

Establish `e : (((p⁻¹ * r : P) : G))⁻¹ * g = (r : G)⁻¹ * ((p : G) * g)`. Simplify using `[mul_assoc]`. Rewrite using `[e]` and apply the resulting hypothesis. Rewrite using `[bump_of_not h, bump_of_not h', map_zero]`.
-/
theorem bump_mul_left (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (p : P) (g : G) :
    bump P σ K x ((p : G) * g) = σ p (bump P σ K x g) := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (((p * q : P) : G))⁻¹ * ((p : G) * g) ∈ K := by
      have e : (((p * q : P) : G))⁻¹ * ((p : G) * g) = (q : G)⁻¹ * g := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_eq hx hq', bump_eq hx hq, map_mul, Module.End.mul_apply]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * ((p : G) * g) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨p⁻¹ * r, ?_⟩
      have e : (((p⁻¹ * r : P) : G))⁻¹ * g = (r : G)⁻¹ * ((p : G) * g) := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_of_not h, bump_of_not h', map_zero]

/- English proof (translation)
Distinguish the cases in `h : ∃ q : P, (q : G)⁻¹ * g ∈ K`. Take `⟨q, hq⟩` from `h`. Establish `hq' : (q : G)⁻¹ * (g * k) ∈ K`. Rewrite using `[← mul_assoc]`. Conclude with `K.mul_mem hq hk`.

Rewrite using `[bump_eq hx hq', bump_eq hx hq]`. Establish `h' : ¬ ∃ r : P, (r : G)⁻¹ * (g * k) ∈ K`. Introduce and unpack `⟨r, hr⟩`. Use `h ⟨r, ?_⟩` and prove the remaining obligations. Use `K.mul_mem hr (K.inv_mem hk)` as an intermediate fact.

Establish `e : (r : G)⁻¹ * (g * k) * k⁻¹ = (r : G)⁻¹ * g` using `by simp [mul_assoc]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[bump_of_not h, bump_of_not h']`.
-/
theorem bump_mul_right (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (g : G) {k : G} (hk : k ∈ K) :
    bump P σ K x (g * k) = bump P σ K x g := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (q : G)⁻¹ * (g * k) ∈ K := by
      rw [← mul_assoc]; exact K.mul_mem hq hk
    rw [bump_eq hx hq', bump_eq hx hq]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * (g * k) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨r, ?_⟩
      have := K.mul_mem hr (K.inv_mem hk)
      have e : (r : G)⁻¹ * (g * k) * k⁻¹ = (r : G)⁻¹ * g := by simp [mul_assoc]
      rwa [e] at this
    rw [bump_of_not h, bump_of_not h']

/- English proof (translation)
Establish `h : ((1 : P) : G)⁻¹ * 1 ∈ K` using `by simp [K.one_mem]`. Rewrite using `[bump_eq hx h]`. Simplify using the standard rewrite rules.
-/
theorem bump_one (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : bump P σ K x 1 = x := by
  have h : ((1 : P) : G)⁻¹ * 1 ∈ K := by simp [K.one_mem]
  rw [bump_eq hx h]; simp

def bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : indSpace P σ :=
  ⟨bump P σ K x, fun p g => bump_mul_left hx p g⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Conclude with `bump_mul_right hx g hk`.
-/
theorem ind_bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {k : G} (hk : k ∈ K) :
    ind P σ k (bumpInd hx) = bumpInd hx := by
  apply Subtype.ext
  funext g
  exact bump_mul_right hx g hk

/- English proof (translation)
Establish `hs : bumpInd hx ∈ smoothPart (ind P σ)` using `mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem) fun k hk => ind_bumpInd hx hk)`. Use `(Submodule.ne_bot_iff _).2 ⟨⟨bumpInd hx, hs⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `Subtype.ext (ind_bumpInd hx k.2)`.

Introduce `h`. Apply `hx0` to reduce the goal to its premises. Establish `h1` using `congrFun (congrArg (fun φ : smoothPart (ind P σ) => (φ.1 : G → W)) h) 1`. Rewrite using `[← bump_one hx]`. Conclude with `h1`.
-/
theorem fixed_smInd_ne_bot [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G))
    (hx0 : x ≠ 0) (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : fixed (smInd P σ) K ≠ ⊥ := by
  have hs : bumpInd hx ∈ smoothPart (ind P σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun k hk => ind_bumpInd hx hk)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨bumpInd hx, hs⟩, ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (ind_bumpInd hx k.2)
  · intro h
    apply hx0
    have h1 := congrFun (congrArg (fun φ : smoothPart (ind P σ) => (φ.1 : G → W)) h) 1
    rw [← bump_one hx]
    exact h1

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ hK _ hx0 hx` and use `fixed_smInd_ne_bot hK hx0 hx`.
-/
theorem fixed_smInd_ne_bot_of_fixed : ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G), IsOpen (K : Set G) → ∀ x : W, x ≠ 0 → (∀ p : P, (p : G) ∈ K → σ p x = x) → fixed (smInd P σ) K ≠ ⊥ :=
  fun _ _ _ _ _ _ _ _ _ _ hK _ hx0 hx => fixed_smInd_ne_bot hK hx0 hx

end GlobalTheory.CompanionTheory.SmInd
