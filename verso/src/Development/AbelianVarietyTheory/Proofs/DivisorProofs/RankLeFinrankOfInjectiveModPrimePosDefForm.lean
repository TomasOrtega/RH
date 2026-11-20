import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModLStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

def satSpanFamily {H : Type} [AddCommGroup H] {n : ℕ} (u : Fin n → H) : AddSubgroup H where
  carrier := {h | ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u)}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk, ha⟩ ⟨m, hm, hb⟩
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm k m a]
    exact add_mem (Submodule.smul_mem _ m ha) (Submodule.smul_mem _ k hb)
  neg_mem' := by
    rintro a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_neg]; exact neg_mem ha⟩

/- English proof (translation)
Introduce `l _ H T _ _ _ _ _ Q hpar hnn hdef φ hφ n u hu`. Use `set M := satSpanFamily u with hMdef`. Establish `memM : ∀ h, h ∈ M ↔ ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u)` using `fun h => Iff.rfl`. Establish `hbound : ∀ (m : ℕ) (v : Fin m → M), LinearIndependent ℤ v → m ≤ n`. Introduce `m v hv`.

Use `choose k hk hks using fun j => (memM (v j : H)).1 (v j).2`. Set `w : Fin m → Submodule.span ℤ (Set.range u)` to `fun j => ⟨k j • (v j : H), hks j⟩`. Establish `hw : LinearIndependent ℤ w`. Rewrite `hv`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`.

Establish `h1 : ∑ i, (g i * k i) • v i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val hg` as an intermediate fact. Simplify `this` using `[w, mul_smul]`. Conclude with `(mul_eq_zero.1 (hv _ h1 j)).resolve_right (hk j)`.

Use `haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) := Module.Finite.span_of_finite ℤ (Set.finite_range u)`. Use `hw.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[finrank_span_eq_card hu]`. Simplify using `using this`. Take `⟨hfin, hfree, -⟩` from `GlobalTheory.finite_free_of_definite_form_of_rank_le M (fun x => Q x) (fun f g => by simpa using hpar f g) (fun f => hnn f) (fun f hf => Subtype.ext (hdef _ hf)) n hbound`.

Use `haveI := hfin`. Use `haveI := hfree`. Set `ψ : M →+ T` to `φ.comp M.subtype`. Establish `hlne : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Establish `hψ : ∀ (h : M) (t : T), ψ h = (l : ℤ_[l]) • t → ∃ h' : M, h = l • h'`.

Introduce `h t ht`. Take `⟨h', hh'⟩` from `hφ (h : H) t ht`. Take `⟨k, hk, hks⟩` from `(memM (h : H)).1 h.2`. Use `⟨⟨h', k * l, mul_ne_zero hk (by exact_mod_cast hlne), ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, natCast_zsmul, ← hh']`.

Conclude with `hks`. Simplify using `[hh']`. Establish `htor : ∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0`. Introduce `t ht`. Establish `hl : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hlne`.

Conclude with `(smul_eq_zero.1 ht).resolve_left hl`. Take `⟨hinj, -⟩` from `GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL l M T htor ψ hψ`. Establish `h1` using `LinearMap.finrank_le_finrank_of_injective hinj`. Rewrite `h1` using `[Module.finrank_baseChange]`. Set `v : Fin n → M` to `fun i => ⟨u i, 1, one_ne_zero, by`.

Simplify using `using Submodule.subset_span (Set.mem_range_self i)⟩`. Establish `hv : LinearIndependent ℤ v` using `LinearIndependent.of_comp M.subtype.toIntLinearMap (by`. Establish `e : (M.subtype.toIntLinearMap : M →ₗ[ℤ] H) ∘ v = u` using `funext fun i => rfl`. Rewrite using `[e]`. Conclude with `hu)`.

Establish `h2` using `hv.fintype_card_le_finrank`. Simplify using `only [Fintype.card_fin] at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_le_finrank_of_injective_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  intro l _ H T _ _ _ _ _ Q hpar hnn hdef φ hφ n u hu
  classical
  set M := satSpanFamily u with hMdef
  have memM : ∀ h, h ∈ M ↔ ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u) :=
    fun h => Iff.rfl
  have hbound : ∀ (m : ℕ) (v : Fin m → M), LinearIndependent ℤ v → m ≤ n := by
    intro m v hv
    choose k hk hks using fun j => (memM (v j : H)).1 (v j).2
    let w : Fin m → Submodule.span ℤ (Set.range u) := fun j => ⟨k j • (v j : H), hks j⟩
    have hw : LinearIndependent ℤ w := by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro g hg j
      have h1 : ∑ i, (g i * k i) • v i = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val hg
        simpa [w, mul_smul] using this
      exact (mul_eq_zero.1 (hv _ h1 j)).resolve_right (hk j)
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range u)
    have := hw.fintype_card_le_finrank
    rw [finrank_span_eq_card hu] at this
    simpa using this
  obtain ⟨hfin, hfree, -⟩ := GlobalTheory.finite_free_of_definite_form_of_rank_le M (fun x => Q x)
    (fun f g => by simpa using hpar f g) (fun f => hnn f) (fun f hf => Subtype.ext (hdef _ hf)) n hbound
  haveI := hfin
  haveI := hfree
  let ψ : M →+ T := φ.comp M.subtype
  have hlne : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hψ : ∀ (h : M) (t : T), ψ h = (l : ℤ_[l]) • t → ∃ h' : M, h = l • h' := by
    intro h t ht
    obtain ⟨h', hh'⟩ := hφ (h : H) t ht
    obtain ⟨k, hk, hks⟩ := (memM (h : H)).1 h.2
    refine ⟨⟨h', k * l, mul_ne_zero hk (by exact_mod_cast hlne), ?_⟩, Subtype.ext ?_⟩
    · rw [mul_smul, natCast_zsmul, ← hh']
      exact hks
    · simp [hh']
  have htor : ∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0 := by
    intro t ht
    have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hlne
    exact (smul_eq_zero.1 ht).resolve_left hl
  obtain ⟨hinj, -⟩ := GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL l M T htor ψ hψ
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_baseChange] at h1
  let v : Fin n → M := fun i => ⟨u i, 1, one_ne_zero, by
    simpa using Submodule.subset_span (Set.mem_range_self i)⟩
  have hv : LinearIndependent ℤ v :=
    LinearIndependent.of_comp M.subtype.toIntLinearMap (by
      have e : (M.subtype.toIntLinearMap : M →ₗ[ℤ] H) ∘ v = u := funext fun i => rfl
      rw [e]; exact hu)
  have h2 := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h2
  omega

end GlobalTheory
