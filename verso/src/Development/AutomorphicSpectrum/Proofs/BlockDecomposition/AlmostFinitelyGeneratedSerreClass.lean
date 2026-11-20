import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.AlmostFinite

section Sub

variable {R : Type} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def AF (c : R) (N : Submodule R M) : Prop :=
  ∃ (n : ℕ) (G : Submodule R M), G.FG ∧ G ≤ N ∧ ∀ x ∈ N, c ^ n • x ∈ G

def AN (c : R) (A : Submodule R M) : Prop := ∀ N : Submodule R M, N ≤ A → AF c N

/- English proof (translation)
Introduce `N hN` and use `h N (hN.trans hAB)`.
-/
theorem AN.mono {c : R} {A B : Submodule R M} (h : AN c B) (hAB : A ≤ B) : AN c A :=
  fun N hN => h N (hN.trans hAB)

/- English proof (translation)
Introduce `N hN` and use `⟨0, ⊥, Submodule.fg_bot, bot_le, fun x hx => by have h := hN hx simp only [Submodule.mem_bot] at h simp [h]⟩`.
-/
theorem an_bot (c : R) : AN c (⊥ : Submodule R M) := fun N hN =>
  ⟨0, ⊥, Submodule.fg_bot, bot_le, fun x hx => by
    have h := hN hx
    simp only [Submodule.mem_bot] at h
    simp [h]⟩

/- English proof (translation)
Introduce `N hN`. Establish `key : ∃ (n : ℕ) (G : Submodule R M), G.FG ∧ G ≤ N ∧ ∀ y ∈ N, ∃ g ∈ G, c ^ n • y - g ∈ A`. Distinguish the cases in `h : ∃ a₀ ∈ A, ∃ r₀ : R, r₀ ∉ I ∧ a₀ + r₀ • x ∈ N`. Take `⟨a₀, ha₀, r₀, hr₀, hy₀⟩` from `h`. Take `⟨n, hn⟩` from `hc r₀ hr₀`.

Take `⟨u, hu, i, hi, hui⟩` from `Submodule.mem_sup.1 hn`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Use `⟨n, Submodule.span R {a₀ + r₀ • x}, Submodule.fg_span_singleton _, (Submodule.span_singleton_le_iff_mem _ _).2 hy₀, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (hN hy)`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hb`.

Use `⟨(s * r) • (a₀ + r₀ • x), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩` and prove the remaining obligations. Establish `e : c ^ n • (a + r • x) - (s * r) • (a₀ + r₀ • x) = c ^ n • a + r • (i • x) - (s * r) • a₀`. Rewrite using `[← hui]`. Use `module`. Rewrite using `[e]`.

Conclude with `A.sub_mem (A.add_mem (A.smul_mem _ ha) (A.smul_mem _ (hx i hi))) (A.smul_mem _ ha₀)`. Use `⟨0, ⊥, Submodule.fg_bot, bot_le, fun y hy => ⟨0, Submodule.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (hN hy)`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Establish `hr : r ∈ I`.

Assume the negation of the conclusion as `hr`. Conclude with `h ⟨a, ha, r, hr, hy⟩`. Simplify using `using A.add_mem ha (hx r hr)`. Take `⟨n, G, hG, hGN, hy⟩` from `key`. Take `⟨m, G₂, hG₂, hG₂le, hm⟩` from `hA (N ⊓ A) inf_le_right`.

Use `⟨m + n, G ⊔ G₂, hG.sup hG₂, sup_le hGN (hG₂le.trans inf_le_left), fun y hyN => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hgA⟩` from `hy y hyN`. Establish `h1 : c ^ n • y - g ∈ N ⊓ A` using `⟨N.sub_mem (N.smul_mem _ hyN) (hGN hg), hgA⟩`. Establish `h2` using `hm _ h1`. Establish `e : c ^ (m + n) • y = c ^ m • g + c ^ m • (c ^ n • y - g)`.

Rewrite using `[pow_add, mul_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (G.smul_mem _ hg)) (Submodule.mem_sup_right h2)`.
-/
theorem AN.step {I : Ideal R} {c : R}
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {A : Submodule R M} {x : M} (hx : ∀ i ∈ I, i • x ∈ A) (hA : AN c A) :
    AN c (A ⊔ Submodule.span R {x}) := by
  intro N hN
  have key : ∃ (n : ℕ) (G : Submodule R M), G.FG ∧ G ≤ N ∧
      ∀ y ∈ N, ∃ g ∈ G, c ^ n • y - g ∈ A := by
    by_cases h : ∃ a₀ ∈ A, ∃ r₀ : R, r₀ ∉ I ∧ a₀ + r₀ • x ∈ N
    · obtain ⟨a₀, ha₀, r₀, hr₀, hy₀⟩ := h
      obtain ⟨n, hn⟩ := hc r₀ hr₀
      obtain ⟨u, hu, i, hi, hui⟩ := Submodule.mem_sup.1 hn
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hu
      refine ⟨n, Submodule.span R {a₀ + r₀ • x}, Submodule.fg_span_singleton _,
        (Submodule.span_singleton_le_iff_mem _ _).2 hy₀, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hN hy)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine ⟨(s * r) • (a₀ + r₀ • x),
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      have e : c ^ n • (a + r • x) - (s * r) • (a₀ + r₀ • x)
          = c ^ n • a + r • (i • x) - (s * r) • a₀ := by
        rw [← hui]; module
      rw [e]
      exact A.sub_mem (A.add_mem (A.smul_mem _ ha) (A.smul_mem _ (hx i hi))) (A.smul_mem _ ha₀)
    · refine ⟨0, ⊥, Submodule.fg_bot, bot_le, fun y hy => ⟨0, Submodule.zero_mem _, ?_⟩⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hN hy)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
      have hr : r ∈ I := by
        by_contra hr
        exact h ⟨a, ha, r, hr, hy⟩
      simpa using A.add_mem ha (hx r hr)
  obtain ⟨n, G, hG, hGN, hy⟩ := key
  obtain ⟨m, G₂, hG₂, hG₂le, hm⟩ := hA (N ⊓ A) inf_le_right
  refine ⟨m + n, G ⊔ G₂, hG.sup hG₂, sup_le hGN (hG₂le.trans inf_le_left), fun y hyN => ?_⟩
  obtain ⟨g, hg, hgA⟩ := hy y hyN
  have h1 : c ^ n • y - g ∈ N ⊓ A := ⟨N.sub_mem (N.smul_mem _ hyN) (hGN hg), hgA⟩
  have h2 := hm _ h1
  have e : c ^ (m + n) • y = c ^ m • g + c ^ m • (c ^ n • y - g) := by
    rw [pow_add, mul_smul, smul_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (G.smul_mem _ hg)) (Submodule.mem_sup_right h2)

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using hA`. Consider the case `insert a s _ ih`. Establish `h` using `AN.step hc (A := A ⊔ Submodule.span R (s : Set M)) (x := a) (fun i hi => Submodule.mem_sup_left (hT a (Finset.mem_insert_self _ _) i hi)) (ih fun t ht => hT t (Finset.mem_insert_of_mem ht))`. Use `h.mono ?_` and prove the remaining obligations.

Rewrite using `[Finset.coe_insert, Submodule.span_insert]`. Conclude with `sup_le (le_sup_of_le_left le_sup_left) (sup_le le_sup_right (le_sup_of_le_left le_sup_right))`.
-/
theorem AN.finset {I : Ideal R} {c : R}
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {A : Submodule R M} (hA : AN c A) (T : Finset M) (hT : ∀ t ∈ T, ∀ i ∈ I, i • t ∈ A) :
    AN c (A ⊔ Submodule.span R (T : Set M)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hA
  | insert a s _ ih =>
    have h := AN.step hc (A := A ⊔ Submodule.span R (s : Set M)) (x := a)
      (fun i hi => Submodule.mem_sup_left (hT a (Finset.mem_insert_self _ _) i hi))
      (ih fun t ht => hT t (Finset.mem_insert_of_mem ht))
    refine h.mono ?_
    rw [Finset.coe_insert, Submodule.span_insert]
    exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le le_sup_right (le_sup_of_le_left le_sup_right))

/- English proof (translation)
Establish `main : ∀ d j : ℕ, I ^ (j + d) = ⊥ → AN c (I ^ j • F)`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `j hj`.

Rewrite `hj` using `[add_zero]`. Rewrite using `[hj, Submodule.bot_smul]`. Conclude with `an_bot c`. Consider the case `succ d ih`. Introduce `j hj`.

Establish `hA : AN c (I ^ (j + 1) • F)` using `ih (j + 1) (by rw [← hj]; congr 1; omega)`. Take `⟨T, hT⟩ : (I ^ j • F).FG` from `Submodule.FG.smul (hI.pow) hF`. Use `(AN.finset hc hA T fun t ht i hi => ?_).mono ?_` and prove the remaining obligations. Establish `ht' : t ∈ I ^ j • F` using `hT ▸ Submodule.subset_span ht`. Rewrite using `[pow_succ', mul_smul]`.

Conclude with `Submodule.smul_mem_smul hi ht'`. Rewrite using `[hT]`. Conclude with `le_sup_right`. Take `⟨k, hk⟩` from `hnil`. Use `main k 0 (by simpa using hk)` as an intermediate fact.

Simplify using `using this`.
-/
theorem AN.of_fg {I : Ideal R} {c : R} (hI : I.FG) (hnil : IsNilpotent I)
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {F : Submodule R M} (hF : F.FG) : AN c F := by
  have main : ∀ d j : ℕ, I ^ (j + d) = ⊥ → AN c (I ^ j • F) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [add_zero] at hj
      rw [hj, Submodule.bot_smul]
      exact an_bot c
    | succ d ih =>
      intro j hj
      have hA : AN c (I ^ (j + 1) • F) := ih (j + 1) (by rw [← hj]; congr 1; omega)
      obtain ⟨T, hT⟩ : (I ^ j • F).FG := Submodule.FG.smul (hI.pow) hF
      refine (AN.finset hc hA T fun t ht i hi => ?_).mono ?_
      · have ht' : t ∈ I ^ j • F := hT ▸ Submodule.subset_span ht
        rw [pow_succ', mul_smul]
        exact Submodule.smul_mem_smul hi ht'
      · rw [hT]; exact le_sup_right
  obtain ⟨k, hk⟩ := hnil
  have := main k 0 (by simpa using hk)
  simpa using this

/- English proof (translation)
Take `⟨n, F, hF, hn⟩` from `hM`. Take `⟨m, G, hG, hGle, hm⟩` from `AN.of_fg hI hnil hc hF (N ⊓ F) inf_le_right`. Use `⟨m + n, G, hG, hGle.trans inf_le_left, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `hm _ (⟨N.smul_mem _ hx, hn x⟩ : c ^ n • x ∈ N ⊓ F)`. Rewrite `h` using `[← mul_smul, ← pow_add]`. Then use the resulting hypothesis.
-/
theorem af_of_afg {I : Ideal R} {c : R} (hI : I.FG) (hnil : IsNilpotent I)
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hM : AFG c M) (N : Submodule R M) : AF c N := by
  obtain ⟨n, F, hF, hn⟩ := hM
  obtain ⟨m, G, hG, hGle, hm⟩ := AN.of_fg hI hnil hc hF (N ⊓ F) inf_le_right
  refine ⟨m + n, G, hG, hGle.trans inf_le_left, fun x hx => ?_⟩
  have h := hm _ (⟨N.smul_mem _ hx, hn x⟩ : c ^ n • x ∈ N ⊓ F)
  rwa [← mul_smul, ← pow_add] at h

/- English proof (translation)
Take `⟨s, rfl⟩` from `hG`. Establish `h : (s : Set M₂) ⊆ g '' Set.univ` using `fun y hy => by`. Simplify using `using hle (Submodule.subset_span hy)`. Take `⟨s', -, rfl⟩` from `Finset.subset_set_image_iff.1 h`. Conclude with `⟨Submodule.span R (s' : Set M), ⟨s', rfl⟩, by rw [Submodule.map_span]; simp⟩`.
-/
theorem exists_fg_map_eq {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (g : M →ₗ[R] M₂)
    {G : Submodule R M₂} (hG : G.FG) (hle : G ≤ LinearMap.range g) :
    ∃ G' : Submodule R M, G'.FG ∧ G'.map g = G := by
  classical
  obtain ⟨s, rfl⟩ := hG
  have h : (s : Set M₂) ⊆ g '' Set.univ := fun y hy => by
    simpa using hle (Submodule.subset_span hy)
  obtain ⟨s', -, rfl⟩ := Finset.subset_set_image_iff.1 h
  exact ⟨Submodule.span R (s' : Set M), ⟨s', rfl⟩, by rw [Submodule.map_span]; simp⟩

/- English proof (translation)
Take `⟨a, G₃, hG₃, hG₃le, ha⟩` from `af_of_afg hI hnil hc h₃ (LinearMap.range g)`. Take `⟨G', hG', rfl⟩` from `exists_fg_map_eq g hG₃ hG₃le`. Take `⟨b, N₁, hN₁, hb⟩` from `h₁`. Use `⟨b + a, G' ⊔ N₁.map f, hG'.sup (hN₁.map f), fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hyx⟩` from `(Submodule.mem_map).1 (ha (g x) ⟨x, rfl⟩)`.

Take `⟨z, hz⟩` from `(hfg (c ^ a • x - y)).1 (by rw [map_sub, map_smul, hyx, sub_self])`. Establish `e : c ^ (b + a) • x = c ^ b • y + f (c ^ b • z)`. Rewrite using `[map_smul, hz, pow_add, mul_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (G'.smul_mem _ hy)) (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hb z)))`.
-/
theorem afg_mid {I : Ideal R} {c : R} (hI : I.FG) (hnil : IsNilpotent I)
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : Function.Exact f g) (h₁ : AFG c M₁) (h₃ : AFG c M₃) : AFG c M₂ := by
  obtain ⟨a, G₃, hG₃, hG₃le, ha⟩ := af_of_afg hI hnil hc h₃ (LinearMap.range g)
  obtain ⟨G', hG', rfl⟩ := exists_fg_map_eq g hG₃ hG₃le
  obtain ⟨b, N₁, hN₁, hb⟩ := h₁
  refine ⟨b + a, G' ⊔ N₁.map f, hG'.sup (hN₁.map f), fun x => ?_⟩
  obtain ⟨y, hy, hyx⟩ := (Submodule.mem_map).1 (ha (g x) ⟨x, rfl⟩)
  obtain ⟨z, hz⟩ := (hfg (c ^ a • x - y)).1 (by rw [map_sub, map_smul, hyx, sub_self])
  have e : c ^ (b + a) • x = c ^ b • y + f (c ^ b • z) := by
    rw [map_smul, hz, pow_add, mul_smul, smul_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (G'.smul_mem _ hy))
    (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hb z)))

end Sub

/- English proof (translation)
Introduce `R _ I c hI hnil _ _ hc`. Use `⟨⟨fun M _ _ => AFG c M, fun M _ _ _ => ⟨0, ⊥, Submodule.fg_bot, fun x => ?_⟩, fun M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ => afg_mid hI hnil hc f g hfg h₁ h₃⟩, fun M _ _ => Iff.rfl⟩` and prove the remaining obligations. Simplify using `[Subsingleton.elim x 0]`.
-/
theorem serre_afg : ∀ (R : Type) [CommRing R] (I : Ideal R) (c : R), I.FG → IsNilpotent I → I.IsPrime →
    (∀ x y : R, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I) → (∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I) →
    ∃ 𝒮 : Serre.{1} R, ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ AFG c M := by
  intro R _ I c hI hnil _ _ hc
  refine ⟨⟨fun M _ _ => AFG c M, fun M _ _ _ => ⟨0, ⊥, Submodule.fg_bot, fun x => ?_⟩,
    fun M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ => afg_mid hI hnil hc f g hfg h₁ h₃⟩,
    fun M _ _ => Iff.rfl⟩
  simp [Subsingleton.elim x 0]

end GlobalTheory.CompanionTheory.AlmostFinite
