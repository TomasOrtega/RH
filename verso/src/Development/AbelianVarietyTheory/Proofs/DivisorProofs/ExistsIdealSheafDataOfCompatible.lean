import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.AffineIdealGlue

variable {X : Scheme.{0}}

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
lemma res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom s) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def glueIdeal (𝒜 : Set X.affineOpens) (k : ∀ W : X.affineOpens, Ideal Γ(X, W))
    (V : X.affineOpens) : Ideal Γ(X, V) :=
  ⨅ W ∈ 𝒜, ⨅ h : W ≤ V, (k W).comap (X.presheaf.map (homOfLE h).op).hom

/- English proof (translation)
Simplify using `[glueIdeal, Submodule.mem_iInf]`.
-/
lemma mem_glueIdeal {𝒜 : Set X.affineOpens} {k : ∀ W : X.affineOpens, Ideal Γ(X, W)}
    {V : X.affineOpens} {s : Γ(X, V)} :
    s ∈ glueIdeal 𝒜 k V ↔
      ∀ W ∈ 𝒜, ∀ h : W ≤ V, (X.presheaf.map (homOfLE h).op).hom s ∈ k W := by
  simp [glueIdeal, Submodule.mem_iInf]

section
variable {𝒜 : Set X.affineOpens} {k : ∀ W : X.affineOpens, Ideal Γ(X, W)}
  (hk : ∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
    (k W).map (X.presheaf.map (homOfLE h).op).hom = k W')
include hk

/- English proof (translation)
Rewrite using `[← hk W hW W' h]`. Conclude with `Ideal.mem_map_of_mem _ hs`.
-/
lemma res_mem {W W' : X.affineOpens} (hW : W ∈ 𝒜) (h : W' ≤ W) {s : Γ(X, W)} (hs : s ∈ k W) :
    (X.presheaf.map (homOfLE h).op).hom s ∈ k W' := by
  rw [← hk W hW W' h]; exact Ideal.mem_map_of_mem _ hs

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `s hs`. Use `mem_glueIdeal.1 hs V hV le_rfl` as an intermediate fact. Use `erw [X.presheaf.map_id] at this`. Conclude with `this`.

Introduce `s hs`. Conclude with `mem_glueIdeal.2 fun W hW h => res_mem hk hV h hs`.
-/
lemma glueIdeal_eq {V : X.affineOpens} (hV : V ∈ 𝒜) : glueIdeal 𝒜 k V = k V := by
  apply le_antisymm
  · intro s hs
    have := mem_glueIdeal.1 hs V hV le_rfl
    erw [X.presheaf.map_id] at this
    exact this
  · intro s hs
    exact mem_glueIdeal.2 fun W hW h => res_mem hk hV h hs

/- English proof (translation)
Use `haveI := B.2.isLocalization_basicOpen g`. Rewrite `hx` using `[← hk B hB (X.affineBasicOpen g) (X.affineBasicOpen_le g)]`. Express the relevant statement in the definitionally equal form `algebraMap Γ(X, B) Γ(X, X.basicOpen g) x ∈ Ideal.map (algebraMap Γ(X, B) Γ(X, X.basicOpen g)) (k B) at hx`. Take `⟨_, ⟨n, rfl⟩, h⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) Γ(X, X.basicOpen g) (k B) x).1 hx`. Conclude with `⟨n, h⟩`.
-/
lemma exists_pow_mul_mem {B : X.affineOpens} (hB : B ∈ 𝒜) (g x : Γ(X, B))
    (hx : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom x ∈ k (X.affineBasicOpen g)) :
    ∃ n : ℕ, g ^ n * x ∈ k B := by
  haveI := B.2.isLocalization_basicOpen g
  rw [← hk B hB (X.affineBasicOpen g) (X.affineBasicOpen_le g)] at hx
  change algebraMap Γ(X, B) Γ(X, X.basicOpen g) x ∈
    Ideal.map (algebraMap Γ(X, B) Γ(X, X.basicOpen g)) (k B) at hx
  obtain ⟨_, ⟨n, rfl⟩, h⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) Γ(X, X.basicOpen g) (k B) x).1 hx
  exact ⟨n, h⟩

/- English proof (translation)
Establish `hloc : ∀ y : U.1, ∃ h : Γ(X, U), y.1 ∈ X.basicOpen h ∧ X.affineBasicOpen h ∈ 𝒜 ∧ ∃ m : ℕ, (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (f ^ m * a) ∈ k (X.affineBasicOpen h)`. Introduce `y`. Take `⟨W0, hW0, hyW0⟩` from `hcov y.1`. Take `⟨h, hhW0, hyh⟩` from `U.2.exists_basicOpen_le (V := W0.1) ⟨y.1, hyW0⟩ y.2`. Establish `hB : X.affineBasicOpen h ∈ 𝒜` using `h𝒜 W0 hW0 _ hhW0`.

Use `⟨h, hyh, hB, ?_⟩` and prove the remaining obligations. Establish `hle : X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f) ≤ X.basicOpen f`. Rewrite using `[Scheme.basicOpen_res]`. Conclude with `inf_le_right`. Take `⟨m, hm⟩` from `exists_pow_mul_mem hk hB ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f) ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom a) (by`.

Establish `hmem` using `ha (X.affineBasicOpen _) (h𝒜 _ hB _ (X.affineBasicOpen_le _)) hle`. Use `erw [res_res]`. Conclude with `hmem)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`.

Conclude with `hm`. Use `choose h hyh hB m hm using hloc`. Take `⟨F, hF⟩` from `U.2.isCompact.elim_finite_subcover (fun y => (X.basicOpen (h y) : Set X)) (fun y => (X.basicOpen (h y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyh ⟨y, hy⟩⟩)`. Establish `hspan : Ideal.span (h '' ↑F) = ⊤`. Rewrite using `[← U.2.self_le_iSup_basicOpen_iff]`.

Introduce `z hz`. Take `⟨y, hyF, hzy⟩ : ∃ y ∈ F, z ∈ X.basicOpen (h y)` from `by simpa using hF hz`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨h y, y, hyF, rfl⟩, hzy⟩`. Use `⟨∑ y ∈ F, m y, mem_glueIdeal.2 fun W hW hWU => ?_⟩` and prove the remaining obligations. Use `set ρ := (X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op).hom with hρ`.

Establish `hspanW : Ideal.span (ρ '' (h '' ↑F)) = ⊤`. Rewrite using `[← Ideal.map_span, hspan, Ideal.map_top]`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem (k W) _ hspanW _ ?_` and prove the remaining obligations. Introduce and unpack `⟨_, _, ⟨y, hyF, rfl⟩, rfl⟩`. Establish `hBy : (X.presheaf.map (homOfLE (X.basicOpen_le (h y))).op).hom (f ^ (∑ y ∈ F, m y) * a) ∈ k (X.affineBasicOpen (h y))`.

Establish `hle : m y ≤ ∑ y ∈ F, m y` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (hm y)`. Take `⟨n, hn⟩` from `exists_pow_mul_mem hk hW (ρ (h y)) (ρ (f ^ (∑ y ∈ F, m y) * a)) (by`. Establish `hle : (X.affineBasicOpen (ρ (h y))) ≤ X.affineBasicOpen (h y)`.

Express the relevant statement in the definitionally equal form `X.basicOpen (ρ (h y)) ≤ X.basicOpen (h y)`. Rewrite using `[hρ, Scheme.basicOpen_res]`. Conclude with `inf_le_right`. Use `res_mem hk (hB y) hle hBy` as an intermediate fact. Use `erw [res_res] at this`.

Rewrite using `[hρ]`. Use `erw [res_res]`. Conclude with `this)`. Conclude with `⟨n, hn⟩`.
-/
lemma exists_pow_mul_mem_glueIdeal (h𝒜 : ∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜)
    (hcov : ∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) (U : X.affineOpens) (f a : Γ(X, U))
    (ha : ∀ W ∈ 𝒜, ∀ h : W.1 ≤ X.basicOpen f,
      (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le f))).op).hom a ∈ k W) :
    ∃ m : ℕ, f ^ m * a ∈ glueIdeal 𝒜 k U := by
  classical
  have hloc : ∀ y : U.1, ∃ h : Γ(X, U), y.1 ∈ X.basicOpen h ∧ X.affineBasicOpen h ∈ 𝒜 ∧
      ∃ m : ℕ, (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (f ^ m * a) ∈
        k (X.affineBasicOpen h) := by
    intro y
    obtain ⟨W0, hW0, hyW0⟩ := hcov y.1
    obtain ⟨h, hhW0, hyh⟩ := U.2.exists_basicOpen_le (V := W0.1) ⟨y.1, hyW0⟩ y.2
    have hB : X.affineBasicOpen h ∈ 𝒜 := h𝒜 W0 hW0 _ hhW0
    refine ⟨h, hyh, hB, ?_⟩
    have hle : X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f) ≤
        X.basicOpen f := by
      rw [Scheme.basicOpen_res]; exact inf_le_right
    obtain ⟨m, hm⟩ := exists_pow_mul_mem hk hB
      ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f)
      ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom a) (by
        have hmem := ha (X.affineBasicOpen _) (h𝒜 _ hB _ (X.affineBasicOpen_le _)) hle
        erw [res_res]; exact hmem)
    refine ⟨m, ?_⟩
    rw [map_mul, map_pow]; exact hm
  choose h hyh hB m hm using hloc
  obtain ⟨F, hF⟩ := U.2.isCompact.elim_finite_subcover (fun y => (X.basicOpen (h y) : Set X))
    (fun y => (X.basicOpen (h y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyh ⟨y, hy⟩⟩)
  have hspan : Ideal.span (h '' ↑F) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro z hz
    obtain ⟨y, hyF, hzy⟩ : ∃ y ∈ F, z ∈ X.basicOpen (h y) := by simpa using hF hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨h y, y, hyF, rfl⟩, hzy⟩
  refine ⟨∑ y ∈ F, m y, mem_glueIdeal.2 fun W hW hWU => ?_⟩
  set ρ := (X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op).hom with hρ
  have hspanW : Ideal.span (ρ '' (h '' ↑F)) = ⊤ := by
    rw [← Ideal.map_span, hspan, Ideal.map_top]
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (k W) _ hspanW _ ?_
  rintro ⟨_, _, ⟨y, hyF, rfl⟩, rfl⟩

  have hBy : (X.presheaf.map (homOfLE (X.basicOpen_le (h y))).op).hom
      (f ^ (∑ y ∈ F, m y) * a) ∈ k (X.affineBasicOpen (h y)) := by
    have hle : m y ≤ ∑ y ∈ F, m y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
    exact Ideal.mul_mem_left _ _ (hm y)
  obtain ⟨n, hn⟩ := exists_pow_mul_mem hk hW (ρ (h y)) (ρ (f ^ (∑ y ∈ F, m y) * a)) (by
    have hle : (X.affineBasicOpen (ρ (h y))) ≤ X.affineBasicOpen (h y) := by
      change X.basicOpen (ρ (h y)) ≤ X.basicOpen (h y)
      rw [hρ, Scheme.basicOpen_res]; exact inf_le_right
    have := res_mem hk (hB y) hle hBy
    erw [res_res] at this
    rw [hρ]
    erw [res_res]
    exact this)
  exact ⟨n, hn⟩

/- English proof (translation)
Use `haveI := U.2.isLocalization_basicOpen f`. Establish `halg : ∀ y, algebraMap Γ(X, U) Γ(X, X.basicOpen f) y = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom y` using `fun _ => rfl`. Apply `le_antisymm` to reduce the goal to its premises. Use `Ideal.map_le_of_le_comap ?_` and prove the remaining obligations. Introduce `s hs`.

Establish `key : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom s ∈ glueIdeal 𝒜 k (X.affineBasicOpen f)`. Use `mem_glueIdeal.2 fun W hW hWf => ?_` and prove the remaining obligations. Use `erw [res_res]`. Conclude with `mem_glueIdeal.1 hs W hW _`. Conclude with `key`.

Introduce `t ht`. Take `⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers f) t`. Establish `hspec` using `IsLocalization.mk'_spec Γ(X, X.basicOpen f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)`. Simplify using `only at hspec`. Take `⟨m, hm⟩` from `exists_pow_mul_mem_glueIdeal hk h𝒜 hcov U f a (by`.

Introduce `W hW hWf`. Establish `e` using `res_res (X.basicOpen_le f) hWf a`. Rewrite using `[← e, ← halg, ← hspec, map_mul]`. Conclude with `Ideal.mul_mem_right _ _ (mem_glueIdeal.1 ht W hW hWf))`. Use `show _ ∈ Ideal.map (algebraMap Γ(X, U) Γ(X, X.basicOpen f)) (glueIdeal 𝒜 k U)`.

Rewrite using `[IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)]`. Use `⟨⟨⟨f ^ m * a, hm⟩, ⟨f ^ (m + n), m + n, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[pow_add, map_mul, map_mul]`. Take the linear combination `(algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ m)) * hspec`.
-/
lemma glueIdeal_basicOpen (h𝒜 : ∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜)
    (hcov : ∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) (U : X.affineOpens) (f : Γ(X, U)) :
    (glueIdeal 𝒜 k U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      glueIdeal 𝒜 k (X.affineBasicOpen f) := by
  haveI := U.2.isLocalization_basicOpen f
  have halg : ∀ y, algebraMap Γ(X, U) Γ(X, X.basicOpen f) y =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom y := fun _ => rfl
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap ?_
    intro s hs
    have key : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom s ∈
        glueIdeal 𝒜 k (X.affineBasicOpen f) := by
      refine mem_glueIdeal.2 fun W hW hWf => ?_
      erw [res_res]
      exact mem_glueIdeal.1 hs W hW _
    exact key
  · intro t ht
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
    have hspec := IsLocalization.mk'_spec Γ(X, X.basicOpen f) a
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    simp only at hspec
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_glueIdeal hk h𝒜 hcov U f a (by
      intro W hW hWf
      have e := res_res (X.basicOpen_le f) hWf a
      rw [← e, ← halg, ← hspec, map_mul]
      exact Ideal.mul_mem_right _ _ (mem_glueIdeal.1 ht W hW hWf))
    show _ ∈ Ideal.map (algebraMap Γ(X, U) Γ(X, X.basicOpen f)) (glueIdeal 𝒜 k U)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)]
    refine ⟨⟨⟨f ^ m * a, hm⟩, ⟨f ^ (m + n), m + n, rfl⟩⟩, ?_⟩
    simp only
    rw [pow_add, map_mul, map_mul]
    linear_combination (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ m)) * hspec

end

/- English proof (translation)
Introduce `X 𝒜 h𝒜 hcov k hk`. Conclude with `⟨{ ideal := glueIdeal 𝒜 k, map_ideal_basicOpen := glueIdeal_basicOpen hk h𝒜 hcov }, fun W hW => glueIdeal_eq hk hW⟩`.
-/
theorem exists_idealSheafData_of_compatible :
    ∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W := by
  intro X 𝒜 h𝒜 hcov k hk
  exact ⟨{ ideal := glueIdeal 𝒜 k, map_ideal_basicOpen := glueIdeal_basicOpen hk h𝒜 hcov },
    fun W hW => glueIdeal_eq hk hW⟩

end GlobalTheory.AffineIdealGlue
