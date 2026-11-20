import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

def HasFiniteLength (ρ : Representation ℂ G V) : Prop :=
  IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule

variable {ρ : Representation ℂ G V}

/- English proof (translation)
Rewrite using `[HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', IsArtinian]`. Set `e` to `Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨e.strictMono.wellFoundedLT, e.strictMono.wellFoundedGT⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨e.symm.strictMono.wellFoundedGT, e.symm.strictMono.wellFoundedLT⟩`.
-/
theorem hasFiniteLength_iff :
    HasFiniteLength ρ ↔
      WellFoundedLT (Subrepresentation ρ) ∧ WellFoundedGT (Subrepresentation ρ) := by
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', IsArtinian]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨e.strictMono.wellFoundedLT, e.strictMono.wellFoundedGT⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.symm.strictMono.wellFoundedGT, e.symm.strictMono.wellFoundedLT⟩

/- English proof (translation)
The claim follows from `(hasFiniteLength_iff.1 h).1`.
-/
theorem HasFiniteLength.wellFoundedLT (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).1

/- English proof (translation)
The claim follows from `(hasFiniteLength_iff.1 h).2`.
-/
theorem HasFiniteLength.wellFoundedGT (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).2

/- English proof (translation)
Rewrite using `[hasFiniteLength_iff]`. Use `⟨hΛ.wellFoundedLT, ?_⟩` and prove the remaining obligations. Establish `h1 : WellFoundedLT (∀ i, (α i)ᵒᵈ)` using `Pi.wellFoundedLT`. Establish `h2 : WellFoundedGT (∀ i, α i)` using `⟨h1.wf⟩`. Conclude with `hΛ.wellFoundedGT`.
-/
theorem hasFiniteLength_of_strictMono {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, WellFoundedLT (α i)] [∀ i, WellFoundedGT (α i)]
    (Λ : Subrepresentation ρ → ∀ i, α i) (hΛ : StrictMono Λ) : HasFiniteLength ρ := by
  rw [hasFiniteLength_iff]
  refine ⟨hΛ.wellFoundedLT, ?_⟩
  have h1 : WellFoundedLT (∀ i, (α i)ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i, α i) := ⟨h1.wf⟩
  exact hΛ.wellFoundedGT

/- English proof (translation)
Establish `: Subsingleton ρ.asModule` using `inferInstanceAs (Subsingleton V)`. Conclude with `IsFiniteLength.of_subsingleton`.
-/
theorem hasFiniteLength_of_subsingleton [Subsingleton V] : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  exact IsFiniteLength.of_subsingleton

/- English proof (translation)
Establish `: Finite (Subrepresentation ρ)` using `Finite.of_equiv _ IsSimpleOrder.equivBool.symm`. Rewrite using `[hasFiniteLength_iff]`. Conclude with `⟨Finite.to_wellFoundedLT, Finite.to_wellFoundedGT⟩`.
-/
theorem hasFiniteLength_of_isIrreducible [ρ.IsIrreducible] : HasFiniteLength ρ := by
  classical
  have : Finite (Subrepresentation ρ) := Finite.of_equiv _ IsSimpleOrder.equivBool.symm
  rw [hasFiniteLength_iff]
  exact ⟨Finite.to_wellFoundedLT, Finite.to_wellFoundedGT⟩

section MapComap

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

def subrepMap (f : Representation.IntertwiningMap ρ σ) (A : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, A.apply_mem_toSubmodule g hx, Representation.IntertwiningMap.isIntertwining _ _ f g x⟩

def subrepComap (f : Representation.IntertwiningMap ρ σ) (B : Subrepresentation σ) :
    Subrepresentation ρ where
  toSubmodule := B.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g x hx := by
    show f (ρ g x) ∈ B.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hx

/- English proof (translation)
Introduce `_ _ h _ ⟨x, hx, hxy⟩` and use `⟨x, h hx, hxy⟩`.
-/
theorem subrepMap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepMap f) :=
  fun _ _ h _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

/- English proof (translation)
Introduce `_ _ h _ hx` and use `h hx`.
-/
theorem subrepComap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepComap f) :=
  fun _ _ h _ hx => h hx

/- English proof (translation)
Use `hσ.wellFoundedLT` as an intermediate fact. Use `hσ.wellFoundedGT` as an intermediate fact. Use `hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation σ) (fun A _ => subrepMap f A) fun A B hAB => ?_` and prove the remaining obligations. Use `lt_of_le_of_ne (fun _ => subrepMap_mono f hAB.le) fun h => hAB.ne ?_` and prove the remaining obligations. Establish `h1` using `congrFun h ()`.

Use `le_antisymm hAB.le fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy, hyx⟩ : f x ∈ subrepMap f A` from `by show f x ∈ subrepMap f A`. Rewrite using `[show subrepMap f A = subrepMap f B from h1]`. Conclude with `⟨x, hx, rfl⟩`. Rewrite using `[← hf hyx]`.

Conclude with `hy`.
-/
theorem hasFiniteLength_of_injective (f : Representation.IntertwiningMap ρ σ)
    (hf : Injective f) (hσ : HasFiniteLength σ) : HasFiniteLength ρ := by
  have := hσ.wellFoundedLT
  have := hσ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation σ)
    (fun A _ => subrepMap f A) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepMap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ : f x ∈ subrepMap f A := by
    show f x ∈ subrepMap f A
    rw [show subrepMap f A = subrepMap f B from h1]
    exact ⟨x, hx, rfl⟩
  rw [← hf hyx]
  exact hy

/- English proof (translation)
Use `hρ.wellFoundedLT` as an intermediate fact. Use `hρ.wellFoundedGT` as an intermediate fact. Use `hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation ρ) (fun B _ => subrepComap f B) fun A B hAB => ?_` and prove the remaining obligations. Use `lt_of_le_of_ne (fun _ => subrepComap_mono f hAB.le) fun h => hAB.ne ?_` and prove the remaining obligations. Establish `h1` using `congrFun h ()`.

Use `le_antisymm hAB.le fun y hy => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hf y`. Establish `hx : x ∈ subrepComap f B` using `hy`. Rewrite `hx` using `[← show subrepComap f A = subrepComap f B from h1]`. Conclude with `hx`.
-/
theorem hasFiniteLength_of_surjective (f : Representation.IntertwiningMap ρ σ)
    (hf : Surjective f) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  have := hρ.wellFoundedLT
  have := hρ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation ρ)
    (fun B _ => subrepComap f B) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepComap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun y hy => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ subrepComap f B := hy
  rw [← show subrepComap f A = subrepComap f B from h1] at hx
  exact hx

end MapComap

section Filtration

/- English proof (translation)
Use `fun j => (hσ j).wellFoundedLT` as an intermediate fact. Use `fun j => (hσ j).wellFoundedGT` as an intermediate fact. Set `cut : ∀ j : Fin k, Subrepresentation ρ → Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)))` to `fun j A => ⟨A.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => A.apply_mem_toSubmodule g hx⟩`. Use `hasFiniteLength_of_strictMono (α := fun j => Subrepresentation (σ j)) (fun A j => subrepMap (Ψ j) (cut j A)) fun A B hAB => ?_` and prove the remaining obligations. Establish `hmono' : ∀ j, subrepMap (Ψ j) (cut j A) ≤ subrepMap (Ψ j) (cut j B)` using `fun j => subrepMap_mono _ (fun x hx => hAB.le hx)`.

Rewrite using `[Pi.lt_def]`. Use `⟨hmono', ?_⟩` and prove the remaining obligations. Establish `hex : ∃ j, j < k ∧ ∃ x ∈ B, x ∈ Vf (j + 1) ∧ x ∉ A`. Take `⟨x, hxB, hxA⟩` from `SetLike.exists_of_lt hAB`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[h0]`. Conclude with `hxA (by`. Establish `: x ∈ (⊤ : Submodule ℂ V)` using `trivial`. Rewrite `this` using `[← hk]`.

Rewrite using `[(Submodule.mem_bot ℂ).1 this]`. Conclude with `A.toSubmodule.zero_mem)`. Use `⟨k - 1, by omega, x, hxB, ?_, hxA⟩` and prove the remaining obligations. Rewrite using `[Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]`. Discharge the goal by the elementary cases of `trivial`.

Set `j₀` to `Nat.find hex`. Take `⟨hj₀k, x, hxB, hxV, hxA⟩` from `Nat.find_spec hex`. Establish `hbelow : ∀ y ∈ B, y ∈ Vf j₀ → y ∈ A`. Introduce `y hyB hyV`. Break down `Nat.eq_zero_or_pos j₀ with h | h` into its components or cases.

Rewrite `hyV` using `[h, h0]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hyV]`. Conclude with `A.toSubmodule.zero_mem`. Assume the negation of the conclusion as `hyA`. Take `⟨m, hm⟩ : ∃ m, j₀ = m + 1` from `⟨j₀ - 1, by omega⟩`.

Use `Nat.find_min hex (m := m) (by omega)` as an intermediate fact. Conclude with `this ⟨by omega, y, hyB, by rw [← hm]; exact hyV, hyA⟩`. Use `⟨⟨j₀, hj₀k⟩, lt_of_le_of_ne (hmono' _) fun heq => hxA ?_⟩` and prove the remaining obligations. Establish `hmem : Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ ∈ subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B)` using `⟨⟨x, hxV⟩, hxB, rfl⟩`. Establish `heq' : subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ A) = subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B)` using `heq`.

Rewrite `hmem` using `[← heq']`. Take `⟨y, hyA, hyx⟩` from `hmem`. Establish `hyx' : Ψ ⟨j₀, hj₀k⟩ y = Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩` using `hyx`. Establish `hd : Ψ ⟨j₀, hj₀k⟩ (⟨x, hxV⟩ - y) = 0` using `by rw [map_sub, hyx', sub_self]`. Rewrite `hd` using `[hΨ]`.

Establish `hyA' : (y : V) ∈ A` using `hyA`. Establish `hdB : ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) ∈ B` using `B.toSubmodule.sub_mem hxB (hAB.le hyA')`. Use `hbelow _ hdB hd` as an intermediate fact. Establish `hx' : x = ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) + y` using `by simp`. Rewrite using `[hx']`.

Conclude with `A.toSubmodule.add_mem this hyA'`.
-/
theorem hasFiniteLength_of_filtration {k : ℕ} (Vf : ℕ → Submodule ℂ V)
    (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥) (hk : Vf k = ⊤)
    {W : Fin k → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (σ : ∀ j, Representation ℂ G (W j))
    (Ψ : ∀ j : Fin k, Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)))
      (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) (hσ : ∀ j, HasFiniteLength (σ j)) :
    HasFiniteLength ρ := by
  classical
  have := fun j => (hσ j).wellFoundedLT
  have := fun j => (hσ j).wellFoundedGT

  let cut : ∀ j : Fin k, Subrepresentation ρ →
      Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) := fun j A =>
    ⟨A.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => A.apply_mem_toSubmodule g hx⟩
  refine hasFiniteLength_of_strictMono (α := fun j => Subrepresentation (σ j))
    (fun A j => subrepMap (Ψ j) (cut j A)) fun A B hAB => ?_
  have hmono' : ∀ j, subrepMap (Ψ j) (cut j A) ≤ subrepMap (Ψ j) (cut j B) := fun j =>
    subrepMap_mono _ (fun x hx => hAB.le hx)
  rw [Pi.lt_def]
  refine ⟨hmono', ?_⟩

  have hex : ∃ j, j < k ∧ ∃ x ∈ B, x ∈ Vf (j + 1) ∧ x ∉ A := by
    obtain ⟨x, hxB, hxA⟩ := SetLike.exists_of_lt hAB
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [h0] at hk
      exact hxA (by
        have : x ∈ (⊤ : Submodule ℂ V) := trivial
        rw [← hk] at this
        rw [(Submodule.mem_bot ℂ).1 this]
        exact A.toSubmodule.zero_mem)
    refine ⟨k - 1, by omega, x, hxB, ?_, hxA⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]
    trivial
  let j₀ := Nat.find hex
  obtain ⟨hj₀k, x, hxB, hxV, hxA⟩ := Nat.find_spec hex
  have hbelow : ∀ y ∈ B, y ∈ Vf j₀ → y ∈ A := by
    intro y hyB hyV
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, h0] at hyV
      rw [(Submodule.mem_bot ℂ).1 hyV]
      exact A.toSubmodule.zero_mem
    · by_contra hyA
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      have := Nat.find_min hex (m := m) (by omega)
      exact this ⟨by omega, y, hyB, by rw [← hm]; exact hyV, hyA⟩
  refine ⟨⟨j₀, hj₀k⟩, lt_of_le_of_ne (hmono' _) fun heq => hxA ?_⟩
  have hmem : Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ ∈ subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) :=
    ⟨⟨x, hxV⟩, hxB, rfl⟩
  have heq' : subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ A) =
      subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) := heq
  rw [← heq'] at hmem
  obtain ⟨y, hyA, hyx⟩ := hmem
  have hyx' : Ψ ⟨j₀, hj₀k⟩ y = Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ := hyx
  have hd : Ψ ⟨j₀, hj₀k⟩ (⟨x, hxV⟩ - y) = 0 := by rw [map_sub, hyx', sub_self]
  rw [hΨ] at hd
  have hyA' : (y : V) ∈ A := hyA
  have hdB : ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) ∈ B :=
    B.toSubmodule.sub_mem hxB (hAB.le hyA')
  have := hbelow _ hdB hd
  have hx' : x = ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) + y := by simp
  rw [hx']
  exact A.toSubmodule.add_mem this hyA'

end Filtration

end GroundTheory.Automorphic
