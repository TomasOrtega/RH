import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

noncomputable section

namespace GlobalTheory.Shin

open Polynomial GlobalTheory.CuspGL
open scoped Classical

def nrmG {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ) (l : ℕ) (δ : G) : G :=
  ((List.range l).map fun i => φ (s ^ i) δ).prod

def Kills {G : Type} [Group G] (φ Y : G → ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
    ∑ᶠ g, star (Y g) * LinearMap.trace ℂ V (ρ g) = 0 → ∑ᶠ g, star (φ g) • ρ g = 0

def KillsIrr {G : Type} [Group G] [Finite G] (φ Y : G → ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible →
    ∑ᶠ g, star (Y g) * LinearMap.trace ℂ V (ρ g) = 0 → ∑ᶠ g, star (φ g) • ρ g = 0

/- English proof (translation)
Introduce `V _ _ _ ρ _ hρ` and use `h V ρ hρ`.
-/
theorem Kills.killsIrr {G : Type} [Group G] [Finite G] {φ Y : G → ℂ} (h : Kills φ Y) : KillsIrr φ Y :=
  fun V _ _ _ ρ _ hρ => h V ρ hρ

namespace IsoPart

def conjRep {G : Type} [Group G] {n : ℕ} (σ : Representation ℂ G (Fin n → ℂ)) : Representation ℂ G (Fin n → ℂ) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (σ g)).map (starRingEnd ℂ))
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
  map_mul' g h := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul,
      Module.End.mul_eq_comp]

/- English proof (translation)
Establish `h : ∀ A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ), LinearMap.trace ℂ _ A = (LinearMap.toMatrix' A).trace` using `fun A => by`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']`. Unfold `Representation.character`. Rewrite using `[h, h]`. Simplify using `[conjRep, Matrix.trace]`.
-/
theorem character_conjRep {G : Type} [Group G] {n : ℕ} (σ : Representation ℂ G (Fin n → ℂ)) (g : G) :
    (conjRep σ).character g = star (σ.character g) := by
  have h : ∀ A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ), LinearMap.trace ℂ _ A = (LinearMap.toMatrix' A).trace := fun A => by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
  unfold Representation.character
  rw [h, h]
  simp [conjRep, Matrix.trace]

/- English proof (translation)
Establish `: Fintype G` using `Fintype.ofFinite G`. Take `⟨n, σ, hσ⟩` from `hY`. Establish `hst : ∀ g, star (Y g) = (conjRep σ).dual.character g⁻¹` using `fun g => by`. Rewrite using `[Representation.char_dual, inv_inv, character_conjRep, hσ]`. Simplify using the standard rewrite rules.

Establish `hne : (Nat.card G : ℂ) ≠ 0`. Establish `: 0 < Nat.card G` using `Nat.card_pos`. Conclude with `this.ne'` after adjusting the coercions. Establish `hinv : Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero hne`. Rewrite `h`, the goal using `[finsum_eq_sum_of_fintype]`.

Simplify using `only [hst] at h ⊢`. Establish `h1` using `Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom (conjRep σ).dual ρ)`. Establish `h2` using `Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom (conjRep σ).dual A.toRepresentation)`. Simplify using `only [Representation.char_linHom] at h1 h2`. Establish `h' : ∑ g : G, (conjRep σ).dual.character g⁻¹ * ρ.character g = 0` using `h`.

Rewrite `h1` using `[h', mul_zero]`. Establish `hbot : (Representation.linHom (conjRep σ).dual ρ).invariants = ⊥`. Apply `Submodule.finrank_eq_zero.mp` to reduce the goal to its premises. Conclude with `h1.symm` after adjusting the coercions. Establish `hbot' : (Representation.linHom (conjRep σ).dual A.toRepresentation).invariants = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `f hf`. Establish `hm : A.toSubmodule.subtype ∘ₗ f ∈ (Representation.linHom (conjRep σ).dual ρ).invariants`. Introduce `g`. Use `ext1 x`.

Use `congrArg (fun F => ((F x : A.toSubmodule) : V)) (hf g)` as an intermediate fact. Conclude with `this`. Rewrite `hm` using `[hbot, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Use extensionality with `x`.

Conclude with `congrArg (fun F => F x) hm`. Rewrite `h2` using `[hbot', finrank_bot, Nat.cast_zero]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (by simpa using hne)`.
-/
theorem orth_subrepresentation {G : Type} [Group G] [Finite G] {Y : G → ℂ} (hY : GlobalTheory.BI.IsChar ℂ ℂ Y)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : ∑ᶠ g, star (Y g) * LinearMap.trace ℂ V (ρ g) = 0) (A : Subrepresentation ρ) :
    ∑ᶠ g, star (Y g) * LinearMap.trace ℂ A.toSubmodule (A.toRepresentation g) = 0 := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, σ, hσ⟩ := hY
  have hst : ∀ g, star (Y g) = (conjRep σ).dual.character g⁻¹ := fun g => by
    rw [Representation.char_dual, inv_inv, character_conjRep, hσ]; simp
  have hne : (Nat.card G : ℂ) ≠ 0 := by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne'
  have hinv : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hne
  rw [finsum_eq_sum_of_fintype] at h ⊢
  simp only [hst] at h ⊢
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom (conjRep σ).dual ρ)
  have h2 := Representation.card_inv_mul_sum_char_eq_finrank
    (Representation.linHom (conjRep σ).dual A.toRepresentation)
  simp only [Representation.char_linHom] at h1 h2
  have h' : ∑ g : G, (conjRep σ).dual.character g⁻¹ * ρ.character g = 0 := h
  rw [h', mul_zero] at h1
  have hbot : (Representation.linHom (conjRep σ).dual ρ).invariants = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast h1.symm
  have hbot' : (Representation.linHom (conjRep σ).dual A.toRepresentation).invariants = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    have hm : A.toSubmodule.subtype ∘ₗ f ∈ (Representation.linHom (conjRep σ).dual ρ).invariants := by
      intro g
      ext1 x
      have := congrArg (fun F => ((F x : A.toSubmodule) : V)) (hf g)
      exact this
    rw [hbot, Submodule.mem_bot] at hm
    rw [Submodule.mem_bot]
    ext x
    exact congrArg (fun F => F x) hm
  rw [hbot', finrank_bot, Nat.cast_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_left (by simpa using hne)

/- English proof (translation)
Establish `hex : ∃ d, ∃ A : Subrepresentation ρ, A.toSubmodule ≠ ⊥ ∧ A.toSubmodule ≤ C.toSubmodule ∧ Module.finrank ℂ A.toSubmodule = d` using `⟨_, C, hC, le_rfl, rfl⟩`. Take `⟨A, hA, hAC, hd⟩` from `Nat.find_spec hex`. Use `⟨A, hA, hAC, ?_⟩` and prove the remaining obligations. Establish `hnt : Nontrivial A.toSubmodule` using `Submodule.nontrivial_iff_ne_bot.2 hA`. Establish `: Nontrivial (Subrepresentation A.toRepresentation)` using `⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ A.toSubmodule) (congrArg Subrepresentation.toSubmodule h)⟩`.

Use `⟨fun S => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hS : S.toSubmodule = ⊥`. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective hS)`. Use `right`. Set `B : Subrepresentation ρ` to `⟨S.toSubmodule.map A.toSubmodule.subtype, by`.

Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Conclude with `⟨A.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩⟩`. Establish `hB : B.toSubmodule ≠ ⊥` using `fun h => hS (by`. Establish `h' : S.toSubmodule.map A.toSubmodule.subtype = ⊥` using `h`. Rewrite using `[← Submodule.comap_map_eq_of_injective A.toSubmodule.injective_subtype S.toSubmodule, h', Submodule.comap_bot, Submodule.ker_subtype])`.

Establish `hle` using `Nat.find_min' hex ⟨B, hB, (Submodule.map_subtype_le _ _).trans hAC, rfl⟩`. Establish `hfr : Module.finrank ℂ B.toSubmodule = Module.finrank ℂ S.toSubmodule` using `Submodule.finrank_map_subtype_eq _ _`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Conclude with `le_antisymm (Submodule.finrank_le _) (by omega)`.
-/
theorem exists_irreducible_le {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (C : Subrepresentation ρ) (hC : C.toSubmodule ≠ ⊥) :
    ∃ A : Subrepresentation ρ, A.toSubmodule ≠ ⊥ ∧ A.toSubmodule ≤ C.toSubmodule ∧
      A.toRepresentation.IsIrreducible := by
  have hex : ∃ d, ∃ A : Subrepresentation ρ, A.toSubmodule ≠ ⊥ ∧ A.toSubmodule ≤ C.toSubmodule ∧
      Module.finrank ℂ A.toSubmodule = d := ⟨_, C, hC, le_rfl, rfl⟩
  obtain ⟨A, hA, hAC, hd⟩ := Nat.find_spec hex
  refine ⟨A, hA, hAC, ?_⟩
  have hnt : Nontrivial A.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hA
  have : Nontrivial (Subrepresentation A.toRepresentation) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ A.toSubmodule) (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    let B : Subrepresentation ρ := ⟨S.toSubmodule.map A.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨A.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hB : B.toSubmodule ≠ ⊥ := fun h => hS (by
      have h' : S.toSubmodule.map A.toSubmodule.subtype = ⊥ := h
      rw [← Submodule.comap_map_eq_of_injective A.toSubmodule.injective_subtype S.toSubmodule, h',
        Submodule.comap_bot, Submodule.ker_subtype])
    have hle := Nat.find_min' hex ⟨B, hB, (Submodule.map_subtype_le _ _).trans hAC, rfl⟩
    have hfr : Module.finrank ℂ B.toSubmodule = Module.finrank ℂ S.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) (by omega)

end IsoPart

/- English proof (translation)
Use `⟨Kills.killsIrr, fun H V _ _ _ ρ h => ?_⟩` and prove the remaining obligations. Establish `: Fintype G` using `Fintype.ofFinite G`. Establish `: NeZero (Nat.card G : ℂ)` using `⟨by`. Establish `: 0 < Nat.card G` using `Nat.card_pos`. Conclude with `this.ne'⟩` after adjusting the coercions.

Use `set T : V →ₗ[ℂ] V := ∑ᶠ g, star (φ g) • ρ g with hT`. Set `N : Subrepresentation ρ` to `⟨⨅ g : G, LinearMap.ker (T ∘ₗ ρ g), by`. Introduce `g v hv`. Rewrite `hv`, the goal using `[Submodule.mem_iInf]`. Introduce `x`.

Use `hv (x * g)` as an intermediate fact. Simplify using `using this⟩`. Take `⟨C, hC⟩` from `exists_isCompl N`. Establish `hCb : C.toSubmodule = ⊥`. Assume the negation of the conclusion as `hne`.

Take `⟨A, hA, hAC, hirr⟩` from `IsoPart.exists_irreducible_le ρ C hne`. Establish `h0` using `H _ A.toRepresentation hirr (IsoPart.orth_subrepresentation hY ρ h A)`. Establish `hAN : A.toSubmodule ≤ N.toSubmodule`. Introduce `v hv`. Use `(Submodule.mem_iInf _).2 fun x => ?_` and prove the remaining obligations.

Use `congrArg (fun F => ((F ⟨ρ x v, A.apply_mem_toSubmodule x hv⟩ : A.toSubmodule) : V)) h0` as an intermediate fact. Rewrite using `[LinearMap.mem_ker, hT]`. Rewrite `this`, the goal using `[finsum_eq_sum_of_fintype]`. Simplify `this` using `[LinearMap.sum_apply, Subrepresentation.toRepresentation]`. Establish `hd : N.toSubmodule ⊓ C.toSubmodule = ⊥` using `congrArg Subrepresentation.toSubmodule hC.inf_eq_bot`.

Conclude with `hA (eq_bot_iff.2 (hd ▸ le_inf hAN hAC))`. Establish `hs : N.toSubmodule ⊔ C.toSubmodule = ⊤` using `congrArg Subrepresentation.toSubmodule hC.sup_eq_top`. Rewrite `hs` using `[hCb, sup_bot_eq]`. Use extensionality with `v`. Establish `hv : v ∈ N.toSubmodule` using `hs ▸ Submodule.mem_top`.

Simplify using `using (Submodule.mem_iInf _).1 hv 1`.
-/
theorem kills_iff_killsIrr {G : Type} [Group G] [Finite G] (φ : G → ℂ) {Y : G → ℂ} (hY : GlobalTheory.BI.IsChar ℂ ℂ Y) :
    Kills φ Y ↔ KillsIrr φ Y := by
  refine ⟨Kills.killsIrr, fun H V _ _ _ ρ h => ?_⟩
  have : Fintype G := Fintype.ofFinite G
  have : NeZero (Nat.card G : ℂ) := ⟨by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne'⟩
  set T : V →ₗ[ℂ] V := ∑ᶠ g, star (φ g) • ρ g with hT
  let N : Subrepresentation ρ := ⟨⨅ g : G, LinearMap.ker (T ∘ₗ ρ g), by
    intro g v hv
    rw [Submodule.mem_iInf] at hv ⊢
    intro x
    have := hv (x * g)
    simpa using this⟩
  obtain ⟨C, hC⟩ := exists_isCompl N
  have hCb : C.toSubmodule = ⊥ := by
    by_contra hne
    obtain ⟨A, hA, hAC, hirr⟩ := IsoPart.exists_irreducible_le ρ C hne
    have h0 := H _ A.toRepresentation hirr (IsoPart.orth_subrepresentation hY ρ h A)
    have hAN : A.toSubmodule ≤ N.toSubmodule := by
      intro v hv
      refine (Submodule.mem_iInf _).2 fun x => ?_
      have := congrArg (fun F => ((F ⟨ρ x v, A.apply_mem_toSubmodule x hv⟩ : A.toSubmodule) : V)) h0
      rw [LinearMap.mem_ker, hT]
      rw [finsum_eq_sum_of_fintype] at this ⊢
      simpa [LinearMap.sum_apply, Subrepresentation.toRepresentation] using this
    have hd : N.toSubmodule ⊓ C.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hC.inf_eq_bot
    exact hA (eq_bot_iff.2 (hd ▸ le_inf hAN hAC))
  have hs : N.toSubmodule ⊔ C.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hC.sup_eq_top
  rw [hCb, sup_bot_eq] at hs
  ext v
  have hv : v ∈ N.toSubmodule := hs ▸ Submodule.mem_top
  simpa using (Submodule.mem_iInf _).1 hv 1

def IsCl {G : Type} [Group G] (f : G → ℂ) : Prop := ∀ x y : G, f (y⁻¹ * x * y) = f x

def Reg (q m k : ℕ) : Prop := ∀ i : ℕ, 0 < i → i < m → ¬ k * q ^ i ≡ k [MOD q ^ m - 1]

section OneField

variable {F : Type} [Field F]

def ent {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) : F :=
  if h : i < n ∧ j < n then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def tl (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin a) (Fin a) F := fun i j => ent M i j

def br (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin b) (Fin b) F :=
  fun i j => ent M (a + i) (a + j)

def InPar (a : ℕ) {n : ℕ} (x : GL (Fin n) F) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (x : Matrix (Fin n) (Fin n) F) i j = 0

def toG {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : GL (Fin n) F := if h : IsUnit M then h.unit else 1

def tlG (a : ℕ) {n : ℕ} (x : GL (Fin n) F) : GL (Fin a) F := toG (tl a (x : Matrix (Fin n) (Fin n) F))

def brG (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) : GL (Fin b) F := toG (br a b (x : Matrix (Fin n) (Fin n) F))

def gal {F' : Type} [Field F'] (t : F →+* F') (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  Matrix.GeneralLinearGroup.map t

def hcTw (t : F →+* F) (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  fun x => (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
    ∑ᶠ y : GL (Fin n) F, if InPar a (y⁻¹ * x * gal t n y) then
      α (tlG a (y⁻¹ * x * gal t n y)) * β (brG a b (y⁻¹ * x * gal t n y)) else 0

def hc (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  hcTw (RingHom.id F) a b α β n

def psiG (S : F[X] → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  fun x => psi S (Fin n → F) (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F))

def chG (S : F[X] → ℂ) (n : ℕ) : GL (Fin n) F → ℂ := fun x => S (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))

def cusp (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) : GL (Fin m) F → ℂ :=
  fun x => (-1) ^ (m - 1) * psiG (rootSum θ k) m x

def deg (L : List (ℕ × ℕ)) : ℕ := (L.map Prod.fst).sum

def J (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) : (n : ℕ) → GL (Fin n) F → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → GL (Fin n) F → ℂ) (fun _ _ => 1)
    (fun p L ih n => hc p.1 (deg L) (cusp θ p.1 p.2) (ih (deg L)) n) L

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem J_nil (θ : AlgebraicClosure F →* ℂ) (n : ℕ) : J θ [] n = fun _ => 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem J_cons (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) (n : ℕ) :
    J θ (p :: L) n = hc p.1 (deg L) (cusp θ p.1 p.2) (J θ L (deg L)) n := rfl

def HFree {n : ℕ} (Y : GL (Fin n) F → ℂ) : Prop :=
  0 < n → ∑ᶠ x ∈ {x : GL (Fin n) F | ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j}, Y x = 0

end OneField

section TwoFields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

def galAct (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) :
    (F' ≃ₐ[F] F') →* MulAut (GL (Fin n) F') where
  toFun t :=
    { toFun := gal (t : F' →+* F') n
      invFun := gal (t.symm : F' →+* F') n
      left_inv := fun x => by ext i j; simp [gal]
      right_inv := fun x => by ext i j; simp [gal]
      map_mul' := fun x y => map_mul _ x y }
  map_one' := by ext x i j; simp [gal]
  map_mul' s t := by ext x i j; simp [gal]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem galAct_apply (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    galAct F F' n t x = gal (t : F' →+* F') n x := rfl

def incl (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  gal (algebraMap F F') n

def nrm (s : F' ≃ₐ[F] F') {n : ℕ} (δ : GL (Fin n) F') : GL (Fin n) F' :=
  nrmG (galAct F F' n) s (Module.finrank F F') δ

def IsNorm (s : F' ≃ₐ[F] F') {n : ℕ} (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (incl F F' n γ) (nrm s δ)

def shLift (s : F' ≃ₐ[F] F') {n : ℕ} (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsNorm s δ γ then f h.choose else 0

abbrev GHat (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) : Type :=
  GL (Fin n) F' ⋊[galAct F F' n] (F' ≃ₐ[F] F')

def pullθ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) :
    AlgebraicClosure F →* ℂ := θ.comp (ι : AlgebraicClosure F →* AlgebraicClosure F')

end TwoFields

def liftL (q l : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.flatMap fun p => (List.range l).map fun i => (p.1 / l, p.2 * q ^ i)

def liftAll (q l : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.flatMap fun p => if l ∣ p.1 then liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]

/- English proof (translation)
Establish `: nrm s (1 : GL (Fin n) F') = 1`. Unfold `nrm nrmG`. Apply `List.prod_eq_one` to reduce the goal to its premises. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `map_one _`. Unfold `IsNorm`. Rewrite using `[this, map_one]`.
-/
theorem isNorm_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (n : ℕ) :
    IsNorm s (1 : GL (Fin n) F') (1 : GL (Fin n) F) := by
  have : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact map_one _
  unfold IsNorm
  rw [this, map_one]

/- English proof (translation)
Introduce `h`. Establish `h1` using `h ℂ (Representation.trivial ℂ ℤˣ ℂ) (by`. Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `[UnitsInt.univ])`. Rewrite `h1` using `[finsum_eq_sum_of_fintype]`.

Establish `h2` using `congrArg (fun F : ℂ →ₗ[ℂ] ℂ => F 1) h1`. Simplify using `[UnitsInt.univ] at h2`.
-/
example : ¬ Kills (fun _ : ℤˣ => (1 : ℂ)) (fun g => ((g : ℤ) : ℂ)) := by
  intro h
  have h1 := h ℂ (Representation.trivial ℂ ℤˣ ℂ) (by
    rw [finsum_eq_sum_of_fintype]
    simp [UnitsInt.univ])
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 := congrArg (fun F : ℂ →ₗ[ℂ] ℂ => F 1) h1
  simp [UnitsInt.univ] at h2

/- English proof (translation)
Introduce `h`. Apply the tactic sequence `let ρ : Representation ℂ ℤˣ (ℂ × ℂ) := { toFun := fun g => LinearMap.prodMap LinearMap.id (((g : ℤ) : ℂ) • LinearMap.id) map_one' := by ext <;> simp map_mul' := fun g k => by ext <;> simp [mul_comm] }`. Establish `hρ : ∀ g : ℤˣ, ρ g = LinearMap.prodMap LinearMap.id (((g : ℤ) : ℂ) • LinearMap.id)` using `fun _ => rfl`. Establish `h1` using `h (ℂ × ℂ) ρ (by`. Rewrite using `[finsum_eq_sum_of_fintype]`.

Simplify using `[UnitsInt.univ, hρ, LinearMap.trace_prodMap'])`. Rewrite `h1` using `[finsum_eq_sum_of_fintype]`. Establish `h2` using `congrArg (fun F : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) => (F (1, 0)).1) h1`. Simplify using `[UnitsInt.univ, hρ] at h2`.
-/
example : ¬ Kills (fun g : ℤˣ => 1 - ((g : ℤ) : ℂ)) (fun g => 1 - ((g : ℤ) : ℂ)) := by
  intro h
  let ρ : Representation ℂ ℤˣ (ℂ × ℂ) :=
    { toFun := fun g => LinearMap.prodMap LinearMap.id (((g : ℤ) : ℂ) • LinearMap.id)
      map_one' := by ext <;> simp
      map_mul' := fun g k => by ext <;> simp [mul_comm] }
  have hρ : ∀ g : ℤˣ, ρ g = LinearMap.prodMap LinearMap.id (((g : ℤ) : ℂ) • LinearMap.id) := fun _ => rfl
  have h1 := h (ℂ × ℂ) ρ (by
    rw [finsum_eq_sum_of_fintype]
    simp [UnitsInt.univ, hρ, LinearMap.trace_prodMap'])
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 := congrArg (fun F : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) => (F (1, 0)).1) h1
  simp [UnitsInt.univ, hρ] at h2

/- English proof (translation)
Unfold `Reg`. Introduce `i h1 h2`. Use `interval_cases i`. Evaluate the decidable proposition.
-/
example : Reg 2 2 1 := by unfold Reg; intro i h1 h2; interval_cases i; decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
example : liftAll 5 2 [(2, 1), (3, 2)] = [(1, 1), (1, 5), (3, 2 * (1 + 125))] := by decide

end GlobalTheory.Shin

end
