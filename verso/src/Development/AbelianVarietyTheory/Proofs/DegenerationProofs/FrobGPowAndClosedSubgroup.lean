import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.FrobSub

def Raises {X : Scheme.{0}} (φ : X ⟶ X) (n : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

/- English proof (translation)
Take `⟨e₁, p₁⟩` from `h₁`. Take `⟨e₂, p₂⟩` from `h₂`. Use `⟨by rw [Scheme.Hom.comp_preimage, ← e₂, ← e₁], ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.appLE_comp_appLE φ ψ U U U e₂.le e₁.le, CommRingCat.hom_comp, RingHom.comp_apply, p₂, map_pow, p₁, ← pow_mul]`.
-/
theorem Raises.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {a b : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (h₁ : Raises φ a U f) (h₂ : Raises ψ b U f) : Raises (φ ≫ ψ) (a * b) U f := by
  obtain ⟨e₁, p₁⟩ := h₁
  obtain ⟨e₂, p₂⟩ := h₂
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e₂, ← e₁], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e₂.le e₁.le, CommRingCat.hom_comp, RingHom.comp_apply, p₂,
    map_pow, p₁, ← pow_mul]

/- English proof (translation)
Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => rwa [Nat.mul_one]`. Consider the case `succ n hn ih`. Use `h.comp ih` as an intermediate fact. Rewrite using `[Nat.mul_succ, pow_add, pow_add, mul_comm (q ^ (m * n))]`.

Conclude with `this`.
-/
theorem Raises.mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) {U : G.left.Opens} {f : Γ(G.left, U)}
    (h : Raises (show G ⟶ G from F ^ m).left (q ^ m) U f) (n : ℕ) (hn : 1 ≤ n) :
    Raises (show G ⟶ G from F ^ (m * n)).left (q ^ (m * n)) U f := by
  induction n, hn using Nat.le_induction with
  | base => rwa [Nat.mul_one]
  | succ n hn ih =>
    have := h.comp ih
    rw [Nat.mul_succ, pow_add, pow_add, mul_comm (q ^ (m * n))]
    exact this

/- English proof (translation)
Take `⟨e, p⟩` from `h`. Establish `e' : ν ⁻¹ᵁ V = ψ ⁻¹ᵁ ν ⁻¹ᵁ V`. Rewrite using `[← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage, ← e]`. Use `⟨e', ?_⟩` and prove the remaining obligations. Establish `k : ∀ (θ θ' : Y ⟶ X) (_ : θ = θ') h h', θ.appLE V (ν ⁻¹ᵁ V) h = θ'.appLE V (ν ⁻¹ᵁ V) h'`.

Introduce and unpack `_ _ rfl _ _`. Both sides reduce to the same expression. Establish `k2 : ν.appLE V (ν ⁻¹ᵁ V) le_rfl ≫ ψ.appLE _ _ e'.le = φ.appLE V V e.le ≫ ν.appLE V (ν ⁻¹ᵁ V) le_rfl`. Rewrite using `[Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]`. Conclude with `k _ _ hc _ _`.

Rewrite using `[Scheme.Hom.app_eq_appLE]`. Use `congrArg (fun t => t.hom g) k2` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Rewrite using `[this, p, map_pow]`.
-/
theorem Raises.pull {X Y : Scheme.{0}} (ν : Y ⟶ X) {φ : X ⟶ X} {ψ : Y ⟶ Y} (hc : ψ ≫ ν = ν ≫ φ) {a : ℕ}
    {V : X.Opens} {g : Γ(X, V)} (h : Raises φ a V g) : Raises ψ a (ν ⁻¹ᵁ V) ((ν.app V).hom g) := by
  obtain ⟨e, p⟩ := h
  have e' : ν ⁻¹ᵁ V = ψ ⁻¹ᵁ ν ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage, ← e]
  refine ⟨e', ?_⟩
  have k : ∀ (θ θ' : Y ⟶ X) (_ : θ = θ') h h', θ.appLE V (ν ⁻¹ᵁ V) h = θ'.appLE V (ν ⁻¹ᵁ V) h' := by
    rintro _ _ rfl _ _; rfl
  have k2 : ν.appLE V (ν ⁻¹ᵁ V) le_rfl ≫ ψ.appLE _ _ e'.le =
      φ.appLE V V e.le ≫ ν.appLE V (ν ⁻¹ᵁ V) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact k _ _ hc _ _
  rw [Scheme.Hom.app_eq_appLE]
  have := congrArg (fun t => t.hom g) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this, p, map_pow]

/- English proof (translation)
Establish `hU' : U = iSup V` using `le_antisymm hU (iSup_le hV)`. Establish `e : U = φ ⁻¹ᵁ U`. Rewrite using `[hU', Scheme.Hom.preimage_iSup]`. Conclude with `iSup_congr fun i => (h i).1`. Use `⟨e, ?_⟩` and prove the remaining obligations.

Use `X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hU _ _ fun i => ?_` and prove the remaining obligations. Take `⟨e', p⟩` from `h i`. Establish `k2 : φ.appLE U U e.le ≫ X.presheaf.map (homOfLE (hV i)).op = X.presheaf.map (homOfLE (hV i)).op ≫ φ.appLE _ _ e'.le`. Rewrite using `[Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`. Use `congrArg (fun t => t.hom f) k2` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Conclude with `this.trans (p.trans (map_pow _ _ _).symm)`.
-/
theorem Raises.of_cover {X : Scheme.{0}} {φ : X ⟶ X} {a : ℕ} {U : X.Opens} {f : Γ(X, U)} {I : Type}
    (V : I → X.Opens) (hV : ∀ i, V i ≤ U) (hU : U ≤ iSup V)
    (h : ∀ i, Raises φ a (V i) ((X.presheaf.map (homOfLE (hV i)).op).hom f)) : Raises φ a U f := by
  have hU' : U = iSup V := le_antisymm hU (iSup_le hV)
  have e : U = φ ⁻¹ᵁ U := by
    rw [hU', Scheme.Hom.preimage_iSup]
    exact iSup_congr fun i => (h i).1
  refine ⟨e, ?_⟩
  refine X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hU _ _ fun i => ?_
  obtain ⟨e', p⟩ := h i
  have k2 : φ.appLE U U e.le ≫ X.presheaf.map (homOfLE (hV i)).op =
      X.presheaf.map (homOfLE (hV i)).op ≫ φ.appLE _ _ e'.le := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have := congrArg (fun t => t.hom f) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.trans (p.trans (map_pow _ _ _).symm)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Simplify using `only [pow_succ, End.mul_def, Category.assoc] at *`. Rewrite using `[ih, reassoc_of% h]`.
-/
theorem pow_comm_hom {C : Type*} [Category C] {N G : C} (ν : N ⟶ G) (F : End G) (F' : End N)
    (h : (show N ⟶ N from F') ≫ ν = ν ≫ (show G ⟶ G from F)) (m : ℕ) :
    (show N ⟶ N from F' ^ m) ≫ ν = ν ≫ (show G ⟶ G from F ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ, End.mul_def, Category.assoc] at *
    rw [ih, reassoc_of% h]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact inferInstanceAs (IsMonHom (𝟙 G))`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Conclude with `inferInstanceAs (IsMonHom ((show G ⟶ G from F) ≫ (show G ⟶ G from F ^ m)))`.
-/
theorem isMonHom_pow {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G)
    (h : IsMonHom (show G ⟶ G from F)) (m : ℕ) : IsMonHom (show G ⟶ G from F ^ m) := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 G))
  | succ m ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom ((show G ⟶ G from F) ≫ (show G ⟶ G from F ^ m)))

end GlobalTheory.SS.FrobSub

open GlobalTheory.SS.FrobSub in

/- English proof (translation)
Introduce `k _ G _ _ F q hF`. Use `⟨fun m hm => ⟨isMonHom_pow G F hF.1 m, fun U hU f => ?_⟩, fun N _ ν F' _ hν hF' hc => ⟨hF', fun U hU f => ?_⟩⟩` and prove the remaining obligations. Take `⟨n, hn, h⟩` from `hF.2 U hU f`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Use `Raises.mul F q n h m hm` as an intermediate fact.

Rewrite `this` using `[mul_comm, pow_mul, pow_mul]`. Conclude with `this`. Establish `key : ∀ x : U, ∃ (W : N.left.Opens) (hW : W ≤ U) (m : ℕ), x.1 ∈ W ∧ 1 ≤ m ∧ Raises (show N ⟶ N from F' ^ m).left (q ^ m) W ((N.left.presheaf.map (homOfLE hW).op).hom f)`. Introduce `x`. Take `⟨W, hW, hWU⟩` from `ν.left.isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen`.

Establish `hx : ν.left x.1 ∈ (⟨W, hW⟩ : G.left.Opens)` using `by show x.1 ∈ ν.left ⁻¹' W`. Rewrite using `[hWU]`. Conclude with `x.2`. Take `⟨V, hV, hxV, hVW⟩` from `exists_isAffineOpen_mem_and_subset hx`. Establish `hle : ν.left ⁻¹ᵁ V ≤ U` using `fun y hy => by`.

Establish `: y ∈ ν.left ⁻¹' W` using `hVW hy`. Rewrite `this` using `[hWU]`. Then use the resulting hypothesis. Take `⟨g, hg⟩` from `ν.left.app_surjective V hV ((N.left.presheaf.map (homOfLE hle).op).hom f)`. Take `⟨m, hm, h⟩` from `hF.2 V hV g`. Use `⟨_, hle, m, hxV, hm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hg]`. Use `Raises.pull ν.left ?_ h` and prove the remaining obligations. Conclude with `congrArg (fun t => t.left) (pow_comm_hom ν F F' hc m)`. Use `choose W hW m hxW hm hR using key`. Take `⟨t, ht⟩` from `hU.isCompact.elim_finite_subcover (fun x => (W x : Set N.left)) (fun x => (W x).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩)`.

Establish `hpos : 1 ≤ ∏ x ∈ t, m x` using `Finset.one_le_prod' fun x _ => hm x`. Use `⟨∏ x ∈ t, m x, hpos, ?_⟩` and prove the remaining obligations. Use `Raises.of_cover (fun x : t => W x.1) (fun x => hW x.1) (fun y hy => ?_) fun x => ?_` and prove the remaining obligations. Take `⟨x, hx, hy'⟩` from `Set.mem_iUnion₂.1 (ht hy)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy'⟩`.

Take `⟨n, hn⟩` from `Finset.dvd_prod_of_mem m x.2`. Establish `hn1 : 1 ≤ n` using `Nat.pos_of_ne_zero fun h0 => by rw [hn, h0] at hpos; simp at hpos`. Rewrite using `[hn]`. Conclude with `Raises.mul F' q _ (hR x.1) n hn1`.
-/
theorem GlobalTheory.SS.frobG_pow_and_closed_subgroup : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → (∀ m, 1 ≤ m → FrobG G (F ^ m) (q ^ m)) ∧ ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (F' : End N), IsMonHom ν → IsClosedImmersion ν.left → IsMonHom (show N ⟶ N from F') → (show N ⟶ N from F') ≫ ν = ν ≫ (show G ⟶ G from F) → FrobG N F' q := by
  intro k _ G _ _ F q hF
  refine ⟨fun m hm => ⟨isMonHom_pow G F hF.1 m, fun U hU f => ?_⟩, fun N _ ν F' _ hν hF' hc => ⟨hF', fun U hU f => ?_⟩⟩
  · obtain ⟨n, hn, h⟩ := hF.2 U hU f
    refine ⟨n, hn, ?_⟩
    have := Raises.mul F q n h m hm
    rw [mul_comm, pow_mul, pow_mul] at this
    exact this
  · have key : ∀ x : U, ∃ (W : N.left.Opens) (hW : W ≤ U) (m : ℕ), x.1 ∈ W ∧ 1 ≤ m ∧
        Raises (show N ⟶ N from F' ^ m).left (q ^ m) W ((N.left.presheaf.map (homOfLE hW).op).hom f) := by
      intro x
      obtain ⟨W, hW, hWU⟩ := ν.left.isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
      have hx : ν.left x.1 ∈ (⟨W, hW⟩ : G.left.Opens) := by
        show x.1 ∈ ν.left ⁻¹' W
        rw [hWU]; exact x.2
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
      have hle : ν.left ⁻¹ᵁ V ≤ U := fun y hy => by
        have : y ∈ ν.left ⁻¹' W := hVW hy
        rwa [hWU] at this
      obtain ⟨g, hg⟩ := ν.left.app_surjective V hV ((N.left.presheaf.map (homOfLE hle).op).hom f)
      obtain ⟨m, hm, h⟩ := hF.2 V hV g
      refine ⟨_, hle, m, hxV, hm, ?_⟩
      rw [← hg]
      refine Raises.pull ν.left ?_ h
      exact congrArg (fun t => t.left) (pow_comm_hom ν F F' hc m)
    choose W hW m hxW hm hR using key
    obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover (fun x => (W x : Set N.left)) (fun x => (W x).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩)
    have hpos : 1 ≤ ∏ x ∈ t, m x := Finset.one_le_prod' fun x _ => hm x
    refine ⟨∏ x ∈ t, m x, hpos, ?_⟩
    refine Raises.of_cover (fun x : t => W x.1) (fun x => hW x.1) (fun y hy => ?_) fun x => ?_
    · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy'⟩
    · obtain ⟨n, hn⟩ := Finset.dvd_prod_of_mem m x.2
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by rw [hn, h0] at hpos; simp at hpos
      rw [hn]
      exact Raises.mul F' q _ (hR x.1) n hn1
