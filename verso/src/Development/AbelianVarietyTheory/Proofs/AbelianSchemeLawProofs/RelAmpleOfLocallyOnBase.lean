import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOneAddKill

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AmpleLocal

variable {X Y Z : Scheme.{0}}

def Pack {ι : Type} (U : ι → Z.Opens) (G : ι → Fn Z) (W : Z.Opens) (S : Set (Fn Z)) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → Fn Z, ∃ D : Fin (M + 1) → Z.Opens, (∀ j, Sc U G W N (s j)) ∧
    (∀ j, IsLoc (D j) W (s j)) ∧ (∀ z ∈ W, ∃ j, z ∈ D j) ∧ (∀ j, IsAffineOpen (D j)) ∧
    ∀ j, Gen (D j) (S ∪ Set.range fun m => s m * inv (s j))

/- English proof (translation)
Use `Fintype.ofFinite Λ` as an intermediate fact. Use `choose N hN M s D hs hD cov aff gen using H`. Establish `hd : ∀ l, ∃ d, ∏ l, N l = N l * (d + 1)` using `fun l => by`. Take `⟨e, he⟩` from `Finset.dvd_prod_of_mem N (Finset.mem_univ l)`. Establish `: 0 < ∏ l, N l` using `Finset.prod_pos fun l _ => hN l`.

Consider the cases of `e with`. Consider the case `zero => omega`. Consider the case `succ e => exact ⟨e, he⟩`. Use `choose d hd using hd`. Set `T` to `Σ l, Fin (M l + 1) × Fin (M l + 1)`.

Establish `hsc : ∀ t : T, Sc U G (W t.1) (∏ l, N l) (s t.1 t.2.2 * s t.1 t.2.1 ^ d t.1)` using `fun t => by`. Rewrite using `[hd t.1, mul_add, mul_one, add_comm]`. Conclude with `(hs _ _).mul ((hs _ _).pow _)`. Use `choose k σ hσ eσ using fun t : T => (hsc t).extend hU hG hT (hφ _) (hW t.1)`. Establish `covW : ∀ z, ∃ l, z ∈ W l` using `fun z => by`.

Assume the negation of the conclusion as `hn`. Establish `: Ideal.span (Set.range a) ≤ (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)).comap ((Pi.evalRingHom _ z).comp φ)` using `Ideal.span_le.2 (by`. Introduce and unpack `_ ⟨l, rfl⟩ hu`. Conclude with `hn ⟨l, (hW l z).2 ⟨trivial, hu⟩⟩)`. Rewrite `this` using `[ha, top_le_iff, Ideal.comap_eq_top_iff]`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top this`. Establish `main : ∀ τ, Sc U G ⊤ (∏ l, N l) τ → ∀ E, IsLoc E ⊤ τ → IsAffineOpen E ∧ Gen E (Set.range φ ∪ Set.range fun m => σ m * inv τ)`. Introduce `τ hτ E hE`. Set `B` to `Subring.closure (Set.range φ ∪ Set.range fun m => σ m * inv τ)`. Establish `hB : B ≤ Reg E` using `Subring.closure_le.2 (by`.

Introduce and unpack `x (⟨r, rfl⟩ | ⟨p, rfl⟩)`. Conclude with `reg_mono le_top (hφ r)`. Conclude with `Sc.ratio hU hG (hσ p) hτ hE)`. Set `ψ : R →+* B` to `φ.codRestrict B fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)`. Establish `key : ∀ l, IsAffineOpen (W l ⊓ E) ∧ Gen (W l ⊓ E) _` using `fun l => extra_section hU hG (hs l) (hD l) (cov l) (aff l) (by`.

Introduce and unpack `x (rfl | ⟨r, rfl⟩)`. Conclude with `reg_inv (reg_mono le_top (hφ _)) fun z hz => (hW l).unit hz`. Conclude with `reg_mono le_top (hφ r)) (gen l) (τ := τ) (d := d l) (by rw [← hd l]; exact hτ.mono le_top)`. Use the proof step `(W := W l ⊓ E) fun z => ⟨fun hz => ⟨hz.1, hE.unit hz.2⟩, fun hz => ⟨hz.1, (hE z).2 ⟨trivial, hz.2⟩⟩⟩`. Take `⟨h₁, h₂⟩` from `local_global B hB (fun l => ψ (a l)) (by`.

Use `congrArg (Ideal.map ψ) ha` as an intermediate fact. Rewrite `this` using `[Ideal.map_top, Ideal.map_span, ← Set.range_comp]`. Conclude with `top_le_iff.1 (this.ge.trans le_sup_right)) (fun l => W l ⊓ E)`. Use the proof step `(fun l z => ⟨fun hz => ⟨hz.2, (hW l).unit hz.1⟩, fun hz => ⟨(hW l z).2 ⟨trivial, hz.2⟩, hz.1⟩⟩)`. Use the proof step `(fun l => (key l).1) fun l => (key l).2.mono (by`.

Introduce and unpack `x ((rfl | ⟨r, rfl⟩) | ⟨p, rfl⟩)`. Conclude with `⟨_, Subring.subset_closure (Or.inl rfl), fun _ _ => rfl⟩`. Conclude with `⟨_, Subring.subset_closure (Or.inr (ψ r).2), fun _ _ => rfl⟩`. Use `⟨inv (φ (a l)) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ * inv τ), Subring.mul_mem _ (Subring.pow_mem _ (Subring.subset_closure (Set.mem_insert _ _)) _) (Subring.subset_closure (Or.inr (Subring.subset_closure (Or.inr ⟨⟨l, p⟩, rfl⟩)))), fun z hz => ?_⟩ show s l p.2 z * s l p.1 z ^ d l * inv τ z = Ri …` and prove the remaining obligations. Rewrite using `[eσ ⟨l, p⟩ z hz.1, mul_assoc (φ _ z ^ _), ← mul_assoc (Ring.inverse _ ^ _), ← mul_pow, Ring.inverse_mul_cancel _ ((hW l).unit hz.1), one_pow, one_mul]`.

Use the proof step `rfl)`. Conclude with `⟨h₁, h₂.mono fun x hx => ⟨x, hx, fun _ _ => rfl⟩⟩`. Set `e : Fin (Fintype.card T + 1) ≃ Option T` to `(finSuccEquiv _).trans (Fintype.equivFin T).symm.optionCongr`. Set `σ' : Option T → Fn Z` to `fun o => o.elim 0 σ`. Establish `hσ' : ∀ o, Sc U G ⊤ (∏ l, N l) (σ' o)` using `fun o => by`.

Consider the cases of `o with`. Consider the case `none => exact Sc.zero _ _`. Consider the case `some t => exact hσ t`. Use `⟨∏ l, N l, (Finset.prod_pos fun l _ => hN l : 0 < ∏ l, N l), Fintype.card T, fun t => σ' (e t), fun t => hσ' _, fun z => ?_, fun t E hE => ?_⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `covW z`.

Take `⟨j, hj⟩` from `cov l z hl`. Use `⟨e.symm (some ⟨l, j, j⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.apply_symm_apply]`. Use `show IsUnit (σ ⟨l, j, j⟩ z)`. Rewrite using `[eσ ⟨l, j, j⟩ z hl]`.

Conclude with `(((hW l).unit hl).pow _).mul (((hD l j).unit hj).mul (((hD l j).unit hj).pow _))`. Take `⟨h₁, h₂⟩` from `main _ (hσ' (e t)) E hE`. Use `⟨h₁, h₂.mono ?_⟩` and prove the remaining obligations. Introduce and unpack `x (hx | ⟨m, rfl⟩)`. Conclude with `⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩`.

Use `⟨_, Subring.subset_closure (Or.inr ⟨e.symm (some m), ?_⟩), fun _ _ => rfl⟩` and prove the remaining obligations. Simplify using `only [Equiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem glue_pack {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} (hU : ∀ z, ∃ i, z ∈ U i) (hG : ∀ i z, IsUnit (G i z))
    [CompactSpace Z] [QuasiSeparatedSpace Z] (hT : ∀ i j, G i * inv (G j) ∈ Reg (U i ⊓ U j))
    {R : Type} [CommRing R] (φ : R →+* Fn Z) (hφ : ∀ r, φ r ∈ Reg ⊤) {Λ : Type} [Finite Λ] (a : Λ → R)
    (ha : Ideal.span (Set.range a) = ⊤) (W : Λ → Z.Opens) (hW : ∀ l, IsLoc (W l) ⊤ (φ (a l)))
    (H : ∀ l, Pack U G (W l) (insert (inv (φ (a l))) (Set.range φ))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ σ : Fin (M + 1) → Fn Z, (∀ t, Sc U G ⊤ N (σ t)) ∧ (∀ z, ∃ t, IsUnit (σ t z)) ∧
      ∀ t D, IsLoc D ⊤ (σ t) → IsAffineOpen D ∧ Gen D (Set.range φ ∪ Set.range fun m => σ m * inv (σ t)) := by
  classical
  have := Fintype.ofFinite Λ
  choose N hN M s D hs hD cov aff gen using H
  have hd : ∀ l, ∃ d, ∏ l, N l = N l * (d + 1) := fun l => by
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ l)
    have : 0 < ∏ l, N l := Finset.prod_pos fun l _ => hN l
    cases e with
    | zero => omega
    | succ e => exact ⟨e, he⟩
  choose d hd using hd
  let T := Σ l, Fin (M l + 1) × Fin (M l + 1)
  have hsc : ∀ t : T, Sc U G (W t.1) (∏ l, N l) (s t.1 t.2.2 * s t.1 t.2.1 ^ d t.1) := fun t => by
    rw [hd t.1, mul_add, mul_one, add_comm]
    exact (hs _ _).mul ((hs _ _).pow _)
  choose k σ hσ eσ using fun t : T => (hsc t).extend hU hG hT (hφ _) (hW t.1)
  have covW : ∀ z, ∃ l, z ∈ W l := fun z => by
    by_contra hn
    have : Ideal.span (Set.range a) ≤ (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)).comap
        ((Pi.evalRingHom _ z).comp φ) := Ideal.span_le.2 (by
      rintro _ ⟨l, rfl⟩ hu
      exact hn ⟨l, (hW l z).2 ⟨trivial, hu⟩⟩)
    rw [ha, top_le_iff, Ideal.comap_eq_top_iff] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
  have main : ∀ τ, Sc U G ⊤ (∏ l, N l) τ → ∀ E, IsLoc E ⊤ τ →
      IsAffineOpen E ∧ Gen E (Set.range φ ∪ Set.range fun m => σ m * inv τ) := by
    intro τ hτ E hE
    let B := Subring.closure (Set.range φ ∪ Set.range fun m => σ m * inv τ)
    have hB : B ≤ Reg E := Subring.closure_le.2 (by
      rintro x (⟨r, rfl⟩ | ⟨p, rfl⟩)
      · exact reg_mono le_top (hφ r)
      · exact Sc.ratio hU hG (hσ p) hτ hE)
    let ψ : R →+* B := φ.codRestrict B fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    have key : ∀ l, IsAffineOpen (W l ⊓ E) ∧ Gen (W l ⊓ E) _ := fun l =>
      extra_section hU hG (hs l) (hD l) (cov l) (aff l) (by
        rintro x (rfl | ⟨r, rfl⟩)
        · exact reg_inv (reg_mono le_top (hφ _)) fun z hz => (hW l).unit hz
        · exact reg_mono le_top (hφ r)) (gen l) (τ := τ) (d := d l) (by rw [← hd l]; exact hτ.mono le_top)
        (W := W l ⊓ E) fun z => ⟨fun hz => ⟨hz.1, hE.unit hz.2⟩, fun hz => ⟨hz.1, (hE z).2 ⟨trivial, hz.2⟩⟩⟩
    obtain ⟨h₁, h₂⟩ := local_global B hB (fun l => ψ (a l)) (by
        have := congrArg (Ideal.map ψ) ha
        rw [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at this
        exact top_le_iff.1 (this.ge.trans le_sup_right)) (fun l => W l ⊓ E)
      (fun l z => ⟨fun hz => ⟨hz.2, (hW l).unit hz.1⟩, fun hz => ⟨(hW l z).2 ⟨trivial, hz.2⟩, hz.1⟩⟩)
      (fun l => (key l).1) fun l => (key l).2.mono (by
        rintro x ((rfl | ⟨r, rfl⟩) | ⟨p, rfl⟩)
        · exact ⟨_, Subring.subset_closure (Or.inl rfl), fun _ _ => rfl⟩
        · exact ⟨_, Subring.subset_closure (Or.inr (ψ r).2), fun _ _ => rfl⟩
        · refine ⟨inv (φ (a l)) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ * inv τ),
            Subring.mul_mem _ (Subring.pow_mem _ (Subring.subset_closure (Set.mem_insert _ _)) _)
              (Subring.subset_closure (Or.inr (Subring.subset_closure (Or.inr ⟨⟨l, p⟩, rfl⟩)))), fun z hz => ?_⟩
          show s l p.2 z * s l p.1 z ^ d l * inv τ z =
            Ring.inverse (φ (a l) z) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ z * inv τ z)
          rw [eσ ⟨l, p⟩ z hz.1, mul_assoc (φ _ z ^ _), ← mul_assoc (Ring.inverse _ ^ _), ← mul_pow,
            Ring.inverse_mul_cancel _ ((hW l).unit hz.1), one_pow, one_mul]
          rfl)
    exact ⟨h₁, h₂.mono fun x hx => ⟨x, hx, fun _ _ => rfl⟩⟩
  let e : Fin (Fintype.card T + 1) ≃ Option T :=
    (finSuccEquiv _).trans (Fintype.equivFin T).symm.optionCongr
  let σ' : Option T → Fn Z := fun o => o.elim 0 σ
  have hσ' : ∀ o, Sc U G ⊤ (∏ l, N l) (σ' o) := fun o => by
    cases o with
    | none => exact Sc.zero _ _
    | some t => exact hσ t
  refine ⟨∏ l, N l, (Finset.prod_pos fun l _ => hN l : 0 < ∏ l, N l), Fintype.card T, fun t => σ' (e t), fun t => hσ' _,
    fun z => ?_, fun t E hE => ?_⟩
  · obtain ⟨l, hl⟩ := covW z
    obtain ⟨j, hj⟩ := cov l z hl
    refine ⟨e.symm (some ⟨l, j, j⟩), ?_⟩
    simp only [Equiv.apply_symm_apply]
    show IsUnit (σ ⟨l, j, j⟩ z)
    rw [eσ ⟨l, j, j⟩ z hl]
    exact (((hW l).unit hl).pow _).mul (((hD l j).unit hj).mul (((hD l j).unit hj).pow _))
  · obtain ⟨h₁, h₂⟩ := main _ (hσ' (e t)) E hE
    refine ⟨h₁, h₂.mono ?_⟩
    rintro x (hx | ⟨m, rfl⟩)
    · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
    · refine ⟨_, Subring.subset_closure (Or.inr ⟨e.symm (some m), ?_⟩), fun _ _ => rfl⟩
      simp only [Equiv.apply_symm_apply]
      rfl

def pb (h : Y ⟶ Z) : Fn Z →+* Fn Y :=
  Pi.ringHom fun y => (h.stalkMap y).hom.comp (Pi.evalRingHom _ (h y))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pb_apply (h : Y ⟶ Z) (F : Fn Z) (y : Y) : pb h F y = (h.stalkMap y).hom (F (h y)) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[pb_apply, Scheme.Hom.stalkMap_comp]`. Both sides reduce to the same expression.
-/
theorem pb_comp (h : Y ⟶ Z) (g : Z ⟶ X) (F : Fn X) : pb (h ≫ g) F = pb h (pb g F) := by
  funext y
  rw [pb_apply, Scheme.Hom.stalkMap_comp]
  rfl

/- English proof (translation)
The claim follows from `isUnit_map_iff (h.stalkMap y).hom _`.
-/
theorem pb_unit (h : Y ⟶ Z) (F : Fn Z) (y : Y) : IsUnit (pb h F y) ↔ IsUnit (F (h y)) :=
  isUnit_map_iff (h.stalkMap y).hom _

/- English proof (translation)
Use function extensionality and compare the values at `y`. Use `show (h.stalkMap y).hom (Ring.inverse (F (h y))) = Ring.inverse (pb h F y)`. Distinguish the cases in `hu : IsUnit (F (h y))`. Use `((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((pb_unit h F y).2 hu)).2 ?_).trans (one_mul _)` and prove the remaining obligations. Rewrite using `[pb_apply, ← map_mul, Ring.inverse_mul_cancel _ hu, map_one]`.

Rewrite using `[Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ (mt (pb_unit h F y).1 hu), map_zero]`.
-/
theorem pb_inv (h : Y ⟶ Z) (F : Fn Z) : pb h (inv F) = inv (pb h F) := by
  funext y
  show (h.stalkMap y).hom (Ring.inverse (F (h y))) = Ring.inverse (pb h F y)
  by_cases hu : IsUnit (F (h y))
  · refine ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((pb_unit h F y).2 hu)).2 ?_).trans (one_mul _)
    rw [pb_apply, ← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  · rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ (mt (pb_unit h F y).1 hu), map_zero]

/- English proof (translation)
The claim follows from `gs_eq (𝟙 Z) z V hz a`.
-/
theorem gs_id (V : Z.Opens) (z : Z) (hz : z ∈ V) (a : Γ(Z, V)) : gs (𝟙 Z) z V a = (Z.presheaf.germ V z hz).hom a :=
  gs_eq (𝟙 Z) z V hz a

/- English proof (translation)
The claim follows from `exists_congr fun a => forall_congr' fun z => forall_congr' fun hz => by rw [gs_id V z hz]`.
-/
theorem mem_reg_iff {V : Z.Opens} {F : Fn Z} : F ∈ Reg V ↔ ∃ a : Γ(Z, V), ∀ z ∈ V, gs (𝟙 Z) z V a = F z :=
  exists_congr fun a => forall_congr' fun z => forall_congr' fun hz => by rw [gs_id V z hz]

/- English proof (translation)
Rewrite using `[← gs_pull h g y V hy, gs_stalkMap h y (g ⁻¹ᵁ V) hy, gs_pull (𝟙 Z) g (h y) V hy, Category.id_comp]`.
-/
theorem stalkMap_gs (h : Y ⟶ Z) (g : Z ⟶ X) (y : Y) (V : X.Opens) (hy : g (h y) ∈ V) (a : Γ(X, V)) :
    (h.stalkMap y).hom (gs g (h y) V a) = gs (h ≫ g) y V a := by
  rw [← gs_pull h g y V hy, gs_stalkMap h y (g ⁻¹ᵁ V) hy, gs_pull (𝟙 Z) g (h y) V hy, Category.id_comp]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(g.app V).hom a, fun z hz => (gs_eq g z V hz a).symm⟩`.
-/
theorem reg_gs (g : Z ⟶ X) (V : X.Opens) (a : Γ(X, V)) : (fun z => gs g z V a) ∈ Reg (g ⁻¹ᵁ V) :=
  ⟨(g.app V).hom a, fun z hz => (gs_eq g z V hz a).symm⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `mem_reg_iff.1 hF`. Conclude with `reg_congr (reg_gs h V a) fun y hy => (gs_stalkMap h y V hy a).trans (congrArg _ (ha _ hy))`.
-/
theorem reg_pull (h : Y ⟶ Z) {V : Z.Opens} {F : Fn Z} (hF : F ∈ Reg V) : pb h F ∈ Reg (h ⁻¹ᵁ V) := by
  obtain ⟨a, ha⟩ := mem_reg_iff.1 hF
  exact reg_congr (reg_gs h V a) fun y hy => (gs_stalkMap h y V hy a).trans (congrArg _ (ha _ hy))

def cst (p : Z ⟶ X) : Γ(X, ⊤) →+* Fn Z :=
  Pi.ringHom fun z => (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp (p.app ⊤).hom

/- English proof (translation)
The claim follows from `(gs_eq p z ⊤ trivial r).symm`.
-/
theorem cst_apply (p : Z ⟶ X) (r : Γ(X, ⊤)) (z : Z) : cst p r z = gs p z ⊤ r := (gs_eq p z ⊤ trivial r).symm

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[pb_apply, cst_apply, cst_apply, stalkMap_gs h p y ⊤ trivial]`.
-/
theorem pb_cst (h : Y ⟶ Z) (p : Z ⟶ X) (r : Γ(X, ⊤)) : pb h (cst p r) = cst (h ≫ p) r := by
  funext y
  rw [pb_apply, cst_apply, cst_apply, stalkMap_gs h p y ⊤ trivial]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(p.app ⊤).hom r, fun _ _ => rfl⟩`.
-/
theorem reg_cst (p : Z ⟶ X) (r : Γ(X, ⊤)) : cst p r ∈ Reg ⊤ := ⟨(p.app ⊤).hom r, fun _ _ => rfl⟩

/- English proof (translation)
Introduce `x` and use `(X.mem_basicOpen r x trivial).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩`.
-/
theorem loc_cst (r : Γ(X, ⊤)) : IsLoc (X.basicOpen r) ⊤ (cst (𝟙 X) r) := fun x =>
  (X.mem_basicOpen r x trivial).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

section Open

variable (h : Y ⟶ Z) [IsOpenImmersion h]

/- English proof (translation)
The claim follows from `(ConcreteCategory.bijective_of_isIso (h.stalkMap y)).1 e`.
-/
theorem pb_inj {F F' : Fn Z} {y : Y} (e : pb h F y = pb h F' y) : F (h y) = F' (h y) :=
  (ConcreteCategory.bijective_of_isIso (h.stalkMap y)).1 e

/- English proof (translation)
Establish `: ∀ z : Z, ∃ x : Z.presheaf.stalk z, ∀ y (e : z = h y), (h.stalkMap y).hom (e ▸ x) = F' y` using `fun z => by`. Distinguish the cases in `hz : ∃ y, h y = z`. Take `⟨y, rfl⟩` from `hz`. Take `⟨x, hx⟩` from `(ConcreteCategory.bijective_of_isIso (h.stalkMap y)).2 (F' y)`. Use `⟨x, fun y' e => ?_⟩` and prove the remaining obligations.

Take `rfl` from `h.isOpenEmbedding.injective e`. Conclude with `hx`. Conclude with `⟨0, fun y e => (hz ⟨y, e.symm⟩).elim⟩`. Use `choose F hF using this`. Conclude with `⟨F, funext fun y => hF (h y) y rfl⟩`.
-/
theorem pb_surj (F' : Fn Y) : ∃ F, pb h F = F' := by
  have : ∀ z : Z, ∃ x : Z.presheaf.stalk z, ∀ y (e : z = h y), (h.stalkMap y).hom (e ▸ x) = F' y := fun z => by
    by_cases hz : ∃ y, h y = z
    · obtain ⟨y, rfl⟩ := hz
      obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (h.stalkMap y)).2 (F' y)
      refine ⟨x, fun y' e => ?_⟩
      obtain rfl := h.isOpenEmbedding.injective e
      exact hx
    · exact ⟨0, fun y e => (hz ⟨y, e.symm⟩).elim⟩
  choose F hF using this
  exact ⟨F, funext fun y => hF (h y) y rfl⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `mem_reg_iff.1 hF`. Take `⟨b, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (h.appIso V).hom).2 a`. Use `mem_reg_iff.2 ⟨b, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `pb_inj h (F := fun z => gs (𝟙 Z) z _ b) (Eq.trans ?_ (ha y hy))` and prove the remaining obligations.

Rewrite using `[pb_apply, ← gs_stalkMap h y _ (h.apply_mem_image_iff.2 hy), h.appIso_hom']`. Conclude with `((gs_appLE h _ _ _ (𝟙 Y) y hy b).trans (by rw [Category.id_comp])).symm`.
-/
theorem reg_push {V : Y.Opens} {F : Fn Z} (hF : pb h F ∈ Reg V) : F ∈ Reg (h ''ᵁ V) := by
  obtain ⟨a, ha⟩ := mem_reg_iff.1 hF
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (h.appIso V).hom).2 a
  refine mem_reg_iff.2 ⟨b, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  refine pb_inj h (F := fun z => gs (𝟙 Z) z _ b) (Eq.trans ?_ (ha y hy))
  rw [pb_apply, ← gs_stalkMap h y _ (h.apply_mem_image_iff.2 hy), h.appIso_hom']
  exact ((gs_appLE h _ _ _ (𝟙 Y) y hy b).trans (by rw [Category.id_comp])).symm

/- English proof (translation)
Introduce `F hF`. Take `⟨b, hb, e⟩` from `hS _ (reg_mono (h.preimage_image_eq V).ge (reg_pull h hF))`. Rewrite `hb` using `[← RingHom.map_closure]`. Take `⟨b, hb, rfl⟩` from `hb`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `pb_inj h (e y hy)`.
-/
theorem gen_push {V : Y.Opens} {S : Set (Fn Z)} (hS : Gen V (pb h '' S)) : Gen (h ''ᵁ V) S := by
  intro F hF
  obtain ⟨b, hb, e⟩ := hS _ (reg_mono (h.preimage_image_eq V).ge (reg_pull h hF))
  rw [← RingHom.map_closure] at hb
  obtain ⟨b, hb, rfl⟩ := hb
  refine ⟨b, hb, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact pb_inj h (e y hy)

/- English proof (translation)
Take `⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩` from `H`. Use `choose s' e using fun j => pb_surj h (s j)`. Take `rfl : s = fun j => pb h (s' j)` from `funext fun j => (e j).symm`. Use `⟨N, hN, M, s', fun j => h ''ᵁ D j, fun j i => ?_, fun j z => ⟨?_, ?_⟩, ?_, fun j => (aff j).image_of_isOpenImmersion h, fun j => gen_push h ?_⟩` and prove the remaining obligations. Use `reg_mono ?_ (reg_push h (V := ⊤ ⊓ h ⁻¹ᵁ U i) (by rw [map_mul, map_pow]; exact hs j i))` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨y, -, rfl⟩, hy⟩`. Conclude with `⟨y, ⟨trivial, hy⟩, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨⟨y, trivial, rfl⟩, (pb_unit h _ y).1 ((hD j).unit hy)⟩`. Introduce and unpack `⟨⟨y, -, rfl⟩, hy⟩`.

Conclude with `⟨y, (hD j y).2 ⟨trivial, (pb_unit h _ y).2 hy⟩, rfl⟩`. Introduce and unpack `_ ⟨y, -, rfl⟩`. Take `⟨j, hj⟩` from `cov y trivial`. Conclude with `⟨j, y, hj, rfl⟩`. Use `gen j` as an intermediate fact.

Simplify `this` using `only [Set.image_union, ← Set.range_comp', map_mul, pb_inv]`.
-/
theorem pack_push {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} {S : Set (Fn Z)}
    (H : Pack (fun i => h ⁻¹ᵁ U i) (fun i => pb h (G i)) ⊤ (pb h '' S)) : Pack U G (h ''ᵁ ⊤) S := by
  obtain ⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩ := H
  choose s' e using fun j => pb_surj h (s j)
  obtain rfl : s = fun j => pb h (s' j) := funext fun j => (e j).symm
  refine ⟨N, hN, M, s', fun j => h ''ᵁ D j, fun j i => ?_, fun j z => ⟨?_, ?_⟩, ?_,
    fun j => (aff j).image_of_isOpenImmersion h, fun j => gen_push h ?_⟩
  · refine reg_mono ?_ (reg_push h (V := ⊤ ⊓ h ⁻¹ᵁ U i) (by rw [map_mul, map_pow]; exact hs j i))
    rintro _ ⟨⟨y, -, rfl⟩, hy⟩
    exact ⟨y, ⟨trivial, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, trivial, rfl⟩, (pb_unit h _ y).1 ((hD j).unit hy)⟩
  · rintro ⟨⟨y, -, rfl⟩, hy⟩
    exact ⟨y, (hD j y).2 ⟨trivial, (pb_unit h _ y).2 hy⟩, rfl⟩
  · rintro _ ⟨y, -, rfl⟩
    obtain ⟨j, hj⟩ := cov y trivial
    exact ⟨j, y, hj, rfl⟩
  · have := gen j
    simpa only [Set.image_union, ← Set.range_comp', map_mul, pb_inv] using this

end Open

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H x`. Take `⟨b, hb, e⟩` from `H (fun z => gs (𝟙 Z) z D x) (mem_reg_iff.2 ⟨x, fun _ _ => rfl⟩)`. It suffices to establish `∃ p, ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by`. Take `⟨p, hp⟩` from `this`.

Conclude with `⟨p, sec_ext fun z hz => (hp z hz).trans ((e z hz).symm.trans (gs_id D z hz x))⟩`. Use `clear e`. Proceed by induction on `hb using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨c, rfl⟩ | ⟨t, rfl⟩` into its components or cases.

Conclude with `⟨MvPolynomial.C c, fun z hz => by rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩`. Conclude with `⟨MvPolynomial.X t, fun z hz => by rw [MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]⟩`. Consider the case `zero => exact ⟨0, fun z hz => by rw [map_zero, map_zero]; rfl⟩`. Consider the case `one => exact ⟨1, fun z hz => by rw [map_one, map_one]; rfl⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨p, hp⟩` from `hx`. Take `⟨q, hq⟩` from `hy`. Conclude with `⟨p + q, fun z hz => by rw [map_add, map_add, hp, hq]; rfl⟩`. Consider the case `neg x _ hx`. Take `⟨p, hp⟩` from `hx`.

Conclude with `⟨-p, fun z hz => by rw [map_neg, map_neg, hp]; rfl⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨p, hp⟩` from `hx`. Take `⟨q, hq⟩` from `hy`. Conclude with `⟨p * q, fun z hz => by rw [map_mul, map_mul, hp, hq]; rfl⟩`.

Introduce and unpack `H F ⟨x, hx⟩`. Take `⟨p, rfl⟩` from `H x`. It suffices to establish `∃ b ∈ Subring.closure (Set.range φ ∪ Set.range ρ), ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by`. Take `⟨b, hb, e⟩` from `this`. Conclude with `⟨b, hb, fun z hz => (hx z hz).symm.trans (e z hz)⟩`.

Use `clear hx`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨φ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), fun z hz => by`. Rewrite using `[MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩`. Consider the case `add p q hp hq`.

Take `⟨a, ha, e⟩` from `hp`. Take `⟨b, hb, e'⟩` from `hq`. Conclude with `⟨a + b, add_mem ha hb, fun z hz => by rw [map_add, map_add, e, e']; rfl⟩`. Consider the case `mul_X p t hp`. Take `⟨a, ha, e⟩` from `hp`.

Conclude with `⟨a * ρ t, mul_mem ha (Subring.subset_closure (Or.inr ⟨t, rfl⟩)), fun z hz => by`. Rewrite using `[map_mul, map_mul, e, MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]`. Use the proof step `rfl⟩`.
-/
theorem gen_iff {R T : Type} [CommRing R] {D : Z.Opens} (ψ : R →+* Γ(Z, D)) (r : T → Γ(Z, D)) (φ : R → Fn Z)
    (ρ : T → Fn Z) (hψ : ∀ c, ∀ z ∈ D, gs (𝟙 Z) z D (ψ c) = φ c z) (hr : ∀ t, ∀ z ∈ D, gs (𝟙 Z) z D (r t) = ρ t z) :
    Gen D (Set.range φ ∪ Set.range ρ) ↔ Function.Surjective (MvPolynomial.eval₂Hom ψ r) := by
  constructor
  · intro H x
    obtain ⟨b, hb, e⟩ := H (fun z => gs (𝟙 Z) z D x) (mem_reg_iff.2 ⟨x, fun _ _ => rfl⟩)
    suffices ∃ p, ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by
      obtain ⟨p, hp⟩ := this
      exact ⟨p, sec_ext fun z hz => (hp z hz).trans ((e z hz).symm.trans (gs_id D z hz x))⟩
    clear e
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨MvPolynomial.C c, fun z hz => by rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩
      · exact ⟨MvPolynomial.X t, fun z hz => by rw [MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]⟩
    | zero => exact ⟨0, fun z hz => by rw [map_zero, map_zero]; rfl⟩
    | one => exact ⟨1, fun z hz => by rw [map_one, map_one]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, fun z hz => by rw [map_add, map_add, hp, hq]; rfl⟩
    | neg x _ hx =>
      obtain ⟨p, hp⟩ := hx
      exact ⟨-p, fun z hz => by rw [map_neg, map_neg, hp]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p * q, fun z hz => by rw [map_mul, map_mul, hp, hq]; rfl⟩
  · rintro H F ⟨x, hx⟩
    obtain ⟨p, rfl⟩ := H x
    suffices ∃ b ∈ Subring.closure (Set.range φ ∪ Set.range ρ),
        ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by
      obtain ⟨b, hb, e⟩ := this
      exact ⟨b, hb, fun z hz => (hx z hz).symm.trans (e z hz)⟩
    clear hx
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨φ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), fun z hz => by
        rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩
    | add p q hp hq =>
      obtain ⟨a, ha, e⟩ := hp
      obtain ⟨b, hb, e'⟩ := hq
      exact ⟨a + b, add_mem ha hb, fun z hz => by rw [map_add, map_add, e, e']; rfl⟩
    | mul_X p t hp =>
      obtain ⟨a, ha, e⟩ := hp
      exact ⟨a * ρ t, mul_mem ha (Subring.subset_closure (Or.inr ⟨t, rfl⟩)), fun z hz => by
        rw [map_mul, map_mul, e, MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]; rfl⟩

section Link

variable {P : LB Y}

/- English proof (translation)
Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k'` using `⟨hk, hk'⟩`. Conclude with `(gs_res _ y _ hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) (s.compat k k')).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))`.
-/
theorem sec_tr (s : LB.Sec P) (y : Y) {k k' : P.ι} (hk : y ∈ P.U k) (hk' : y ∈ P.U k') :
    gs (𝟙 Y) y _ (s.f k) = (gm (𝟙 Y) y _ (P.g k k')).val * gs (𝟙 Y) y _ (s.f k') := by
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k' := ⟨hk, hk'⟩
  exact (gs_res _ y _ hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) (s.compat k k')).trans ((gs_mul _ y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

def sv (γ : Y → P.ι) (s : LB.Sec P) : Fn Y := fun y => gs (𝟙 Y) y (P.U (γ y)) (s.f (γ y))

variable {γ : Y → P.ι} (hγ : ∀ y, y ∈ P.U (γ y))
include hγ

/- English proof (translation)
Introduce `y` and use `(mem_nonzeroLocus s y).trans ⟨fun ⟨k, hk, hu⟩ => ⟨trivial, by rw [sec_tr s y hk (hγ y)] at hu; exact isUnit_of_mul_isUnit_right hu⟩, fun hu => ⟨γ y, hγ y, hu.2⟩⟩`.
-/
theorem loc_sv (s : LB.Sec P) : IsLoc (nonzeroLocus s) ⊤ (sv γ s) := fun y =>
  (mem_nonzeroLocus s y).trans ⟨fun ⟨k, hk, hu⟩ => ⟨trivial, by
    rw [sec_tr s y hk (hγ y)] at hu; exact isUnit_of_mul_isUnit_right hu⟩, fun hu => ⟨γ y, hγ y, hu.2⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U (γ y)` using `⟨hy, hγ y⟩`. Establish `e` using `congrArg (gs (𝟙 Y) y _) (H (γ y))`. Rewrite `e` using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm]`.

Conclude with `(Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy)).2 e.symm`. Introduce `H k`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Establish `e` using `(Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy.1)).1 (H y hy.1)`. Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U k` using `hy`.

Rewrite using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, sec_tr s y hy.2 (hγ y), sec_tr t y hy.2 (hγ y), mul_left_comm]`. Conclude with `congrArg _ e.symm`.
-/
theorem ratio_iff (s t : LB.Sec P) (r : Γ(Y, nonzeroLocus s)) :
    (∀ k, (Y.presheaf.map (homOfLE (inf_le_right : nonzeroLocus s ⊓ P.U k ≤ P.U k)).op).hom (t.f k) =
      (Y.presheaf.map (homOfLE (inf_le_left : nonzeroLocus s ⊓ P.U k ≤ nonzeroLocus s)).op).hom r *
        (Y.presheaf.map (homOfLE (inf_le_right : nonzeroLocus s ⊓ P.U k ≤ P.U k)).op).hom (s.f k)) ↔
    ∀ y ∈ nonzeroLocus s, gs (𝟙 Y) y _ r = (sv γ t * inv (sv γ s)) y := by
  constructor
  · intro H y hy
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U (γ y) := ⟨hy, hγ y⟩
    have e := congrArg (gs (𝟙 Y) y _) (H (γ y))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy)).2 e.symm
  · intro H k
    refine fn_ext fun y hy => ?_
    have e := (Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy.1)).1 (H y hy.1)
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U k := hy
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, sec_tr s y hy.2 (hγ y),
      sec_tr t y hy.2 (hγ y), mul_left_comm]
    exact congrArg _ e.symm

omit hγ

variable {ι : Type} {U : ι → Y.Opens} {G : ι → Fn Y} {N : ℕ} {κ : ι → P.ι} {c : Y → ι}
  (hκ : ∀ i, U i ≤ P.U (κ i)) (hc : ∀ y, y ∈ U (c y))
  (hg : ∀ i y, y ∈ U i → (gm (𝟙 Y) y _ (P.g (κ i) (κ (c y)))).val = G i y ^ N)
include hκ hc hg

/- English proof (translation)
Introduce `i` and use `reg_congr (reg_mono (inf_le_right.trans (hκ i)) (reg_gs (𝟙 Y) _ (s.f (κ i)))) fun y hy => by rw [sec_tr s y (hκ i hy.2) (hκ _ (hc y)), hg i y hy.2] rfl`.
-/
theorem sc_sv (s : LB.Sec P) : Sc U G ⊤ N (sv (fun y => κ (c y)) s) := fun i =>
  reg_congr (reg_mono (inf_le_right.trans (hκ i)) (reg_gs (𝟙 Y) _ (s.f (κ i)))) fun y hy => by
    rw [sec_tr s y (hκ i hy.2) (hκ _ (hc y)), hg i y hy.2]
    rfl

/- English proof (translation)
Establish `: ∀ k, (fun y => (gm (𝟙 Y) y _ (P.g k (κ (c y)))).val * σ y) ∈ Reg (P.U k)` using `fun k => reg_glue fun z hz => ⟨P.U k ⊓ U (c z), ⟨hz, hc z⟩, reg_congr (mul_mem (reg_mono (inf_le_inf_left _ (hκ _)) (reg_gs (𝟙 Y) _ (P.g k (κ (c z))).val)) (reg_mono (le_inf le_top inf_le_right) (hσ (c z)))) fun y hy => by show gs (𝟙 Y) y _ (P.g k (κ (c z))).val * (G (c z) y ^ N …`. Rewrite using `[gs_unit (𝟙 Y) y (P.U k ⊓ P.U (κ (c z))) ⟨hy.1, hκ _ hy.2⟩, ← hg _ y hy.2, ← mul_assoc, ← Units.val_mul, gm_cocycle hP (𝟙 Y) y hy.1 (hκ _ hy.2) (hκ _ (hc y))]⟩`. Use `choose f hf using fun k => mem_reg_iff.1 (this k)`. Use `⟨⟨f, fun k k' => fn_ext fun y hy => ?_⟩, funext fun y => ?_⟩` and prove the remaining obligations. Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k'` using `hy`.

Rewrite using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm, hf k y hy.1, hf k' y hy.2, ← mul_assoc, ← Units.val_mul, gm_cocycle hP (𝟙 Y) y hy.1 hy.2 (hκ _ (hc y))]`. Use `(hf _ y (hκ _ (hc y))).trans ?_` and prove the remaining obligations. Rewrite using `[gm_self hP (𝟙 Y) y (hκ _ (hc y)), Units.val_one, one_mul]`.
-/
theorem exists_sv (hP : P.IsLB) {σ : Fn Y} (hσ : Sc U G ⊤ N σ) : ∃ s : LB.Sec P, sv (fun y => κ (c y)) s = σ := by
  have : ∀ k, (fun y => (gm (𝟙 Y) y _ (P.g k (κ (c y)))).val * σ y) ∈ Reg (P.U k) := fun k =>
    reg_glue fun z hz => ⟨P.U k ⊓ U (c z), ⟨hz, hc z⟩, reg_congr
      (mul_mem (reg_mono (inf_le_inf_left _ (hκ _)) (reg_gs (𝟙 Y) _ (P.g k (κ (c z))).val))
        (reg_mono (le_inf le_top inf_le_right) (hσ (c z)))) fun y hy => by
      show gs (𝟙 Y) y _ (P.g k (κ (c z))).val * (G (c z) y ^ N * σ y) = _
      rw [gs_unit (𝟙 Y) y (P.U k ⊓ P.U (κ (c z))) ⟨hy.1, hκ _ hy.2⟩, ← hg _ y hy.2, ← mul_assoc, ← Units.val_mul,
        gm_cocycle hP (𝟙 Y) y hy.1 (hκ _ hy.2) (hκ _ (hc y))]⟩
  choose f hf using fun k => mem_reg_iff.1 (this k)
  refine ⟨⟨f, fun k k' => fn_ext fun y hy => ?_⟩, funext fun y => ?_⟩
  · have hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k' := hy
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm, hf k y hy.1, hf k' y hy.2,
      ← mul_assoc, ← Units.val_mul, gm_cocycle hP (𝟙 Y) y hy.1 hy.2 (hκ _ (hc y))]
  · refine (hf _ y (hκ _ (hc y))).trans ?_
    rw [gm_self hP (𝟙 Y) y (hκ _ (hc y)), Units.val_one, one_mul]

end Link

/- English proof (translation)
Take `⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩` from `H`. Use `⟨N, hN, M, s, D, hs, hD, cov, aff, fun j => (gen j).mono ?_⟩` and prove the remaining obligations. Introduce and unpack `x (hx | hx)`. Conclude with `⟨x, Subring.closure_mono Set.subset_union_left (hS x hx), fun _ _ => rfl⟩`. Conclude with `⟨x, Subring.subset_closure (Or.inr hx), fun _ _ => rfl⟩`.
-/
theorem Pack.mono {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} {W : Z.Opens} {S S' : Set (Fn Z)} (H : Pack U G W S)
    (hS : ∀ x ∈ S, x ∈ Subring.closure S') : Pack U G W S' := by
  obtain ⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩ := H
  refine ⟨N, hN, M, s, D, hs, hD, cov, aff, fun j => (gen j).mono ?_⟩
  rintro x (hx | hx)
  · exact ⟨x, Subring.closure_mono Set.subset_union_left (hS x hx), fun _ _ => rfl⟩
  · exact ⟨x, Subring.subset_closure (Or.inr hx), fun _ _ => rfl⟩

/- English proof (translation)
Take `⟨F, hF⟩` from `pb_surj b (cst (𝟙 V) c)`. Establish `h₁ : F ∈ Reg (B.basicOpen a)` using `hb ▸ reg_push b (hF ▸ reg_cst _ c)`. Establish `h₂ : Gen ⊤ (Set.range (cst (𝟙 B)))` using `fun F ⟨x, hx⟩ => ⟨cst (𝟙 B) x, Subring.subset_closure ⟨x, rfl⟩, fun z hz => (hx z hz).symm⟩`. Take `⟨β, hβ, eβ⟩` from `Gen.loc (isAffineOpen_top B) (loc_cst a) (reg_cst _ a) h₂ F h₁`. Establish `: cst q c = pb h (pb p β)`.

Rewrite using `[← pb_comp, e, ← Category.comp_id q, ← pb_cst, ← hF, ← pb_comp, Category.comp_id q]`. Use function extensionality and compare the values at `y`. Rewrite using `[pb_apply, pb_apply, eβ]`. Rewrite using `[← hb]`. Conclude with `⟨q y, trivial, rfl⟩`.

Rewrite using `[this, ← RingHom.map_closure]`. Use `⟨_, ?_, rfl⟩` and prove the remaining obligations. Use `Subring.mem_map.2 ⟨β, hβ, (rfl : pb p β = _)⟩` as an intermediate fact. Rewrite `this` using `[RingHom.map_closure]`. Simplify using `only [Set.image_insert_eq, ← Set.range_comp', pb_inv, pb_cst, Category.comp_id] at this`.

Conclude with `this`.
-/
theorem cst_mem {B V : Scheme.{0}} [IsAffine B] (a : Γ(B, ⊤)) (b : V ⟶ B) [IsOpenImmersion b]
    (hb : b ''ᵁ ⊤ = B.basicOpen a) (q : Y ⟶ V) (h : Y ⟶ Z) (p : Z ⟶ B) (e : h ≫ p = q ≫ b) (c : Γ(V, ⊤)) :
    cst q c ∈ Subring.closure (pb h '' insert (inv (cst p a)) (Set.range (cst p))) := by
  obtain ⟨F, hF⟩ := pb_surj b (cst (𝟙 V) c)
  have h₁ : F ∈ Reg (B.basicOpen a) := hb ▸ reg_push b (hF ▸ reg_cst _ c)
  have h₂ : Gen ⊤ (Set.range (cst (𝟙 B))) := fun F ⟨x, hx⟩ =>
    ⟨cst (𝟙 B) x, Subring.subset_closure ⟨x, rfl⟩, fun z hz => (hx z hz).symm⟩
  obtain ⟨β, hβ, eβ⟩ := Gen.loc (isAffineOpen_top B) (loc_cst a) (reg_cst _ a) h₂ F h₁
  have : cst q c = pb h (pb p β) := by
    rw [← pb_comp, e, ← Category.comp_id q, ← pb_cst, ← hF, ← pb_comp, Category.comp_id q]
    funext y
    rw [pb_apply, pb_apply, eβ]
    rw [← hb]
    exact ⟨q y, trivial, rfl⟩
  rw [this, ← RingHom.map_closure]
  refine ⟨_, ?_, rfl⟩
  have := Subring.mem_map.2 ⟨β, hβ, (rfl : pb p β = _)⟩
  rw [RingHom.map_closure] at this
  simp only [Set.image_insert_eq, ← Set.range_comp', pb_inv, pb_cst, Category.comp_id] at this
  exact this

/- English proof (translation)
Use `(congrArg Units.val (gm_linComb L _ _ (𝟙 _) y _ _ (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hi'))).trans ?_` and prove the remaining obligations. Simplify using `only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val, Category.id_comp]`.
-/
theorem gm_const (L : LB X) (j : Y ⟶ X) (N : ℕ) (y : Y) (i i' : L.ι) (hi : j y ∈ L.U i) (hi' : j y ∈ L.U i') :
    (gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin N) (fun _ => j) (fun _ => 1)).g (fun _ => i) (fun _ => i'))).val =
      (gm j y _ (L.g i i')).val ^ N := by
  refine (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y _ _ (Set.mem_iInter.2 fun _ => hi)
    (Set.mem_iInter.2 fun _ => hi'))).trans ?_
  simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val,
    Category.id_comp]

/- English proof (translation)
Establish `: IsAffine U` using `hU`. Establish `hle : U.ι ''ᵁ U.toScheme.basicOpen a ≤ U₀`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `ha hx`. Set `V : U₀.toScheme.Opens` to `U₀.ι ⁻¹ᵁ (U.ι ''ᵁ U.toScheme.basicOpen a)`.

Establish `hV : IsAffineOpen V` using `(((isAffineOpen_top U.toScheme).basicOpen a).image_of_isOpenImmersion U.ι).preimage_of_isOpenImmersion U₀.ι (by rwa [Scheme.Opens.opensRange_ι])`. Take `⟨b, hb⟩ : ∃ b : V.toScheme ⟶ U.toScheme, b ≫ U.ι = V.ι ≫ U₀.ι` from `⟨IsOpenImmersion.lift U.ι (V.ι ≫ U₀.ι) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨x, -, hx⟩` from `y.2`. Conclude with `⟨x, hx⟩), IsOpenImmersion.lift_fac _ _ _⟩`.

Establish `: IsOpenImmersion (b ≫ U.ι)` using `by rw [hb]; infer_instance`. Establish `: IsOpenImmersion b` using `IsOpenImmersion.of_comp b U.ι`. Establish `hb' : b ''ᵁ ⊤ = U.toScheme.basicOpen a`. Apply `U.ι.image_injective` to reduce the goal to its premises. Use `show U.ι ''ᵁ b ''ᵁ ⊤ = U.ι ''ᵁ _`.

Rewrite using `[← Scheme.Hom.comp_image]`. Simplify using `only [hb]`. Rewrite using `[Scheme.Hom.comp_image, Scheme.Opens.ι_image_top, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hle]`. Set `p₀` to `A.hom ∣_ U₀`. Set `j` to `(p₀ ⁻¹ᵁ V).ι ≫ (A.hom ⁻¹ᵁ U₀).ι`.

Establish `hj : j ≫ A.hom = (p₀ ∣_ V) ≫ b ≫ U.ι`. Rewrite using `[hb, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, morphismRestrict_ι]`. Take `⟨h, hh⟩ : ∃ h : (p₀ ⁻¹ᵁ V).toScheme ⟶ (A.hom ⁻¹ᵁ U).toScheme, h ≫ (A.hom ⁻¹ᵁ U).ι = j` from `⟨IsOpenImmersion.lift _ j (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `(congrArg (fun q => q y ∈ U) hj).mpr (b ((p₀ ∣_ V) y)).2), IsOpenImmersion.lift_fac _ _ _⟩`. Establish `: IsOpenImmersion (h ≫ (A.hom ⁻¹ᵁ U).ι)` using `by rw [hh]; infer_instance`. Establish `: IsOpenImmersion h` using `IsOpenImmersion.of_comp h (A.hom ⁻¹ᵁ U).ι`. Establish `e : h ≫ (A.hom ∣_ U) = (p₀ ∣_ V) ≫ b`. Rewrite using `[← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, hj, Category.assoc]`.

Establish `hu : ∀ z, IsUnit (cst (A.hom ∣_ U) a z) ↔ (A.hom ∣_ U) z ∈ U.toScheme.basicOpen a` using `fun z => by`. Rewrite using `[← Category.comp_id (A.hom ∣_ U), ← pb_cst, pb_unit, Category.comp_id]`. Conclude with `⟨fun hz => (loc_cst a _).2 ⟨trivial, hz⟩, fun hz => (loc_cst a).unit hz⟩`. Use `⟨h ''ᵁ ⊤, fun z => ⟨?_, fun hz => ?_⟩, pack_push h ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, -, rfl⟩`.

Use `⟨trivial, (hu _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[← hb']`. Conclude with `⟨(p₀ ∣_ V) y, trivial, (congrArg (fun q => q y) e).symm⟩`. Establish `hz` using `(hu z).1 hz.2`. Establish `e₁ : U.ι ((A.hom ∣_ U) z) = A.hom z.1` using `morphismRestrict_base_coe A.hom U z`.

Establish `m₀ : z.1 ∈ A.hom ⁻¹ᵁ U₀` using `by show A.hom z.1 ∈ U₀`. Rewrite using `[← e₁]`. Conclude with `ha hz`. Establish `m₁ : (⟨z.1, m₀⟩ : (A.hom ⁻¹ᵁ U₀).toScheme) ∈ p₀ ⁻¹ᵁ V` using `⟨_, hz, e₁.trans (morphismRestrict_base_coe A.hom U₀ ⟨z.1, m₀⟩).symm⟩`. Conclude with `⟨⟨_, m₁⟩, trivial, Subtype.ext (congrArg (fun q => q ⟨_, m₁⟩) hh)⟩`.

Take `⟨N, hN, M, s, cov, hs⟩` from `H V hV`. Use `choose aff r hr surj using hs`. Set `P` to `powOver (Over.mk p₀) (L.pull (A.hom ⁻¹ᵁ U₀).ι) V N`. Set `κ : L.ι → P.ι` to `fun i _ _ => i`. Establish `pt : ∀ y, (A.hom ⁻¹ᵁ U).ι (h y) = (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y)` using `fun y => congrArg (fun q => q y) hh`.

Establish `hκ : ∀ i, h ⁻¹ᵁ ((A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i) ≤ P.U (κ i)` using `fun i y hy => Set.mem_iInter.2 fun _ => mem_pull.2 (show (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) ∈ L.U i from pt y ▸ hy)`. Establish `hγ : ∀ y, y ∈ P.U (κ (c (h y)))` using `fun y => hκ _ (hc (h y))`. Use `Pack.mono (S := Set.range (cst (p₀ ∣_ V))) ⟨N, hN, M, fun i => sv (fun y => κ (c (h y))) (s i), fun i => nonzeroLocus (s i), fun i => sc_sv hκ (fun y => hc (h y)) (fun i y hy => ?_) (s i), fun i => loc_sv hγ (s i), fun y _ => Opens.mem_iSup.1 (cov.ge trivial), aff, fun i => ?_⟩ ? …` and prove the remaining obligations. Establish `hm : (A.hom ⁻¹ᵁ U).ι (h y) ∈ L.U i ⊓ L.U (c (h y))` using `⟨hy, hc (h y)⟩`. Establish `m₁ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => i)` using `mem_pull.2 ((pt y) ▸ hm.1)`.

Establish `m₂ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => c (h y))` using `mem_pull.2 ((pt y) ▸ hm.2)`. Use `(gm_const _ _ N y _ _ m₁ m₂).trans ?_` and prove the remaining obligations. Use `congrArg (· ^ N) ((congrArg Units.val (gm_pull_g L _ _ y _ _ m₁ m₂)).trans ?_)` and prove the remaining obligations. Rewrite using `[pb_apply, ← gs_unit _ _ _ hm, stalkMap_gs h _ y _ hm, gs_unit _ y _ hm, hh]`. Conclude with `(gen_iff _ (r i) _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans (by rw [Category.id_comp, cst_apply]; rfl)) (fun m => (ratio_iff hγ (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `cst_mem a b hb' _ h _ e x`.
-/
theorem pack_of_relAmple {S : Scheme.{0}} (A : Over S) (L : LB A.left) (U : S.Opens) (hU : IsAffineOpen U)
    (U₀ : S.Opens) (H : RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)) (a : Γ(U.toScheme, ⊤))
    (ha : U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀) (c : (A.hom ⁻¹ᵁ U).toScheme → L.ι)
    (hc : ∀ z, (A.hom ⁻¹ᵁ U).ι z ∈ L.U (c z)) :
    ∃ W, IsLoc W ⊤ (cst (A.hom ∣_ U) a) ∧ Pack (fun i => (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i)
      (fun i z => (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val) W
      (insert (inv (cst (A.hom ∣_ U) a)) (Set.range (cst (A.hom ∣_ U)))) := by
  have : IsAffine U := hU
  have hle : U.ι ''ᵁ U.toScheme.basicOpen a ≤ U₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ha hx
  let V : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ (U.ι ''ᵁ U.toScheme.basicOpen a)
  have hV : IsAffineOpen V := (((isAffineOpen_top U.toScheme).basicOpen a).image_of_isOpenImmersion
    U.ι).preimage_of_isOpenImmersion U₀.ι (by rwa [Scheme.Opens.opensRange_ι])
  obtain ⟨b, hb⟩ : ∃ b : V.toScheme ⟶ U.toScheme, b ≫ U.ι = V.ι ≫ U₀.ι :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ U₀.ι) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, -, hx⟩ := y.2
      exact ⟨x, hx⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion (b ≫ U.ι) := by rw [hb]; infer_instance
  have : IsOpenImmersion b := IsOpenImmersion.of_comp b U.ι
  have hb' : b ''ᵁ ⊤ = U.toScheme.basicOpen a := by
    apply U.ι.image_injective
    show U.ι ''ᵁ b ''ᵁ ⊤ = U.ι ''ᵁ _
    rw [← Scheme.Hom.comp_image]
    simp only [hb]
    rw [Scheme.Hom.comp_image, Scheme.Opens.ι_image_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.2 hle]
  let p₀ := A.hom ∣_ U₀
  let j := (p₀ ⁻¹ᵁ V).ι ≫ (A.hom ⁻¹ᵁ U₀).ι
  have hj : j ≫ A.hom = (p₀ ∣_ V) ≫ b ≫ U.ι := by
    rw [hb, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, morphismRestrict_ι]
  obtain ⟨h, hh⟩ : ∃ h : (p₀ ⁻¹ᵁ V).toScheme ⟶ (A.hom ⁻¹ᵁ U).toScheme, h ≫ (A.hom ⁻¹ᵁ U).ι = j :=
    ⟨IsOpenImmersion.lift _ j (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ U) hj).mpr (b ((p₀ ∣_ V) y)).2), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion (h ≫ (A.hom ⁻¹ᵁ U).ι) := by rw [hh]; infer_instance
  have : IsOpenImmersion h := IsOpenImmersion.of_comp h (A.hom ⁻¹ᵁ U).ι
  have e : h ≫ (A.hom ∣_ U) = (p₀ ∣_ V) ≫ b := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, hj, Category.assoc]
  have hu : ∀ z, IsUnit (cst (A.hom ∣_ U) a z) ↔ (A.hom ∣_ U) z ∈ U.toScheme.basicOpen a := fun z => by
    rw [← Category.comp_id (A.hom ∣_ U), ← pb_cst, pb_unit, Category.comp_id]
    exact ⟨fun hz => (loc_cst a _).2 ⟨trivial, hz⟩, fun hz => (loc_cst a).unit hz⟩
  refine ⟨h ''ᵁ ⊤, fun z => ⟨?_, fun hz => ?_⟩, pack_push h ?_⟩
  · rintro ⟨y, -, rfl⟩
    refine ⟨trivial, (hu _).2 ?_⟩
    rw [← hb']
    exact ⟨(p₀ ∣_ V) y, trivial, (congrArg (fun q => q y) e).symm⟩
  · have hz := (hu z).1 hz.2
    have e₁ : U.ι ((A.hom ∣_ U) z) = A.hom z.1 := morphismRestrict_base_coe A.hom U z
    have m₀ : z.1 ∈ A.hom ⁻¹ᵁ U₀ := by
      show A.hom z.1 ∈ U₀
      rw [← e₁]; exact ha hz
    have m₁ : (⟨z.1, m₀⟩ : (A.hom ⁻¹ᵁ U₀).toScheme) ∈ p₀ ⁻¹ᵁ V :=
      ⟨_, hz, e₁.trans (morphismRestrict_base_coe A.hom U₀ ⟨z.1, m₀⟩).symm⟩
    exact ⟨⟨_, m₁⟩, trivial, Subtype.ext (congrArg (fun q => q ⟨_, m₁⟩) hh)⟩
  obtain ⟨N, hN, M, s, cov, hs⟩ := H V hV
  choose aff r hr surj using hs
  let P := powOver (Over.mk p₀) (L.pull (A.hom ⁻¹ᵁ U₀).ι) V N
  let κ : L.ι → P.ι := fun i _ _ => i
  have pt : ∀ y, (A.hom ⁻¹ᵁ U).ι (h y) = (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) := fun y => congrArg (fun q => q y) hh
  have hκ : ∀ i, h ⁻¹ᵁ ((A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i) ≤ P.U (κ i) := fun i y hy =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (show (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) ∈ L.U i from pt y ▸ hy)
  have hγ : ∀ y, y ∈ P.U (κ (c (h y))) := fun y => hκ _ (hc (h y))
  refine Pack.mono (S := Set.range (cst (p₀ ∣_ V))) ⟨N, hN, M, fun i => sv (fun y => κ (c (h y))) (s i),
    fun i => nonzeroLocus (s i), fun i => sc_sv hκ (fun y => hc (h y)) (fun i y hy => ?_) (s i),
    fun i => loc_sv hγ (s i), fun y _ => Opens.mem_iSup.1 (cov.ge trivial), aff, fun i => ?_⟩ ?_
  · have hm : (A.hom ⁻¹ᵁ U).ι (h y) ∈ L.U i ⊓ L.U (c (h y)) := ⟨hy, hc (h y)⟩
    have m₁ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => i) :=
      mem_pull.2 ((pt y) ▸ hm.1)
    have m₂ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => c (h y)) :=
      mem_pull.2 ((pt y) ▸ hm.2)
    refine (gm_const _ _ N y _ _ m₁ m₂).trans ?_
    refine congrArg (· ^ N) ((congrArg Units.val (gm_pull_g L _ _ y _ _ m₁ m₂)).trans ?_)
    rw [pb_apply, ← gs_unit _ _ _ hm, stalkMap_gs h _ y _ hm, gs_unit _ y _ hm, hh]
  · exact (gen_iff _ (r i) _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans
      (by rw [Category.id_comp, cst_apply]; rfl))
      (fun m => (ratio_iff hγ (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  · rintro _ ⟨x, rfl⟩
    exact cst_mem a b hb' _ h _ e x

/- English proof (translation)
Introduce `S A L hL _ _ H U hU`. Establish `: IsAffine U` using `hU`. Establish `: CompactSpace (A.hom ⁻¹ᵁ U).toScheme` using `QuasiCompact.compactSpace_of_compactSpace (A.hom ∣_ U)`. Establish `: QuasiSeparatedSpace (A.hom ⁻¹ᵁ U).toScheme` using `quasiSeparatedSpace_of_quasiSeparated (A.hom ∣_ U)`. Use `choose c hc using fun z : (A.hom ⁻¹ᵁ U).toScheme => exists_chart hL ((A.hom ⁻¹ᵁ U).ι z)`.

Set `good : Set Γ(U.toScheme, ⊤)` to `{a | ∃ U₀ : S.Opens, U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀ ∧ RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)}`. Establish `hspan : Ideal.span good = ⊤`. Rewrite using `[← (isAffineOpen_top U.toScheme).iSup_basicOpen_eq_self_iff, eq_top_iff]`. Introduce `x _`. Take `⟨U₀, hx, h₀⟩` from `H (U.ι x)`.

Take `⟨a, ha, hxa⟩` from `(isAffineOpen_top U.toScheme).exists_basicOpen_le (V := U.ι ⁻¹ᵁ U₀) ⟨x, hx⟩ trivial`. Conclude with `Opens.mem_iSup.2 ⟨⟨a, U₀, ha, h₀⟩, hxa⟩`. Take `⟨t, ht, hspan'⟩` from `(Ideal.span_eq_top_iff_finite _).1 hspan`. Use `choose W hW hP using fun l : t => (ht l.2).elim fun U₀ h₀ => pack_of_relAmple A L U hU U₀ h₀.2 l.1 h₀.1 c hc`. Establish `hcov : ∀ z, ∃ i, z ∈ (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i` using `fun z => ⟨c z, hc z⟩`.

Take `⟨N, hN, M, σ, hσ, cov, main⟩` from `glue_pack hcov (fun _ _ => Units.isUnit _) (fun i j => reg_congr (reg_gs (A.hom ⁻¹ᵁ U).ι _ (L.g i j).val) fun z hz => by show _ = (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val * Ring.inverse (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g j (c z))).val`. Rewrite using `[gs_unit _ z _ hz, Ring.inverse_unit, ← Units.val_mul, ← gm_cocycle hL _ z hz.1 hz.2 (hc z), mul_inv_cancel_right])`. Use the proof step `(cst (A.hom ∣_ U)) (reg_cst _) (fun l : t => l.1) (by rw [Subtype.range_coe_subtype]; exact hspan') W hW hP`. Set `κ : L.ι → (powOver A L U N).ι` to `fun i _ => i`. Establish `hκ : ∀ i, (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i ≤ (powOver A L U N).U (κ i)` using `fun i y hy => Set.mem_iInter.2 fun _ => hy`.

Establish `hγ : ∀ y, y ∈ (powOver A L U N).U (κ (c y))` using `fun y => hκ _ (hc y)`. Use `choose s hs using fun m => exists_sv hκ hc (fun i y hy => gm_const L _ N y _ _ hy (hc y)) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _) (hσ m)`. Establish `loc : ∀ m, IsLoc (nonzeroLocus (s m)) ⊤ (σ m)` using `fun m => hs m ▸ loc_sv hγ (s m)`. Use `⟨N, hN, M, s, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i _ (loc i)).1, ?_⟩⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `cov z`.

Conclude with `Opens.mem_iSup.2 ⟨m, (loc m z).2 ⟨trivial, hm⟩⟩`. Use `choose r hr using fun m => mem_reg_iff.1 (Sc.ratio hcov (fun _ _ => Units.isUnit _) (hσ m) (hσ i) (loc i))`. Use `⟨r, fun m => (ratio_iff hγ (s i) (s m) (r m)).2 (by rw [hs, hs]; exact hr m), ?_⟩` and prove the remaining obligations. Conclude with `(gen_iff _ r _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans (by rw [Category.id_comp, cst_apply])) hr).1 (main i _ (loc i)).2`.
-/
theorem relAmple_of_locally : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom →
    QuasiSeparated A.hom → (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
      RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → RelAmple A L := by
  intro S A L hL _ _ H U hU
  have : IsAffine U := hU
  have : CompactSpace (A.hom ⁻¹ᵁ U).toScheme := QuasiCompact.compactSpace_of_compactSpace (A.hom ∣_ U)
  have : QuasiSeparatedSpace (A.hom ⁻¹ᵁ U).toScheme := quasiSeparatedSpace_of_quasiSeparated (A.hom ∣_ U)
  choose c hc using fun z : (A.hom ⁻¹ᵁ U).toScheme => exists_chart hL ((A.hom ⁻¹ᵁ U).ι z)
  let good : Set Γ(U.toScheme, ⊤) := {a | ∃ U₀ : S.Opens, U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀ ∧
    RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)}
  have hspan : Ideal.span good = ⊤ := by
    rw [← (isAffineOpen_top U.toScheme).iSup_basicOpen_eq_self_iff, eq_top_iff]
    intro x _
    obtain ⟨U₀, hx, h₀⟩ := H (U.ι x)
    obtain ⟨a, ha, hxa⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le (V := U.ι ⁻¹ᵁ U₀) ⟨x, hx⟩ trivial
    exact Opens.mem_iSup.2 ⟨⟨a, U₀, ha, h₀⟩, hxa⟩
  obtain ⟨t, ht, hspan'⟩ := (Ideal.span_eq_top_iff_finite _).1 hspan
  choose W hW hP using fun l : t => (ht l.2).elim fun U₀ h₀ => pack_of_relAmple A L U hU U₀ h₀.2 l.1 h₀.1 c hc
  have hcov : ∀ z, ∃ i, z ∈ (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i := fun z => ⟨c z, hc z⟩
  obtain ⟨N, hN, M, σ, hσ, cov, main⟩ := glue_pack hcov (fun _ _ => Units.isUnit _) (fun i j =>
      reg_congr (reg_gs (A.hom ⁻¹ᵁ U).ι _ (L.g i j).val) fun z hz => by
        show _ = (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val * Ring.inverse (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g j (c z))).val
        rw [gs_unit _ z _ hz, Ring.inverse_unit, ← Units.val_mul, ← gm_cocycle hL _ z hz.1 hz.2 (hc z),
          mul_inv_cancel_right])
    (cst (A.hom ∣_ U)) (reg_cst _) (fun l : t => l.1) (by rw [Subtype.range_coe_subtype]; exact hspan') W hW hP
  let κ : L.ι → (powOver A L U N).ι := fun i _ => i
  have hκ : ∀ i, (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i ≤ (powOver A L U N).U (κ i) := fun i y hy => Set.mem_iInter.2 fun _ => hy
  have hγ : ∀ y, y ∈ (powOver A L U N).U (κ (c y)) := fun y => hκ _ (hc y)
  choose s hs using fun m => exists_sv hκ hc (fun i y hy => gm_const L _ N y _ _ hy (hc y))
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _) (hσ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (s m)) ⊤ (σ m) := fun m => hs m ▸ loc_sv hγ (s m)
  refine ⟨N, hN, M, s, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i _ (loc i)).1, ?_⟩⟩
  · obtain ⟨m, hm⟩ := cov z
    exact Opens.mem_iSup.2 ⟨m, (loc m z).2 ⟨trivial, hm⟩⟩
  · choose r hr using fun m => mem_reg_iff.1 (Sc.ratio hcov (fun _ _ => Units.isUnit _) (hσ m) (hσ i) (loc i))
    refine ⟨r, fun m => (ratio_iff hγ (s i) (s m) (r m)).2 (by rw [hs, hs]; exact hr m), ?_⟩
    exact (gen_iff _ r _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans
      (by rw [Category.id_comp, cst_apply])) hr).1 (main i _ (loc i)).2

end GlobalTheory.AmpleLocal
