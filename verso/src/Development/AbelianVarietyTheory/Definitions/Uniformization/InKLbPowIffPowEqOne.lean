import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.NoUnifOfZeroMatrix

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.KModel

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

/- English proof (translation)
Establish `mem : ∀ (j : K → PUnit.{1} → L.ι) (y : Y), y ∈ LB.wchart (lbPow L n) φ j ↔ y ∈ LB.wchart L φ (fun k => j k ⟨⟩)` using `fun j y => ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h k) ⟨⟩, fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h k⟩`. Establish `key : ∀ (i j : K → PUnit.{1} → L.ι) (y : Y), y ∈ LB.wchart (lbPow L n) φ i → y ∈ LB.wchart (lbPow L n) φ j → gm (𝟙 Y) y (LB.wchart (lbPow L n) φ i ⊓ LB.wchart (lbPow L n) φ j) ((LB.LinComb (lbPow L n) φ ε).g i j) = gm (𝟙 Y) y (LB.wchart L φ (fun k => i k ⟨⟩) ⊓ LB.wchart L φ (fun …`. Introduce `i j y hi hj`. Use `(gm_linComb (lbPow L n) φ ε (𝟙 Y) y i j hi hj).trans (Eq.trans ?_ (gm_linComb L φ (fun k => n * ε k) (𝟙 Y) y (fun k => i k ⟨⟩) (fun k => j k ⟨⟩) ((mem i y).1 hi) ((mem j y).1 hj)).symm)` and prove the remaining obligations. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[zpow_mul, zpow_natCast]`. Conclude with `congrArg (· ^ ε k) ((gm_linComb L (fun _ : PUnit.{1} => 𝟙 X) (fun _ => (n : ℤ)) (𝟙 Y ≫ φ k) y (i k) (j k) (Set.mem_iInter.1 hi k) (Set.mem_iInter.1 hj k)).trans (by`. Rewrite using `[Fintype.prod_unique, Category.comp_id, zpow_natCast]))`. Prove the components needed by the constructor for the conclusion. Conclude with `KerPow.gen_transfer (M := LB.LinComb (lbPow L n) φ ε) (M' := LB.LinComb L φ (fun k => n * ε k)) (fun j k _ => j k) (fun j y hy => (mem _ y).2 hy) fun i j y hi hj => (key (fun k _ => i k) (fun k _ => j k) y ((mem _ y).2 hi) ((mem _ y).2 hj)).symm`.

Conclude with `KerPow.gen_transfer (M' := LB.LinComb (lbPow L n) φ ε) (M := LB.LinComb L φ (fun k => n * ε k)) (fun j k => j k ⟨⟩) (fun j y hy => (mem _ y).1 hy) fun i j y hi hj => key i j y hi hj`.
-/
theorem hasGen_lbPow (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℕ) :
    KerPow.HasGen (lbPow L n) φ ε ↔ KerPow.HasGen L φ (fun k => n * ε k) := by
  have mem : ∀ (j : K → PUnit.{1} → L.ι) (y : Y), y ∈ LB.wchart (lbPow L n) φ j ↔ y ∈ LB.wchart L φ (fun k => j k ⟨⟩) :=
    fun j y => ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h k) ⟨⟩,
      fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h k⟩
  have key : ∀ (i j : K → PUnit.{1} → L.ι) (y : Y), y ∈ LB.wchart (lbPow L n) φ i → y ∈ LB.wchart (lbPow L n) φ j →
      gm (𝟙 Y) y (LB.wchart (lbPow L n) φ i ⊓ LB.wchart (lbPow L n) φ j) ((LB.LinComb (lbPow L n) φ ε).g i j) =
      gm (𝟙 Y) y (LB.wchart L φ (fun k => i k ⟨⟩) ⊓ LB.wchart L φ (fun k => j k ⟨⟩))
        ((LB.LinComb L φ (fun k => n * ε k)).g (fun k => i k ⟨⟩) (fun k => j k ⟨⟩)) := by
    intro i j y hi hj
    refine (gm_linComb (lbPow L n) φ ε (𝟙 Y) y i j hi hj).trans
      (Eq.trans ?_ (gm_linComb L φ (fun k => n * ε k) (𝟙 Y) y (fun k => i k ⟨⟩) (fun k => j k ⟨⟩) ((mem i y).1 hi) ((mem j y).1 hj)).symm)
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_mul, zpow_natCast]
    exact congrArg (· ^ ε k) ((gm_linComb L (fun _ : PUnit.{1} => 𝟙 X) (fun _ => (n : ℤ)) (𝟙 Y ≫ φ k) y (i k) (j k)
      (Set.mem_iInter.1 hi k) (Set.mem_iInter.1 hj k)).trans (by
        rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]))
  constructor
  · exact KerPow.gen_transfer (M := LB.LinComb (lbPow L n) φ ε) (M' := LB.LinComb L φ (fun k => n * ε k))
      (fun j k _ => j k) (fun j y hy => (mem _ y).2 hy)
      fun i j y hi hj => (key (fun k _ => i k) (fun k _ => j k) y ((mem _ y).2 hi) ((mem _ y).2 hj)).symm
  · exact KerPow.gen_transfer (M' := LB.LinComb (lbPow L n) φ ε) (M := LB.LinComb L φ (fun k => n * ε k))
      (fun j k => j k ⟨⟩) (fun j y hy => (mem _ y).1 hy) fun i j y hi hj => key i j y hi hj

end

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} {T : Over S}

/- English proof (translation)
Establish `triv : KerPow.LocGen L (K` using `Fin 0) (fst T B).left ![] ![] := KerPow.locGen_of_trivial hL fun U _ h => by simp`. Establish `e : InK B (lbPow L n) x ↔ KerPow.LocGen L (K` using `Fin 2) (fst T B).left ![(translPt B x).left, (snd T B).left] (fun k => n * (![1, -1] : Fin 2 → ℤ) k) := by`. Rewrite using `[inK_iff_locGen]`. Simplify using `only [KerPow.LocGen, hasGen_lbPow]`. Rewrite using `[e]`.

Apply the tactic sequence `constructor <;> intro H <;> refine triv.comb hL H fun U _ h => ?_ <;> simp [Fin.prod_univ_two, mul_comm]`.
-/
theorem inK_lbPow_iff (hL : L.IsLB) (x : T ⟶ B) (n : ℕ) : InK B (lbPow L n) x ↔
    KerPow.LocGen L (K := Fin 2) (fst T B).left ![(snd T B).left, (translPt B x).left] ![(n : ℤ), -(n : ℤ)] := by
  have triv : KerPow.LocGen L (K := Fin 0) (fst T B).left ![] ![] :=
    KerPow.locGen_of_trivial hL fun U _ h => by simp
  have e : InK B (lbPow L n) x ↔ KerPow.LocGen L (K := Fin 2) (fst T B).left
      ![(translPt B x).left, (snd T B).left] (fun k => n * (![1, -1] : Fin 2 → ℤ) k) := by
    rw [inK_iff_locGen]
    simp only [KerPow.LocGen, hasGen_lbPow]
  rw [e]
  constructor <;> intro H <;> refine triv.comb hL H fun U _ h => ?_ <;> simp [Fin.prod_univ_two, mul_comm]

/- English proof (translation)
The claim follows from `(inK_lbPow_iff P.isLB x N).trans ((KerPow.locGen_iff _ _ _).symm.trans (h S P N hN T x))`.
-/
theorem inK_lbPow_iff_pow_eq_one (h : KerPowSt) [IsLocallyNoetherian S] (P : PolAV S) {N : ℕ} (hN : 1 ≤ N)
    (x : T ⟶ P.A) : InK P.A (lbPow P.L N) x ↔ x ^ N = 1 :=
  (inK_lbPow_iff P.isLB x N).trans ((KerPow.locGen_iff _ _ _).symm.trans (h S P N hN T x))

/- English proof (translation)
The claim follows from `(inK_lbPow_iff hL x 0).2 (KerPow.locGen_of_trivial hL fun U _ h => by simp)`.
-/
theorem inK_lbPow_zero (hL : L.IsLB) (x : T ⟶ B) : InK B (lbPow L 0) x :=
  (inK_lbPow_iff hL x 0).2 (KerPow.locGen_of_trivial hL fun U _ h => by simp)

/- English proof (translation)
Use `(inK_iff_locGen x).2 fun p => ?_` and prove the remaining obligations. Take `⟨V, hV, H⟩` from `h p`. Take `⟨W, hW, t⟩` from `(inK_iff_locGen _).1 H ⟨p, hV⟩`. Set `U : T.left.Opens` to `V.ι ''ᵁ W`. Establish `hU : ∀ q : T.left, q ∈ U → q ∈ V` using `fun q ⟨r, _, e⟩ => e ▸ r.2`.

Use `⟨U, ⟨⟨p, hV⟩, hW, rfl⟩, ?_⟩` and prove the remaining obligations. Set `Z` to `overRes (T := T ⊗ B) ((fst T B).left ⁻¹ᵁ U)`. Set `ρ : Z ⟶ T ⊗ B` to `overResι _`. Set `a₀ : Z.left ⟶ V.toScheme` to `IsOpenImmersion.lift V.ι (ρ ≫ fst T B).left (by`. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU _ y.2)`. Establish `ha₀ : a₀ ≫ V.ι = (ρ ≫ fst T B).left` using `IsOpenImmersion.lift_fac _ _ _`. Set `a : Z ⟶ overRes V` to `Over.homMk a₀ (by show a₀ ≫ V.ι ≫ T.hom = _`. Rewrite using `[← Category.assoc, ha₀, Over.w])`.

Establish `ha : a ≫ overResι V = ρ ≫ fst T B` using `Over.OverMorphism.ext ha₀`. Set `u : Z ⟶ overRes V ⊗ B` to `lift a (ρ ≫ snd T B)`. Apply the tactic sequence `have hu : u ≫ overResι V ▷ B = ρ := by ext1 <;> simp [u, ha]`. Use `t.of_range u.left (fun y => ?_) fun k => ?_` and prove the remaining obligations. Establish `e₁ : (fst (overRes V) B).left (u.left y) = a₀ y` using `congrArg (fun q : Z ⟶ overRes V => q.left y) (lift_fst a _)`.

Take `⟨r, hr, e⟩` from `(y.2 : (fst T B).left y.1 ∈ U)`. Establish `e₂ : a₀ y = r` using `Subtype.ext ((congrArg (fun q : Z.left ⟶ T.left => q y) ha₀).trans e.symm)`. Use `show (fst (overRes V) B).left (u.left y) ∈ W`. Rewrite using `[e₁, e₂]`. Conclude with `hr`.

Use `fin_cases k`. Use `show (u ≫ translPt B (overResι V ≫ x)).left = (ρ ≫ translPt B x).left`. Rewrite using `[← KerPow.whisker_translPt, ← Category.assoc, hu]`. Conclude with `congrArg (fun q => q.left) (lift_snd a (ρ ≫ snd T B))`.
-/
theorem inK_of_local (x : T ⟶ B)
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ InK B L (overResι V ≫ x)) : InK B L x := by
  refine (inK_iff_locGen x).2 fun p => ?_
  obtain ⟨V, hV, H⟩ := h p
  obtain ⟨W, hW, t⟩ := (inK_iff_locGen _).1 H ⟨p, hV⟩
  let U : T.left.Opens := V.ι ''ᵁ W
  have hU : ∀ q : T.left, q ∈ U → q ∈ V := fun q ⟨r, _, e⟩ => e ▸ r.2
  refine ⟨U, ⟨⟨p, hV⟩, hW, rfl⟩, ?_⟩
  let Z := overRes (T := T ⊗ B) ((fst T B).left ⁻¹ᵁ U)
  let ρ : Z ⟶ T ⊗ B := overResι _
  let a₀ : Z.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι (ρ ≫ fst T B).left (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU _ y.2)
  have ha₀ : a₀ ≫ V.ι = (ρ ≫ fst T B).left := IsOpenImmersion.lift_fac _ _ _
  let a : Z ⟶ overRes V := Over.homMk a₀ (by
    show a₀ ≫ V.ι ≫ T.hom = _
    rw [← Category.assoc, ha₀, Over.w])
  have ha : a ≫ overResι V = ρ ≫ fst T B := Over.OverMorphism.ext ha₀
  let u : Z ⟶ overRes V ⊗ B := lift a (ρ ≫ snd T B)
  have hu : u ≫ overResι V ▷ B = ρ := by
    ext1 <;> simp [u, ha]
  refine t.of_range u.left (fun y => ?_) fun k => ?_
  · have e₁ : (fst (overRes V) B).left (u.left y) = a₀ y :=
      congrArg (fun q : Z ⟶ overRes V => q.left y) (lift_fst a _)
    obtain ⟨r, hr, e⟩ := (y.2 : (fst T B).left y.1 ∈ U)
    have e₂ : a₀ y = r := Subtype.ext ((congrArg (fun q : Z.left ⟶ T.left => q y) ha₀).trans e.symm)
    show (fst (overRes V) B).left (u.left y) ∈ W
    rw [e₁, e₂]; exact hr
  · fin_cases k
    · show (u ≫ translPt B (overResι V ≫ x)).left = (ρ ≫ translPt B x).left
      rw [← KerPow.whisker_translPt, ← Category.assoc, hu]
    · exact congrArg (fun q => q.left) (lift_snd a (ρ ≫ snd T B))

/- English proof (translation)
Take `⟨w, hw⟩` from `hw`. Establish `H` using `((inK_iff_locGen _).1 hx).baseChange (π' := (fst T B').left) (T ◁ F).left (𝟙 _) ((congrArg (fun q => q.left) (whiskerLeft_fst T F)).trans (Category.comp_id _).symm) (φ' := fun k => (![(translPt B' x).left, (snd T B').left] : Fin 2 → _) k ≫ F.left) fun k => by fin_cases k`. Use `show (T ◁ F ≫ ((fst T B ≫ x ≫ F) * snd T B)).left = (((fst T B' ≫ x) * snd T B') ≫ F).left`. Rewrite using `[MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc, whiskerLeft_snd, Category.assoc]`. Conclude with `congrArg (fun q => q.left) (whiskerLeft_snd T F)`.

Use `(inK_iff_locGen x).2 fun p => ?_` and prove the remaining obligations. Take `⟨V, hV, t⟩` from `H p`. Take `⟨t, ht⟩` from `t.pull (𝟙 _) (φ' := fun k => (((fst T B').left ⁻¹ᵁ V).ι ≫ (![(translPt B' x).left, (snd T B').left] : Fin 2 → _) k) ≫ F.left) fun k => by`. Rewrite using `[Category.id_comp, Category.assoc]`. Conclude with `⟨V, hV, exists_down ((isGen_iff w).1 hw) hL hL' t ht⟩`.
-/
theorem inK_of_hom {B' : Over S} [GrpObj B'] (F : B' ⟶ B) [IsMonHom F] {L' : LB B'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F.left)) (x : T ⟶ B') (hx : InK B L (x ≫ F)) : InK B' L' x := by
  obtain ⟨w, hw⟩ := hw
  have H := ((inK_iff_locGen _).1 hx).baseChange (π' := (fst T B').left) (T ◁ F).left (𝟙 _)
    ((congrArg (fun q => q.left) (whiskerLeft_fst T F)).trans (Category.comp_id _).symm)
    (φ' := fun k => (![(translPt B' x).left, (snd T B').left] : Fin 2 → _) k ≫ F.left) fun k => by
      fin_cases k
      · show (T ◁ F ≫ ((fst T B ≫ x ≫ F) * snd T B)).left = (((fst T B' ≫ x) * snd T B') ≫ F).left
        rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc, whiskerLeft_snd, Category.assoc]
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T F)
  refine (inK_iff_locGen x).2 fun p => ?_
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨t, ht⟩ := t.pull (𝟙 _) (φ' := fun k => (((fst T B').left ⁻¹ᵁ V).ι ≫
    (![(translPt B' x).left, (snd T B').left] : Fin 2 → _) k) ≫ F.left) fun k => by
      rw [Category.id_comp, Category.assoc]
  exact ⟨V, hV, exists_down ((isGen_iff w).1 hw) hL hL' t ht⟩

/- English proof (translation)
The claim follows from `have h := DVR.linComb_isLB L hL (K := PUnit) (fun _ => F.left) (fun _ => 1) inK_of_hom F hL h (lbIso_self h) x (hx ▸ inK_one hL T)`.
-/
theorem inK_pull_of_ker {B' : Over S} [GrpObj B'] (F : B' ⟶ B) [IsMonHom F] (hL : L.IsLB) (x : T ⟶ B')
    (hx : x ≫ F = 1) : InK B' (L.pull F.left) x :=
  have h := DVR.linComb_isLB L hL (K := PUnit) (fun _ => F.left) (fun _ => 1)
  inK_of_hom F hL h (lbIso_self h) x (hx ▸ inK_one hL T)

/- English proof (translation)
Introduce `_` and use `⟨⊤, trivial, ⟨fun j => (j ⟨⟩ 0).elim⟩, fun j => (j ⟨⟩ 0).elim⟩`.
-/
theorem inK_noCharts (x : T ⟶ B) : InK B ⟨PEmpty, fun i => i.elim, fun i => i.elim⟩ x :=
  fun _ => ⟨⊤, trivial, ⟨fun j => (j ⟨⟩ 0).elim⟩, fun j => (j ⟨⟩ 0).elim⟩

/- English proof (translation)
Take `⟨P, -, -, hg, -, -, ⟨x, h₁, h₂⟩, -⟩` from `TorusAlg.Test.square_lattice H`. Use `⟨P, x, hg, fun hx => h₁ (hx.eq_one P.ktriv), (inK_lbPow_iff_pow_eq_one h P (by norm_num) x).2 ((pow_two x).trans h₂), fun hx => h₁ ?_⟩` and prove the remaining obligations. Establish `e` using `(inK_lbPow_iff_pow_eq_one h P (by norm_num) x).1 hx`. Rewrite `e` using `[pow_succ, pow_two, h₂, _root_.one_mul]`. Then use the resulting hypothesis.
-/
theorem two_torsion (H : TorusAlgebraic) (h : KerPowSt) :
    ∃ (P : PolAV (Sp ℂ)) (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A), P.g = 1 ∧
      ¬ InK P.A P.L x ∧ InK P.A (lbPow P.L 2) x ∧ ¬ InK P.A (lbPow P.L 3) x := by
  obtain ⟨P, -, -, hg, -, -, ⟨x, h₁, h₂⟩, -⟩ := TorusAlg.Test.square_lattice H
  refine ⟨P, x, hg, fun hx => h₁ (hx.eq_one P.ktriv),
    (inK_lbPow_iff_pow_eq_one h P (by norm_num) x).2 ((pow_two x).trans h₂), fun hx => h₁ ?_⟩
  have e := (inK_lbPow_iff_pow_eq_one h P (by norm_num) x).1 hx
  rwa [pow_succ, pow_two, h₂, _root_.one_mul] at e

end GlobalTheory.UU.KModel
end
