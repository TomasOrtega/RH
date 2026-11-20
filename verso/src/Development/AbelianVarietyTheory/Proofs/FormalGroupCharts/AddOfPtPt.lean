import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

/- English proof (translation)
Use `⟨fun m => ?_, fun m => ?_⟩` and prove the remaining obligations. Use `show _ ≫ (y (m + 1) * z (m + 1)) = y m * z m`. Rewrite using `[MonObj.comp_mul, hy.1 m, hz.1 m]`. Use `show _ ≫ (y m * z m) = 1`. Rewrite using `[MonObj.comp_mul, hy.2 m, hz.2 m, _root_.mul_one]`.
-/
theorem IsFPt.mul {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y z : Fam G κ} (hy : IsFPt y) (hz : IsFPt z) : IsFPt (fun m => y m * z m : Fam G κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show _ ≫ (y (m + 1) * z (m + 1)) = y m * z m
    rw [MonObj.comp_mul, hy.1 m, hz.1 m]
  · show _ ≫ (y m * z m) = 1
    rw [MonObj.comp_mul, hy.2 m, hz.2 m, _root_.mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j`. Apply the tactic sequence `funext j; fin_cases j <;> rfl`. Unfold `addOf`. Rewrite using `[h]`.

Unfold `ev`. Conclude with `congrFun MvPowerSeries.subst_self _`.
-/
theorem addOf_pt_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  have h : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  unfold addOf
  rw [h]
  unfold ev
  exact congrFun MvPowerSeries.subst_self _

/- English proof (translation)
Introduce `R _ G _ _ d x hx`. Establish `uC : ∀ {n : ℕ} {a a' : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a' y → a = a'` using `fun {n a a' y} h h' => ((hR R G d x hx (Fin n × Fin d)).2.1 y ((hR R G d x hx (Fin n × Fin d)).2.2.1 a y h)).unique h h'`. Establish `uP : ∀ {n : ℕ} {a : Pt R n d} {y y' : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a y' → y = y'` using `fun {n a y y'} h h' => ((hR R G d x hx (Fin n × Fin d)).1 a h.1).unique h h'`. Establish `gen : ∀ (n : ℕ) (j : Fin n), ∃ y : Fam G (Fin n × Fin d), Rep x (pt R d j) y` using `fun n j => ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists`. Use `choose Y hY using gen`.

Use `⟨?_, fun F F' hF hF' => ?_⟩` and prove the remaining obligations. Use `swap`. Rewrite using `[← addOf_pt_pt F, ← addOf_pt_pt F']`. Conclude with `uC (hF.2 2 _ _ _ _ (hY 2 0) (hY 2 1)) (hF'.2 2 _ _ _ _ (hY 2 0) (hY 2 1))`. Establish `H2` using `hR R G d x hx (Fin 2 × Fin d)`.

Take `⟨F, hF⟩` from `(H2.2.1 _ (IsFPt.mul (H2.2.2.1 _ _ (hY 2 0)) (H2.2.2.1 _ _ (hY 2 1)))).exists`. Establish `law : IsLawOf x F`. Use `⟨hF.1, fun n a b y z ha hb => ?_⟩` and prove the remaining obligations. Set `c : Fin 2 × Fin d → PS R n d` to `fun p => (![a, b] : Fin 2 → Pt R n d) p.1 p.2`. Establish `hc : ∀ p, constantCoeff (c p) = 0` using `fun p => pair_points_zero_constant ha.1 hb.1 p.1 p.2`.

Establish `hex : ∀ m, ∃ ψ : JetR R (Fin 2 × Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m, ∀ j, ψ (zR m j) = toJet m (c j)` using `fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) c hc m).1`. Use `choose ψ hψ using hex`. Establish `sub` using `H2.2.2.2.2 (Fin n × Fin d) c ψ hc hψ`. Establish `hs : ∀ j : Fin 2, (fun i => MvPowerSeries.subst c (pt R (n` using `2) d j i)) = (![a, b] : Fin 2 → Pt R n d) j := fun j => funext fun i => gt_ev_X _ (pair_points_zero_constant ha.1 hb.1) j i`. Establish `e0 : (fun m => spMap (ψ m) ≫ Y 2 0 m) = y`.

Use `sub _ _ (hY 2 0)` as an intermediate fact. Rewrite `this` using `[hs 0]`. Conclude with `uP this ha`. Establish `e1 : (fun m => spMap (ψ m) ≫ Y 2 1 m) = z`. Use `sub _ _ (hY 2 1)` as an intermediate fact.

Rewrite `this` using `[hs 1]`. Conclude with `uP this hb`. Establish `key` using `sub _ _ hF`. Establish `e : (fun m => spMap (ψ m) ≫ (Y 2 0 m * Y 2 1 m)) = fun m => y m * z m`. Use function extensionality and compare the values at `m`.

Rewrite using `[MonObj.comp_mul, ← e0, ← e1]`. Rewrite using `[← e]`. Conclude with `key`. Use `⟨⟨F, hF.1, fun i => ?_, fun i => ?_, fun i => ?_⟩, law⟩` and prove the remaining obligations. Establish `h` using `law.2 1 _ _ _ _ (hR R G d x hx (Fin 1 × Fin d)).2.2.2.1 (hY 1 0)`.

Simplify using `only [_root_.one_mul] at h`. Conclude with `congrFun (uC h (hY 1 0)) i`. Establish `h` using `law.2 2 _ _ _ _ (hY 2 1) (hY 2 0)`. Establish `e : (fun m => Y 2 1 m * Y 2 0 m) = fun m => Y 2 0 m * Y 2 1 m`. Use function extensionality and compare the values at `fun m => _root_.mul_comm _ _`.

Rewrite `h` using `[e]`. Conclude with `congrFun (uC h hF) i`. Establish `h` using `law.2 3 _ _ _ _ (law.2 3 _ _ _ _ (hY 3 0) (hY 3 1)) (hY 3 2)`. Establish `h'` using `law.2 3 _ _ _ _ (hY 3 0) (law.2 3 _ _ _ _ (hY 3 1) (hY 3 2))`. Simplify using `only [_root_.mul_assoc] at h`.

Conclude with `congrFun (uC h h') i`.
-/
theorem lawSt_of (hJ : JetAlgSt) (hR : RepSt) : LawSt := by
  intro R _ G _ _ d x hx
  have uC : ∀ {n : ℕ} {a a' : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a' y → a = a' :=
    fun {n a a' y} h h' =>
      ((hR R G d x hx (Fin n × Fin d)).2.1 y ((hR R G d x hx (Fin n × Fin d)).2.2.1 a y h)).unique h h'
  have uP : ∀ {n : ℕ} {a : Pt R n d} {y y' : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a y' → y = y' :=
    fun {n a y y'} h h' => ((hR R G d x hx (Fin n × Fin d)).1 a h.1).unique h h'
  have gen : ∀ (n : ℕ) (j : Fin n), ∃ y : Fam G (Fin n × Fin d), Rep x (pt R d j) y :=
    fun n j => ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose Y hY using gen
  refine ⟨?_, fun F F' hF hF' => ?_⟩
  swap
  · rw [← addOf_pt_pt F, ← addOf_pt_pt F']
    exact uC (hF.2 2 _ _ _ _ (hY 2 0) (hY 2 1)) (hF'.2 2 _ _ _ _ (hY 2 0) (hY 2 1))
  have H2 := hR R G d x hx (Fin 2 × Fin d)
  obtain ⟨F, hF⟩ := (H2.2.1 _ (IsFPt.mul (H2.2.2.1 _ _ (hY 2 0)) (H2.2.2.1 _ _ (hY 2 1)))).exists
  have law : IsLawOf x F := by
    refine ⟨hF.1, fun n a b y z ha hb => ?_⟩
    let c : Fin 2 × Fin d → PS R n d := fun p => (![a, b] : Fin 2 → Pt R n d) p.1 p.2
    have hc : ∀ p, constantCoeff (c p) = 0 := fun p => pair_points_zero_constant ha.1 hb.1 p.1 p.2
    have hex : ∀ m, ∃ ψ : JetR R (Fin 2 × Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m,
        ∀ j, ψ (zR m j) = toJet m (c j) :=
      fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) c hc m).1
    choose ψ hψ using hex
    have sub := H2.2.2.2.2 (Fin n × Fin d) c ψ hc hψ
    have hs : ∀ j : Fin 2, (fun i => MvPowerSeries.subst c (pt R (n := 2) d j i)) = (![a, b] : Fin 2 → Pt R n d) j :=
      fun j => funext fun i => gt_ev_X _ (pair_points_zero_constant ha.1 hb.1) j i
    have e0 : (fun m => spMap (ψ m) ≫ Y 2 0 m) = y := by
      have := sub _ _ (hY 2 0)
      rw [hs 0] at this
      exact uP this ha
    have e1 : (fun m => spMap (ψ m) ≫ Y 2 1 m) = z := by
      have := sub _ _ (hY 2 1)
      rw [hs 1] at this
      exact uP this hb
    have key := sub _ _ hF
    have e : (fun m => spMap (ψ m) ≫ (Y 2 0 m * Y 2 1 m)) = fun m => y m * z m := by
      funext m
      rw [MonObj.comp_mul, ← e0, ← e1]
    rw [← e]
    exact key
  refine ⟨⟨F, hF.1, fun i => ?_, fun i => ?_, fun i => ?_⟩, law⟩
  · have h := law.2 1 _ _ _ _ (hR R G d x hx (Fin 1 × Fin d)).2.2.2.1 (hY 1 0)
    simp only [_root_.one_mul] at h
    exact congrFun (uC h (hY 1 0)) i
  · have h := law.2 2 _ _ _ _ (hY 2 1) (hY 2 0)
    have e : (fun m => Y 2 1 m * Y 2 0 m) = fun m => Y 2 0 m * Y 2 1 m :=
      funext fun m => _root_.mul_comm _ _
    rw [e] at h
    exact congrFun (uC h hF) i
  · have h := law.2 3 _ _ _ _ (law.2 3 _ _ _ _ (hY 3 0) (hY 3 1)) (hY 3 2)
    have h' := law.2 3 _ _ _ _ (hY 3 0) (law.2 3 _ _ _ _ (hY 3 1) (hY 3 2))
    simp only [_root_.mul_assoc] at h
    exact congrFun (uC h h') i

end GlobalTheory.JetSer
