import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankBundle

variable {X : Scheme.{0}}

/- English proof (translation)
Rewrite using `[gs_eq (𝟙 X) x U h, map_one, map_one]`.
-/
theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) : gs (𝟙 X) x U 1 = 1 := by
  rw [gs_eq (𝟙 X) x U h, map_one, map_one]

/- English proof (translation)
Rewrite using `[gs_eq (𝟙 X) x U h]`. Conclude with `X.mem_basicOpen a x h`.
-/
theorem mem_basicOpen_iff (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)) :
    x ∈ X.basicOpen a ↔ IsUnit (gs (𝟙 X) x U a) := by
  rw [gs_eq (𝟙 X) x U h]
  exact X.mem_basicOpen a x h

/- English proof (translation)
Establish `hm : x ∈ N.U k ⊓ N.U k'` using `⟨hk, hk'⟩`. Conclude with `(gs_res (𝟙 X) x _ hm _).symm.trans ((congrArg (gs (𝟙 X) x _) (s.compat k k')).trans ((gs_mul (𝟙 X) x _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) x _ hm _) (gs_res (𝟙 X) x _ hm _))))`.
-/
theorem sec_compat {N : LB X} (s : LB.Sec N) (x : X) {k k' : N.ι} (hk : x ∈ N.U k) (hk' : x ∈ N.U k') :
    gs (𝟙 X) x (N.U k) (s.f k) = (gm (𝟙 X) x (N.U k ⊓ N.U k') (N.g k k')).val * gs (𝟙 X) x (N.U k') (s.f k') := by
  have hm : x ∈ N.U k ⊓ N.U k' := ⟨hk, hk'⟩
  exact (gs_res (𝟙 X) x _ hm _).symm.trans ((congrArg (gs (𝟙 X) x _) (s.compat k k')).trans
    ((gs_mul (𝟙 X) x _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) x _ hm _) (gs_res (𝟙 X) x _ hm _))))

/- English proof (translation)
Take `⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b)` from `X.toRingedSpace.isUnit_res_basicOpen b`. Use `⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a * (u⁻¹).val, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← gs_res (𝟙 X) x (X.basicOpen_le b) hx b, ← gs_res (𝟙 X) x (X.basicOpen_le b) hx a, ← gs_mul (𝟙 X) x _ hx, ← hu, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]`.
-/
theorem exists_ratio {U : X.Opens} (a b : Γ(X, U)) : ∃ r : Γ(X, X.basicOpen b), ∀ x ∈ X.basicOpen b,
    gs (𝟙 X) x (X.basicOpen b) r * gs (𝟙 X) x U b = gs (𝟙 X) x U a := by
  obtain ⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a * (u⁻¹).val, fun x hx => ?_⟩
  rw [← gs_res (𝟙 X) x (X.basicOpen_le b) hx b, ← gs_res (𝟙 X) x (X.basicOpen_le b) hx a,
    ← gs_mul (𝟙 X) x _ hx, ← hu, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

/- English proof (translation)
Introduce `X N n m w hN hcov hr`. Use `choose S hS using fun (l : Fin (n + 1)) (c : Fin (n + 1) × Fin (m + 1) × N.ι) => exists_ratio ((w l c.2.1).f c.2.2) ((w c.1 c.2.1).f c.2.2)`. Set `U : Fin (n + 1) × Fin (m + 1) × N.ι → X.Opens` to `fun c => X.basicOpen ((w c.1 c.2.1).f c.2.2)`. Establish `hle : ∀ c x, x ∈ U c → x ∈ N.U c.2.2` using `fun c x hx => X.basicOpen_le _ hx`. Establish `hu : ∀ c x, x ∈ U c → IsUnit (gs (𝟙 X) x (N.U c.2.2) ((w c.1 c.2.1).f c.2.2))` using `fun c x hx => (mem_basicOpen_iff x _ (hle c x hx) _).1 hx`.

Establish `one : ∀ c x, x ∈ U c → gs (𝟙 X) x (U c) (S c.1 c) = 1` using `fun c x hx => (hu c x hx).mul_right_cancel ((hS c.1 c x hx).trans (_root_.one_mul _).symm)`. Establish `key : ∀ l c c' x, x ∈ U c → x ∈ U c' → gs (𝟙 X) x (U c) (S l c) = gs (𝟙 X) x (U c) (S c'.1 c) * gs (𝟙 X) x (U c') (S l c')`. Introduce `l c c' x hx hx'`. Establish `e₁` using `hS l c x hx`. Establish `e₂` using `hS c'.1 c x hx`.

Establish `e₃` using `hS l c' x hx'`. Establish `e₄` using `congrArg (gs (𝟙 X) x (N.U c.2.2)) (hr l c'.1 c.2.1 c'.2.1 c.2.2)`. Rewrite `e₄` using `[gs_mul (𝟙 X) x _ (hle c x hx), gs_mul (𝟙 X) x _ (hle c x hx), sec_compat (w c'.1 c'.2.1) x (hle c x hx) (hle c' x hx'), sec_compat (w l c'.2.1) x (hle c x hx) (hle c' x hx')]`. Apply `(((hu c x hx).mul (hu c' x hx')).mul (gm (𝟙 X) x (N.U c.2.2 ⊓ N.U c'.2.2) (N.g c.2.2 c'.2.2)).isUnit).mul_right_cancel` to reduce the goal to its premises. Rewrite `e₄` using `[← e₁, ← e₂, ← e₃]`.

Conclude with `Eq.trans (by ring) (e₄.trans (by ring))`. Establish `hg : ∀ c c', IsUnit (rs X (inf_le_left : U c ⊓ U c' ≤ U c) (S c'.1 c))` using `fun c c' => IsUnit.of_mul_eq_one (rs X (inf_le_right : U c ⊓ U c' ≤ U c') (S c.1 c')) (fn_ext fun x hx => by`. Rewrite using `[gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, ← key c.1 c c' x hx.1 hx.2, one c x hx.1, gs_one x _ hx])`. Establish `gv : ∀ c c' x, x ∈ U c ⊓ U c' → (gm (𝟙 X) x (U c ⊓ U c') (hg c c').unit).val = gs (𝟙 X) x (U c) (S c'.1 c)` using `fun c c' x hx => (gs_unit (𝟙 X) x _ hx _).symm.trans (gs_res (𝟙 X) x _ hx _)`. Establish `ex : ∀ x : X, ∃ c, x ∈ U c` using `fun x => by`.

Establish `hx : x ∈ ⨆ i, ⨆ j, nonzeroLocus (w i j)` using `by rw [hcov]; trivial`. Take `⟨i, hx⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Take `⟨j, hx⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Take `⟨k, hx⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Conclude with `⟨(i, j, k), hx⟩`.

Set `H : LB X` to `⟨Fin (n + 1) × Fin (m + 1) × N.ι, U, fun c c' => (hg c c').unit⟩`. Set `s : Fin (n + 1) → LB.Sec H` to `fun l => ⟨S l, fun c c' => fn_ext fun x hx => (gs_res (𝟙 X) x _ hx _).trans ((key l c c' x hx.1 hx.2).trans ((gs_mul (𝟙 X) x _ hx _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)⟩`. Use `⟨H, s, ⟨?_, fun c => unit_ext fun x hx => Units.ext ?_, fun a b c => unit_ext fun x hx => Units.ext ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 (ex x)`. Rewrite using `[gm_res (𝟙 X) x _ hx, map_one, Units.val_one]`.

Conclude with `(gv c c x ⟨hx, hx⟩).trans (one c x hx)`. Rewrite using `[map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, Units.val_mul]`. Conclude with `(congrArg₂ (· * ·) (gv a b x hx.1) (gv b c x ⟨hx.1.2, hx.2⟩)).trans ((key c.1 a b x hx.1.1 hx.1.2).symm.trans (gv a c x ⟨hx.1.1, hx.2⟩).symm)`. Use `top_unique fun x _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `ex x`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨c.1, TopologicalSpace.Opens.mem_iSup.2 ⟨c, ?_⟩⟩` and prove the remaining obligations. Conclude with `(mem_basicOpen_iff x (U c) hc _).2 ((one c x hc).symm ▸ isUnit_one)`. Introduce `x c hc`. Use `⟨c.2.1, fun k hk => ⟨gm (𝟙 X) x (N.U k ⊓ N.U c.2.2) (N.g k c.2.2) * (hu c x hc).unit, fun l => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[sec_compat (w l c.2.1) x hk (hle c x hc), ← hS l c x hc, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]`.

Conclude with `congrArg _ (_root_.mul_comm _ _)`.
-/
theorem exists_rank_one_bundle : ∀ (X : Scheme.{0}) (N : LB X) (n m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → ∃ (H' : LB X) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB ∧ (⨆ i, nonzeroLocus (s' i) = ⊤) ∧ ∀ (x : X) (c : H'.ι), x ∈ H'.U c → ∃ j, ∀ k, x ∈ N.U k → ∃ v : (X.presheaf.stalk x)ˣ, ∀ i, gs (𝟙 X) x (N.U k) ((w i j).f k) = v.val * gs (𝟙 X) x (H'.U c) ((s' i).f c) := by
  intro X N n m w hN hcov hr
  choose S hS using fun (l : Fin (n + 1)) (c : Fin (n + 1) × Fin (m + 1) × N.ι) =>
    exists_ratio ((w l c.2.1).f c.2.2) ((w c.1 c.2.1).f c.2.2)
  let U : Fin (n + 1) × Fin (m + 1) × N.ι → X.Opens := fun c => X.basicOpen ((w c.1 c.2.1).f c.2.2)
  have hle : ∀ c x, x ∈ U c → x ∈ N.U c.2.2 := fun c x hx => X.basicOpen_le _ hx
  have hu : ∀ c x, x ∈ U c → IsUnit (gs (𝟙 X) x (N.U c.2.2) ((w c.1 c.2.1).f c.2.2)) := fun c x hx =>
    (mem_basicOpen_iff x _ (hle c x hx) _).1 hx
  have one : ∀ c x, x ∈ U c → gs (𝟙 X) x (U c) (S c.1 c) = 1 := fun c x hx =>
    (hu c x hx).mul_right_cancel ((hS c.1 c x hx).trans (_root_.one_mul _).symm)
  have key : ∀ l c c' x, x ∈ U c → x ∈ U c' →
      gs (𝟙 X) x (U c) (S l c) = gs (𝟙 X) x (U c) (S c'.1 c) * gs (𝟙 X) x (U c') (S l c') := by
    intro l c c' x hx hx'
    have e₁ := hS l c x hx
    have e₂ := hS c'.1 c x hx
    have e₃ := hS l c' x hx'
    have e₄ := congrArg (gs (𝟙 X) x (N.U c.2.2)) (hr l c'.1 c.2.1 c'.2.1 c.2.2)
    rw [gs_mul (𝟙 X) x _ (hle c x hx), gs_mul (𝟙 X) x _ (hle c x hx),
      sec_compat (w c'.1 c'.2.1) x (hle c x hx) (hle c' x hx'),
      sec_compat (w l c'.2.1) x (hle c x hx) (hle c' x hx')] at e₄
    apply (((hu c x hx).mul (hu c' x hx')).mul
      (gm (𝟙 X) x (N.U c.2.2 ⊓ N.U c'.2.2) (N.g c.2.2 c'.2.2)).isUnit).mul_right_cancel
    rw [← e₁, ← e₂, ← e₃] at e₄
    exact Eq.trans (by ring) (e₄.trans (by ring))
  have hg : ∀ c c', IsUnit (rs X (inf_le_left : U c ⊓ U c' ≤ U c) (S c'.1 c)) := fun c c' =>
    IsUnit.of_mul_eq_one (rs X (inf_le_right : U c ⊓ U c' ≤ U c') (S c.1 c')) (fn_ext fun x hx => by
      rw [gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, ← key c.1 c c' x hx.1 hx.2,
        one c x hx.1, gs_one x _ hx])
  have gv : ∀ c c' x, x ∈ U c ⊓ U c' →
      (gm (𝟙 X) x (U c ⊓ U c') (hg c c').unit).val = gs (𝟙 X) x (U c) (S c'.1 c) := fun c c' x hx =>
    (gs_unit (𝟙 X) x _ hx _).symm.trans (gs_res (𝟙 X) x _ hx _)
  have ex : ∀ x : X, ∃ c, x ∈ U c := fun x => by
    have hx : x ∈ ⨆ i, ⨆ j, nonzeroLocus (w i j) := by rw [hcov]; trivial
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨k, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨(i, j, k), hx⟩
  let H : LB X := ⟨Fin (n + 1) × Fin (m + 1) × N.ι, U, fun c c' => (hg c c').unit⟩
  let s : Fin (n + 1) → LB.Sec H := fun l => ⟨S l, fun c c' => fn_ext fun x hx =>
    (gs_res (𝟙 X) x _ hx _).trans ((key l c c' x hx.1 hx.2).trans ((gs_mul (𝟙 X) x _ hx _ _).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)⟩
  refine ⟨H, s, ⟨?_, fun c => unit_ext fun x hx => Units.ext ?_, fun a b c => unit_ext fun x hx => Units.ext ?_⟩, ?_, ?_⟩
  · exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 (ex x)
  · rw [gm_res (𝟙 X) x _ hx, map_one, Units.val_one]
    exact (gv c c x ⟨hx, hx⟩).trans (one c x hx)
  · rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, Units.val_mul]
    exact (congrArg₂ (· * ·) (gv a b x hx.1) (gv b c x ⟨hx.1.2, hx.2⟩)).trans
      ((key c.1 a b x hx.1.1 hx.1.2).symm.trans (gv a c x ⟨hx.1.1, hx.2⟩).symm)
  · refine top_unique fun x _ => ?_
    obtain ⟨c, hc⟩ := ex x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨c.1, TopologicalSpace.Opens.mem_iSup.2 ⟨c, ?_⟩⟩
    exact (mem_basicOpen_iff x (U c) hc _).2 ((one c x hc).symm ▸ isUnit_one)
  · intro x c hc
    refine ⟨c.2.1, fun k hk => ⟨gm (𝟙 X) x (N.U k ⊓ N.U c.2.2) (N.g k c.2.2) * (hu c x hc).unit, fun l => ?_⟩⟩
    rw [sec_compat (w l c.2.1) x hk (hle c x hc), ← hS l c x hc, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]
    exact congrArg _ (_root_.mul_comm _ _)

end GlobalTheory.RankBundle
