import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullDescent

section General
variable {X Y Y₃ E B G P S₀ : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {ε : K → ℤ}

/- English proof (translation)
Establish `hm` using `pullGen_isGen_of_isGen φ ε t ht m`. Establish `hs` using `pullGen_isGen_of_isGen φ ε t ht s`. Establish `hq` using `mulGen_isGen_of_isGen _ hm _ (invGen_isGen_of_isGen _ hs)`. Establish `hF : FormEq (Sum.elim (fun k => m ≫ φ k) (fun k => s ≫ φ k)) (Sum.elim ε fun k => -ε k) (PEmpty.elim : PEmpty → (P ⟶ X)) PEmpty.elim`. Introduce `U _ f`.

Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, h, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel, Finset.univ_eq_empty, Finset.prod_empty]`. Take `⟨q, -, hqv⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hM hF _ hq`. Set `j₀ : PEmpty → M.ι` to `PEmpty.elim`. Use `⟨res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := M) (Y := P) j₀).ge (q.s j₀), fun Z r z J hJ => ?_⟩` and prove the remaining obligations.

Establish `e₁` using `hqv Z r z J hJ`. Rewrite `e₁` using `[val_mul hJ, val_inv, val_pull hJ, val_pull hJ]`. Establish `e₂ : val q r z J = gm r z ⊤ (res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L` using `M) (Y := P) j₀).ge (q.s j₀)) := by`. Rewrite using `[val_of q r z J j₀ (fun k => k.elim)]`. Conclude with `(gm_res r z _ (by simp) _).symm`.

Rewrite using `[← e₂, e₁, inv_mul_cancel_right]`.
-/
theorem exists_ratio {M : LB X} (hM : M.IsLB) {φ : K → (Y ⟶ X)} (t : LB.Gen (LB.LinComb M φ ε)) (ht : t.IsGen)
    (m s : P ⟶ Y) (h : ∀ k, m ≫ φ k = s ≫ φ k) : ∃ ρ : Γ(P, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J),
      Good M z J → val t (r ≫ m) z J = gm r z ⊤ ρ * val t (r ≫ s) z J := by
  have hm := pullGen_isGen_of_isGen φ ε t ht m
  have hs := pullGen_isGen_of_isGen φ ε t ht s
  have hq := mulGen_isGen_of_isGen _ hm _ (invGen_isGen_of_isGen _ hs)
  have hF : FormEq (Sum.elim (fun k => m ≫ φ k) (fun k => s ≫ φ k)) (Sum.elim ε fun k => -ε k)
      (PEmpty.elim : PEmpty → (P ⟶ X)) PEmpty.elim := by
    intro U _ f
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, h, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel,
      Finset.univ_eq_empty, Finset.prod_empty]
  obtain ⟨q, -, hqv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hM hF _ hq
  let j₀ : PEmpty → M.ι := PEmpty.elim
  refine ⟨res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := M) (Y := P) j₀).ge (q.s j₀), fun Z r z J hJ => ?_⟩
  have e₁ := hqv Z r z J hJ
  rw [val_mul hJ, val_inv, val_pull hJ, val_pull hJ] at e₁
  have e₂ : val q r z J = gm r z ⊤ (res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := M) (Y := P) j₀).ge (q.s j₀)) := by
    rw [val_of q r z J j₀ (fun k => k.elim)]
    exact (gm_res r z _ (by simp) _).symm
  rw [← e₂, e₁, inv_mul_cancel_right]

/- English proof (translation)
Take `rfl : φf = fun k => φ k ≫ f` from `funext fun k => (hf k).symm`. Take `rfl : φp = fun k => φ k ≫ p` from `funext fun k => (hp k).symm`. Establish `hLf : (L.pull f).IsLB` using `pull_isLB hL f`. Establish `le : ∀ Q : K → (L.pull f).ι, LB.wchart (L.pull f) φ Q ≤ LB.wchart L (fun k => φ k ≫ f) (fun k => Q k PUnit.unit)` using `fun Q y hy => Set.mem_iInter.2 fun k => by`. Establish `h` using `(mem_pull (L := L) (F := f) (x := φ k y)).1 (Set.mem_iInter.1 hy k)`.

Simplify using `using h`. Set `a : LB.Gen (LB.LinComb (L.pull f) φ ε)` to `⟨fun Q => res (le Q) (b.s fun k => Q k PUnit.unit)⟩`. Establish `ha_gm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (Q : K → (L.pull f).ι), r z ∈ LB.wchart (L.pull f) φ Q → gm r z (LB.wchart (L.pull f) φ Q) (a.s Q) = gm r z (LB.wchart L (fun k => φ k ≫ f) (fun k => Q k PUnit.unit)) (b.s fun k => Q k PUnit.unit)` using `fun Z r z Q hz => gm_res r z (le Q) hz _`. Establish `ha : a.IsGen`. Use `isGen_of_gm a fun y Q Q' hy hy' => ?_` and prove the remaining obligations.

Rewrite using `[ha_gm Y (𝟙 Y) y Q hy, ha_gm Y (𝟙 Y) y Q' hy', gen_trans hb (𝟙 Y) y (le Q hy) (le Q' hy')]`. Use `congr 1`. Unfold `trF`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `h₁ : f ((𝟙 Y ≫ φ k) y) ∈ L.U (Q k PUnit.unit)`. Simplify using `using (mem_pull (L := L) (F := f) (x := φ k y)).1 (Set.mem_iInter.1 hy k)`. Establish `h₂ : f ((𝟙 Y ≫ φ k) y) ∈ L.U (Q' k PUnit.unit)`. Simplify using `using (mem_pull (L := L) (F := f) (x := φ k y)).1 (Set.mem_iInter.1 hy' k)`. Rewrite using `[← Category.assoc]`.

Conclude with `(GlobalTheory.FourthSide.gm_pull_g L f (𝟙 Y ≫ φ k) y _ _ h₁ h₂).symm`. Take `⟨t, ht, hv⟩` from `exists_up ((isGen_iff w).1 hw) hM hLf a ha`. Use `⟨t, ht, fun Z r z JG J hJG hJ => ?_⟩` and prove the remaining obligations. Establish `hP : r z ∈ LB.wchart M (fun k => φ k ≫ p) (fun k => J ((r ≫ φ k) ≫ p))`. Simplify `Good.mem hJ (fun k => φ k ≫ p) r` using `only [Category.assoc]`.

Establish `hQ : r z ∈ LB.wchart (L.pull f) φ (fun k _ => JG ((r ≫ φ k) ≫ f))` using `Set.mem_iInter.2 fun k => (mem_pull (L := L) (F := f) (x := φ k (r z))).2 (by simpa using hJG ((r ≫ φ k) ≫ f))`. Rewrite using `[val_of t r z J (fun k => J ((r ≫ φ k) ≫ p)) (fun k => by simp), hv Z r z _ _ hP hQ, ha_gm Z r z _ hQ, ← val_of b r z JG (fun k => JG ((r ≫ φ k) ≫ f)) (fun k => by simp)]`. Unfold `pw`. Conclude with `mul_comm _ _`.
-/
theorem exists_transport {L : LB G} {M : LB B} (hL : L.IsLB) (hM : M.IsLB) {f : E ⟶ G} {p : E ⟶ B}
    {w : LB.Iso (L.pull f) (M.pull p)} (hw : w.IsGen) (φ : K → (Y ⟶ E)) {φf : K → (Y ⟶ G)} {φp : K → (Y ⟶ B)}
    (hf : ∀ k, φ k ≫ f = φf k) (hp : ∀ k, φ k ≫ p = φp k) (b : LB.Gen (LB.LinComb L φf ε)) (hb : b.IsGen) :
    ∃ t : LB.Gen (LB.LinComb M φp ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (JG) (J),
      Good L z JG → Good M z J → val t r z J = val b r z JG *
        ∏ k, gw w (r ≫ φ k) z (J ((r ≫ φ k) ≫ p)) (fun _ => JG ((r ≫ φ k) ≫ f)) ^ ε k := by
  obtain rfl : φf = fun k => φ k ≫ f := funext fun k => (hf k).symm
  obtain rfl : φp = fun k => φ k ≫ p := funext fun k => (hp k).symm
  have hLf : (L.pull f).IsLB := pull_isLB hL f

  have le : ∀ Q : K → (L.pull f).ι,
      LB.wchart (L.pull f) φ Q ≤ LB.wchart L (fun k => φ k ≫ f) (fun k => Q k PUnit.unit) :=
    fun Q y hy => Set.mem_iInter.2 fun k => by
      have h := (mem_pull (L := L) (F := f) (x := φ k y)).1 (Set.mem_iInter.1 hy k)
      simpa using h
  let a : LB.Gen (LB.LinComb (L.pull f) φ ε) := ⟨fun Q => res (le Q) (b.s fun k => Q k PUnit.unit)⟩
  have ha_gm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (Q : K → (L.pull f).ι),
      r z ∈ LB.wchart (L.pull f) φ Q → gm r z (LB.wchart (L.pull f) φ Q) (a.s Q) =
        gm r z (LB.wchart L (fun k => φ k ≫ f) (fun k => Q k PUnit.unit)) (b.s fun k => Q k PUnit.unit) :=
    fun Z r z Q hz => gm_res r z (le Q) hz _
  have ha : a.IsGen := by
    refine isGen_of_gm a fun y Q Q' hy hy' => ?_
    rw [ha_gm Y (𝟙 Y) y Q hy, ha_gm Y (𝟙 Y) y Q' hy', gen_trans hb (𝟙 Y) y (le Q hy) (le Q' hy')]
    congr 1
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    have h₁ : f ((𝟙 Y ≫ φ k) y) ∈ L.U (Q k PUnit.unit) := by
      simpa using (mem_pull (L := L) (F := f) (x := φ k y)).1 (Set.mem_iInter.1 hy k)
    have h₂ : f ((𝟙 Y ≫ φ k) y) ∈ L.U (Q' k PUnit.unit) := by
      simpa using (mem_pull (L := L) (F := f) (x := φ k y)).1 (Set.mem_iInter.1 hy' k)
    rw [← Category.assoc]
    exact (GlobalTheory.FourthSide.gm_pull_g L f (𝟙 Y ≫ φ k) y _ _ h₁ h₂).symm
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hM hLf a ha
  refine ⟨t, ht, fun Z r z JG J hJG hJ => ?_⟩
  have hP : r z ∈ LB.wchart M (fun k => φ k ≫ p) (fun k => J ((r ≫ φ k) ≫ p)) := by
    simpa only [Category.assoc] using Good.mem hJ (fun k => φ k ≫ p) r
  have hQ : r z ∈ LB.wchart (L.pull f) φ (fun k _ => JG ((r ≫ φ k) ≫ f)) :=
    Set.mem_iInter.2 fun k => (mem_pull (L := L) (F := f) (x := φ k (r z))).2 (by simpa using hJG ((r ≫ φ k) ≫ f))
  rw [val_of t r z J (fun k => J ((r ≫ φ k) ≫ p)) (fun k => by simp), hv Z r z _ _ hP hQ, ha_gm Z r z _ hQ,
    ← val_of b r z JG (fun k => JG ((r ≫ φ k) ≫ f)) (fun k => by simp)]
  unfold pw
  exact mul_comm _ _

/- English proof (translation)
Establish `hW : ∀ j : K → M.ι, q ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => q ≫ ψ k) j` using `fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k`. Establish `hs : ∀ j : K → M.ι, ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ E) (z : Z), g₁ ≫ q = g₂ ≫ q → q (g₂ z) ∈ LB.wchart M ψ j → gm g₁ z (LB.wchart M (fun k => q ≫ ψ k) j) (t.s j) = gm g₂ z (LB.wchart M (fun k => q ≫ ψ k) j) (t.s j)`. Introduce `j Z g₁ g₂ z e hz`. Take `⟨J, hJ⟩` from `GlobalTheory.UU.exists_good_pt hM z`. Establish `e' : ∀ k, g₁ ≫ q ≫ ψ k = g₂ ≫ q ≫ ψ k` using `fun k => by rw [← Category.assoc, e, Category.assoc]`.

Establish `hq : q (g₁ z) = q (g₂ z)`. Use `congrArg (fun f : Z ⟶ Y => f z) e` as an intermediate fact. Simplify using `using this`. Establish `h₁ : g₁ z ∈ LB.wchart M (fun k => q ≫ ψ k) j` using `hW j (show q (g₁ z) ∈ LB.wchart M ψ j from hq ▸ hz)`. Establish `h₂ : g₂ z ∈ LB.wchart M (fun k => q ≫ ψ k) j` using `hW j hz`.

Rewrite using `[gen_trans ht g₁ z h₁ (Good.mem hJ _ g₁), gen_trans ht g₂ z h₂ (Good.mem hJ _ g₂)]`. Establish `hv` using `h Z g₁ g₂ z J hJ e`. Establish `hr : trF (fun k => q ≫ ψ k) ε g₁ z j (fun k => J (g₁ ≫ q ≫ ψ k)) = trF (fun k => q ≫ ψ k) ε g₂ z j (fun k => J (g₂ ≫ q ≫ ψ k))`. Establish `hJ' : (fun k => J (g₁ ≫ q ≫ ψ k)) = (fun k => J (g₂ ≫ q ≫ ψ k))` using `funext fun k => by rw [e' k]`. Rewrite using `[hJ']`.

Simplify using `only [trF, e']`. Conclude with `congrArg₂ (· * ·) hr hv`. Use `choose S hS using fun j => GlobalTheory.LevelComparison.exists_unit_descend q (LB.wchart M ψ j) _ (hW j) (t.s j) (hs j)`. Use `⟨⟨S⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Apply `GlobalTheory.LevelComparison.unit_ext_of_flat q` to reduce the goal to its premises. Introduce `x hx`. Establish `hi : q x ∈ LB.wchart M ψ i` using `hx.1`. Establish `hj : q x ∈ LB.wchart M ψ j` using `hx.2`. Establish `Si` using `hS i E (𝟙 E) x hi`.

Establish `Sj` using `hS j E (𝟙 E) x hj`. Rewrite `Si`, `Sj` using `[Category.id_comp]`. Rewrite using `[map_mul, gm_res q x _ hx, gm_res q x _ hx]`. Express the relevant statement in the definitionally equal form `gm q x (LB.wchart M ψ i) (S i) = gm q x (LB.wchart M ψ i ⊓ LB.wchart M ψ j) ((LB.LinComb M ψ ε).g i j) * gm q x (LB.wchart M ψ j) (S j)`. Rewrite using `[Si, Sj, gm_linComb M ψ ε q x i j hi hj, gen_trans ht (𝟙 E) x (hW i hi) (hW j hj)]`.

Simplify using `only [trF, Category.id_comp]`. Introduce `Z r z J hJ`. Establish `hm : q (r z) ∈ LB.wchart M ψ (fun k => J ((r ≫ q) ≫ ψ k))` using `Good.mem hJ ψ (r ≫ q)`. Rewrite using `[val_of (φ := ψ) _ (r ≫ q) z J (fun k => J ((r ≫ q) ≫ ψ k)) (fun k => rfl), hS _ Z r z hm, val_of t r z J (fun k => J ((r ≫ q) ≫ ψ k)) (fun k => by simp only [Category.assoc])]`.
-/
theorem exists_descend {M : LB B} (hM : M.IsLB) (q : E ⟶ Y) [Flat q] [Surjective q] [QuasiCompact q]
    (ψ : K → (Y ⟶ B)) (t : LB.Gen (LB.LinComb M (fun k => q ≫ ψ k) ε)) (ht : t.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ E) (z : Z) (J), Good M z J → g₁ ≫ q = g₂ ≫ q →
      val t g₁ z J = val t g₂ z J) :
    ∃ s : LB.Gen (LB.LinComb M ψ ε), s.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (J), Good M z J →
      val s (r ≫ q) z J = val t r z J := by
  have hW : ∀ j : K → M.ι, q ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => q ≫ ψ k) j := fun j x hx =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have hs : ∀ j : K → M.ι, ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ E) (z : Z), g₁ ≫ q = g₂ ≫ q →
      q (g₂ z) ∈ LB.wchart M ψ j → gm g₁ z (LB.wchart M (fun k => q ≫ ψ k) j) (t.s j) =
        gm g₂ z (LB.wchart M (fun k => q ≫ ψ k) j) (t.s j) := by
    intro j Z g₁ g₂ z e hz
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hM z
    have e' : ∀ k, g₁ ≫ q ≫ ψ k = g₂ ≫ q ≫ ψ k := fun k => by rw [← Category.assoc, e, Category.assoc]
    have hq : q (g₁ z) = q (g₂ z) := by
      have := congrArg (fun f : Z ⟶ Y => f z) e
      simpa using this
    have h₁ : g₁ z ∈ LB.wchart M (fun k => q ≫ ψ k) j := hW j (show q (g₁ z) ∈ LB.wchart M ψ j from hq ▸ hz)
    have h₂ : g₂ z ∈ LB.wchart M (fun k => q ≫ ψ k) j := hW j hz
    rw [gen_trans ht g₁ z h₁ (Good.mem hJ _ g₁), gen_trans ht g₂ z h₂ (Good.mem hJ _ g₂)]
    have hv := h Z g₁ g₂ z J hJ e
    have hr : trF (fun k => q ≫ ψ k) ε g₁ z j (fun k => J (g₁ ≫ q ≫ ψ k)) =
        trF (fun k => q ≫ ψ k) ε g₂ z j (fun k => J (g₂ ≫ q ≫ ψ k)) := by
      have hJ' : (fun k => J (g₁ ≫ q ≫ ψ k)) = (fun k => J (g₂ ≫ q ≫ ψ k)) := funext fun k => by rw [e' k]
      rw [hJ']
      simp only [trF, e']
    exact congrArg₂ (· * ·) hr hv
  choose S hS using fun j => GlobalTheory.LevelComparison.exists_unit_descend q (LB.wchart M ψ j) _ (hW j) (t.s j) (hs j)
  refine ⟨⟨S⟩, ?_, ?_⟩
  · intro i j
    apply GlobalTheory.LevelComparison.unit_ext_of_flat q
    intro x hx
    have hi : q x ∈ LB.wchart M ψ i := hx.1
    have hj : q x ∈ LB.wchart M ψ j := hx.2
    have Si := hS i E (𝟙 E) x hi
    have Sj := hS j E (𝟙 E) x hj
    rw [Category.id_comp] at Si Sj
    rw [map_mul, gm_res q x _ hx, gm_res q x _ hx]
    change gm q x (LB.wchart M ψ i) (S i) = gm q x (LB.wchart M ψ i ⊓ LB.wchart M ψ j) ((LB.LinComb M ψ ε).g i j) *
      gm q x (LB.wchart M ψ j) (S j)
    rw [Si, Sj, gm_linComb M ψ ε q x i j hi hj,
      gen_trans ht (𝟙 E) x (hW i hi) (hW j hj)]
    simp only [trF, Category.id_comp]
  · intro Z r z J hJ
    have hm : q (r z) ∈ LB.wchart M ψ (fun k => J ((r ≫ q) ≫ ψ k)) := Good.mem hJ ψ (r ≫ q)
    rw [val_of (φ := ψ) _ (r ≫ q) z J (fun k => J ((r ≫ q) ≫ ψ k)) (fun k => rfl), hS _ Z r z hm,
      val_of t r z J (fun k => J ((r ≫ q) ≫ ψ k)) (fun k => by simp only [Category.assoc])]

/- English proof (translation)
The claim follows from `(GlobalTheory.KerPow.pull_iff φ ε g).2 ⟨t, ht⟩`.
-/
theorem triv_pull {M : LB X} {φ : K → (Y ⟶ X)} (g : P ⟶ Y) (t : LB.Gen (LB.LinComb M (fun k => g ≫ φ k) ε))
    (ht : t.IsGen) : AbLaw.Triv ((LB.LinComb M φ ε).pull g) :=
  (GlobalTheory.KerPow.pull_iff φ ε g).2 ⟨t, ht⟩

/- English proof (translation)
Establish `hle : ∀ (j : K' × K → M.ι) (i : K'), LB.wchart M (fun p : K' × K => ψ p.1 ≫ φ p.2) j ≤ ψ i ⁻¹ᵁ LB.wchart M φ (fun k => j (i, k))` using `fun j i x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (i, k)`. Set `u : LB.Gen (LB.LinComb M (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1))` to `⟨fun j => ∏ i, (res (hle j i) (pullU (ψ i) _ (t.s fun k => j (i, k)))) ^ δ i⟩`. Establish `E : ∀ {Z : Scheme.{0}} (r : Z ⟶ P) (z : Z) (j : K' × K → M.ι) (hz : r z ∈ LB.wchart M (fun p : K' × K => ψ p.1 ≫ φ p.2) j), gm r z (LB.wchart M (fun p : K' × K => ψ p.1 ≫ φ p.2) j) (u.s j) = ∏ i, gm (r ≫ ψ i) z (LB.wchart M φ fun k => j (i, k)) (t.s fun k => j (i, k)) ^ δ i`. Introduce `Z r z j hz`. Use `show gm r z _ (∏ i, _) = _`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow, gm_res r z (hle j i) hz]`. Conclude with `congrArg (· ^ δ i) (gm_pull r (ψ i) z _ (hle j i hz) _)`. Use `⟨u, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a b`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[map_mul, gm_res (𝟙 P) x _ hx, gm_res (𝟙 P) x _ hx]`. Use `erw [E (𝟙 P) x a hx.1, E (𝟙 P) x b hx.2]`.

Establish `hg : ∀ i, gm (𝟙 P ≫ ψ i) x (LB.wchart M φ fun k => a (i, k)) (t.s fun k => a (i, k)) = trF φ ε (𝟙 P ≫ ψ i) x (fun k => a (i, k)) (fun k => b (i, k)) * gm (𝟙 P ≫ ψ i) x (LB.wchart M φ fun k => b (i, k)) (t.s fun k => b (i, k))` using `fun i => gen_trans ht (𝟙 P ≫ ψ i) x (hle a i hx.1) (hle b i hx.2)`. Simplify using `only [hg, mul_zpow, Finset.prod_mul_distrib]`. Use `congr 1`. Use `symm`. Use `show gm (𝟙 P) x _ (∏ p, _) = _`.

Use `erw [map_prod (gm (𝟙 P) x _)]`. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `trF`. Rewrite using `[← Finset.prod_zpow]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `mem : (ψ i ≫ φ k) ((𝟙 P : P ⟶ P) x) ∈ M.U (a (i, k)) ⊓ M.U (b (i, k))` using `⟨Set.mem_iInter.1 hx.1 (i, k), Set.mem_iInter.1 hx.2 (i, k)⟩`. Simplify using `only`. Use `erw [map_zpow, gm_res (𝟙 P) x _ hx]`. Rewrite using `[zpow_mul, Category.assoc]`.

Conclude with `congrArg (fun w => (w ^ ε k) ^ δ i) (gm_pull (𝟙 P) (ψ i ≫ φ k) x _ mem _)`. Introduce `Z r z J hJ show gm r z _ (u.s _) = _ erw [E r z _ (Good.mem hJ _ r)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[val_of t (r ≫ ψ i) z J _ fun k => by rw [Category.assoc]]`.
-/
theorem exists_prod {M : LB X} {φ : K → (Y ⟶ X)} (t : LB.Gen (LB.LinComb M φ ε)) (ht : t.IsGen)
    (ψ : K' → (P ⟶ Y)) (δ : K' → ℤ) :
    ∃ u : LB.Gen (LB.LinComb M (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J), Good M z J → val u r z J = ∏ i, val t (r ≫ ψ i) z J ^ δ i := by
  classical
  have hle : ∀ (j : K' × K → M.ι) (i : K'),
      LB.wchart M (fun p : K' × K => ψ p.1 ≫ φ p.2) j ≤ ψ i ⁻¹ᵁ LB.wchart M φ (fun k => j (i, k)) :=
    fun j i x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (i, k)
  let u : LB.Gen (LB.LinComb M (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1)) :=
    ⟨fun j => ∏ i, (res (hle j i) (pullU (ψ i) _ (t.s fun k => j (i, k)))) ^ δ i⟩
  have E : ∀ {Z : Scheme.{0}} (r : Z ⟶ P) (z : Z) (j : K' × K → M.ι)
      (hz : r z ∈ LB.wchart M (fun p : K' × K => ψ p.1 ≫ φ p.2) j),
      gm r z (LB.wchart M (fun p : K' × K => ψ p.1 ≫ φ p.2) j) (u.s j) =
        ∏ i, gm (r ≫ ψ i) z (LB.wchart M φ fun k => j (i, k)) (t.s fun k => j (i, k)) ^ δ i := by
    intro Z r z j hz
    show gm r z _ (∏ i, _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, gm_res r z (hle j i) hz]
    exact congrArg (· ^ δ i) (gm_pull r (ψ i) z _ (hle j i hz) _)
  refine ⟨u, ?_, ?_⟩
  · intro a b
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res (𝟙 P) x _ hx, gm_res (𝟙 P) x _ hx]
    erw [E (𝟙 P) x a hx.1, E (𝟙 P) x b hx.2]
    have hg : ∀ i, gm (𝟙 P ≫ ψ i) x (LB.wchart M φ fun k => a (i, k)) (t.s fun k => a (i, k)) =
        trF φ ε (𝟙 P ≫ ψ i) x (fun k => a (i, k)) (fun k => b (i, k)) *
          gm (𝟙 P ≫ ψ i) x (LB.wchart M φ fun k => b (i, k)) (t.s fun k => b (i, k)) := fun i =>
      gen_trans ht (𝟙 P ≫ ψ i) x (hle a i hx.1) (hle b i hx.2)
    simp only [hg, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    symm
    show gm (𝟙 P) x _ (∏ p, _) = _
    erw [map_prod (gm (𝟙 P) x _)]
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold trF
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    have mem : (ψ i ≫ φ k) ((𝟙 P : P ⟶ P) x) ∈ M.U (a (i, k)) ⊓ M.U (b (i, k)) :=
      ⟨Set.mem_iInter.1 hx.1 (i, k), Set.mem_iInter.1 hx.2 (i, k)⟩
    dsimp only
    erw [map_zpow, gm_res (𝟙 P) x _ hx]
    rw [zpow_mul, Category.assoc]
    exact congrArg (fun w => (w ^ ε k) ^ δ i) (gm_pull (𝟙 P) (ψ i ≫ φ k) x _ mem _)
  · intro Z r z J hJ
    show gm r z _ (u.s _) = _
    erw [E r z _ (Good.mem hJ _ r)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [val_of t (r ≫ ψ i) z J _ fun k => by rw [Category.assoc]]

/- English proof (translation)
Rewrite using `[Fintype.prod_equiv (Equiv.prodComm A B) (fun q : A × B => F q.2 q.1 ^ (-(d q.2 * e q.1))) (fun p : B × A => F p.1 p.2 ^ (-(d p.1 * e p.2))) (fun _ => rfl), ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun p _ => by rw [mul_comm (d p.1), zpow_neg, mul_inv_cancel]`.
-/
private theorem prod_pow_mul_prod_pow_neg_swap_eq_one {U : Type} [CommGroup U] {A B : Type} [Fintype A] [Fintype B]
    (F : B → A → U) (e : A → ℤ) (d : B → ℤ) :
    (∏ p : B × A, F p.1 p.2 ^ (e p.2 * d p.1)) * ∏ q : A × B, F q.2 q.1 ^ (-(d q.2 * e q.1)) = 1 := by
  rw [Fintype.prod_equiv (Equiv.prodComm A B) (fun q : A × B => F q.2 q.1 ^ (-(d q.2 * e q.1)))
      (fun p : B × A => F p.1 p.2 ^ (-(d p.1 * e p.2))) (fun _ => rfl),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => by rw [mul_comm (d p.1), zpow_neg, mul_inv_cancel]

/- English proof (translation)
Take `⟨U, hU, hUv⟩` from `exists_prod b hb ψ δ`. Take `⟨V, hV, hVv⟩` from `exists_prod c hc χ ε`. Establish `hW` using `mulGen_isGen_of_isGen _ hU _ (invGen_isGen_of_isGen _ hV)`. Take `⟨q, -, hq⟩` from `exists_gen hM (φ' := (PEmpty.elim : PEmpty → (P ⟶ X))) (ε' := PEmpty.elim) (by`. Introduce `U _ f`.

Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← h, Finset.univ_eq_empty, Finset.prod_empty]`. Conclude with `prod_pow_mul_prod_pow_neg_swap_eq_one (fun i k => f (ψ i ≫ φ k)) ε δ) _ hW`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ⟩ : ∃ ρ : Γ(P, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J), Good M z J → val U r z J * (val V r z J)⁻¹ = gm r z ⊤ ρ := by`. Use `⟨res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := M) (Y := P) PEmpty.elim).ge (q.s PEmpty.elim), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `e₁` using `hq Z r z J hJ`.

Rewrite `e₁` using `[val_mul hJ, val_inv]`. Rewrite using `[← e₁, val_of q r z J PEmpty.elim (fun k => k.elim)]`. Conclude with `(gm_res r z _ (by simp) _).symm`. Establish `h0 : ∀ y : S₀, gm e y ⊤ ρ = 1`. Introduce `y`.

Take `⟨J', hJ'⟩` from `GlobalTheory.UU.exists_good_pt hM y`. Rewrite using `[← hρ S₀ e y J' hJ', hUv S₀ e y J' hJ', hVv S₀ e y J' hJ']`. Simplify using `[nb _ y J' hJ', nc _ y J' hJ']`. Establish `h1 : Units.map e.appTop.hom.toMonoidHom ρ = 1`. Apply `unit_ext (V := ⊤)` to reduce the goal to its premises.

Introduce `x _`. Rewrite using `[← GlobalTheory.UU.gm_top, h0 x, map_one]`. Take `⟨a, ha⟩` from `hp ρ.val`. Establish `h2 : e.appTop.hom ρ.val = 1` using `by simpa using congrArg Units.val h1`. Establish `h3 : e.appTop.hom (p.appTop.hom a) = a`.

Establish `h3'` using `congrArg (fun g : S₀ ⟶ S₀ => g.appTop.hom a) he`. Simplify using `at h3'`. Conclude with `h3'`. Establish `h4 : ρ = 1`. Use `ext`.

Rewrite using `[← ha, ← h3, ha, h2, map_one, Units.val_one]`. Establish `h5` using `hρ Z r z J hJ`. Rewrite `h5` using `[h4, map_one, hUv Z r z J hJ, hVv Z r z J hJ]`. Conclude with `mul_inv_eq_one.mp h5`.
-/
theorem prod_comm_val {M : LB X} (hM : M.IsLB) {φ : K → (Y ⟶ X)} {θ : K' → (Y₃ ⟶ X)} {δ : K' → ℤ}
    (b : LB.Gen (LB.LinComb M φ ε)) (hb : b.IsGen) (c : LB.Gen (LB.LinComb M θ δ)) (hc : c.IsGen)
    (ψ : K' → (P ⟶ Y)) (χ : K → (P ⟶ Y₃)) (h : ∀ i k, ψ i ≫ φ k = χ k ≫ θ i)
    (p : P ⟶ S₀) (e : S₀ ⟶ P) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (nb : ∀ i y J, Good M y J → val b (e ≫ ψ i) y J = 1) (nc : ∀ k y J, Good M y J → val c (e ≫ χ k) y J = 1)
    (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J) (hJ : Good M z J) :
    ∏ i, val b (r ≫ ψ i) z J ^ δ i = ∏ k, val c (r ≫ χ k) z J ^ ε k := by
  obtain ⟨U, hU, hUv⟩ := exists_prod b hb ψ δ
  obtain ⟨V, hV, hVv⟩ := exists_prod c hc χ ε
  have hW := mulGen_isGen_of_isGen _ hU _ (invGen_isGen_of_isGen _ hV)
  obtain ⟨q, -, hq⟩ := exists_gen hM (φ' := (PEmpty.elim : PEmpty → (P ⟶ X))) (ε' := PEmpty.elim) (by
      intro U _ f
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← h, Finset.univ_eq_empty,
        Finset.prod_empty]
      exact prod_pow_mul_prod_pow_neg_swap_eq_one (fun i k => f (ψ i ≫ φ k)) ε δ) _ hW
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ(P, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J), Good M z J →
      val U r z J * (val V r z J)⁻¹ = gm r z ⊤ ρ := by
    refine ⟨res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := M) (Y := P) PEmpty.elim).ge (q.s PEmpty.elim),
      fun Z r z J hJ => ?_⟩
    have e₁ := hq Z r z J hJ
    rw [val_mul hJ, val_inv] at e₁
    rw [← e₁, val_of q r z J PEmpty.elim (fun k => k.elim)]
    exact (gm_res r z _ (by simp) _).symm

  have h0 : ∀ y : S₀, gm e y ⊤ ρ = 1 := by
    intro y
    obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt hM y
    rw [← hρ S₀ e y J' hJ', hUv S₀ e y J' hJ', hVv S₀ e y J' hJ']
    simp [nb _ y J' hJ', nc _ y J' hJ']
  have h1 : Units.map e.appTop.hom.toMonoidHom ρ = 1 := by
    apply unit_ext (V := ⊤)
    intro x _
    rw [← GlobalTheory.UU.gm_top, h0 x, map_one]
  obtain ⟨a, ha⟩ := hp ρ.val
  have h2 : e.appTop.hom ρ.val = 1 := by simpa using congrArg Units.val h1
  have h3 : e.appTop.hom (p.appTop.hom a) = a := by
    have h3' := congrArg (fun g : S₀ ⟶ S₀ => g.appTop.hom a) he
    simp at h3'
    exact h3'
  have h4 : ρ = 1 := by
    ext
    rw [← ha, ← h3, ha, h2, map_one, Units.val_one]
  have h5 := hρ Z r z J hJ
  rw [h4, map_one, hUv Z r z J hJ, hVv Z r z J hJ] at h5
  exact mul_inv_eq_one.mp h5

end General

/- English proof (translation)
Assume the negation of the conclusion as `hW`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, x ∉ W := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hW (eq_top_iff.2 fun x _ => hc x)`.

Establish `hcl : IsClosed (G.hom.base '' (W : Set G.left)ᶜ)` using `G.hom.isClosedMap _ W.isOpen.isClosed_compl`. Take `⟨m, hm, hpm⟩` from `Ideal.exists_le_maximal (G.hom.base x).asIdeal (G.hom.base x).isPrime.ne_top`. Establish `hIm : I ≤ m` using `(IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)`. Establish `hsp : G.hom.base x ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R)` using `(PrimeSpectrum.le_iff_specializes _ _).1 hpm`. Take `⟨y, hy, hym⟩` from `hsp.mem_closed hcl ⟨x, hx, rfl⟩`.

Establish `hle : I ^ (0 + 1) ≤ m` using `by simpa using hIm`. Establish `hpr : (Ideal.map (Ideal.Quotient.mk (I ^ (0 + 1))) m).IsPrime`. Use `hm.isPrime` as an intermediate fact. Conclude with `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)`. Set `q : PrimeSpectrum (R ⧸ I ^ (0 + 1))` to `⟨_, hpr⟩`.

Establish `hq : PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1))) q = ⟨m, hm.isPrime⟩` using `PrimeSpectrum.ext (Ideal.comap_map_mk hle)`. Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R I 0) y q (hym.trans hq.symm)`. Establish `hw'` using `h w`. Rewrite `hw'` using `[show (fstG I 0 G).left = pullback.fst G.hom (thick R I 0) from rfl]`. Conclude with `hy (hw ▸ hw')`.
-/
theorem eq_top_of_thick {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (G : Over (Spec (CommRingCat.of R))) [UniversallyClosed G.hom] (W : G.left.Opens)
    (h : ∀ z, (fstG I 0 G).left z ∈ W) : W = ⊤ := by
  by_contra hW
  obtain ⟨x, hx⟩ : ∃ x, x ∉ W := by
    by_contra hc
    push Not at hc
    exact hW (eq_top_iff.2 fun x _ => hc x)
  have hcl : IsClosed (G.hom.base '' (W : Set G.left)ᶜ) := G.hom.isClosedMap _ W.isOpen.isClosed_compl
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (G.hom.base x).asIdeal (G.hom.base x).isPrime.ne_top
  have hIm : I ≤ m := (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
  have hsp : G.hom.base x ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hpm
  obtain ⟨y, hy, hym⟩ := hsp.mem_closed hcl ⟨x, hx, rfl⟩
  have hle : I ^ (0 + 1) ≤ m := by simpa using hIm
  have hpr : (Ideal.map (Ideal.Quotient.mk (I ^ (0 + 1))) m).IsPrime := by
    have := hm.isPrime
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  let q : PrimeSpectrum (R ⧸ I ^ (0 + 1)) := ⟨_, hpr⟩
  have hq : PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1))) q = ⟨m, hm.isPrime⟩ :=
    PrimeSpectrum.ext (Ideal.comap_map_mk hle)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R I 0) y q
    (hym.trans hq.symm)
  have hw' := h w
  rw [show (fstG I 0 G).left = pullback.fst G.hom (thick R I 0) from rfl] at hw'
  exact hy (hw ▸ hw')

open AbLaw AbTriv in

/- English proof (translation)
Take `⟨c, hc⟩` from `h₀`. Establish `: UniversallyClosed B.hom` using `by have := hB.proper; infer_instance`. Establish `hsm : Smooth B.hom` using `hB.smooth`. Establish `he : eSec B ≫ B.hom = 𝟙 _`. Unfold `eSec`.

Rewrite using `[Over.w]`. Both sides reduce to the same expression. Establish `hpb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e)`. Introduce `e`. Unfold `fstG thickObj`.

Conclude with `IsPullback.of_hasPullback B.hom (thick V I e)`. Establish `hnorm : ∀ e, ∃ t : LB.Gen (N.pull (fstG I e B).left), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I e B).left) (b : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (J), Good N z J → r ≫ (fstG I e B).left = b ≫ eSec B → val t r z J = val c b z J` using `fun e => GlobalTheory.AbTriv.exists_normalised hN he c hc (hpb e) (ht e)`. Use `choose t htg htv using hnorm`. Establish `hcompat : ∀ e z J, Good N z J → sval (Geo.Tor.genSec (t (e + 1)) (htg (e + 1))) (thickMap V I e B) z J = sval (Geo.Tor.genSec (t e) (htg e)) (𝟙 _) z J`. Introduce `e z J hJ`.

Establish `hτ : thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left` using `by clear * -`. Unfold `thickMap fstG`. Simplify using `only [Over.homMk_left, pullback.lift_fst, Category.comp_id]`. Establish `hb` using `pullGen_isGen_of_isGen (L := N) (fun _ : PUnit => (fstG I (e + 1) B).left) (fun _ => 1) (t (e + 1)) (htg (e + 1)) (thickMap V I e B)`. Establish `hq` using `mulGen_isGen_of_isGen _ hb _ (invGen_isGen_of_isGen (L := N) (φ := fun _ : PUnit => (fstG I e B).left) (ε := fun _ => 1) (t e) (htg e))`.

Establish `hF : FormEq (Sum.elim (fun _ : PUnit => thickMap V I e B ≫ (fstG I (e + 1) B).left) (fun _ : PUnit => (fstG I e B).left)) (Sum.elim (fun _ => 1) fun _ => -1) (PEmpty.elim : PEmpty → ((thickObj V I e B).left ⟶ B.left)) PEmpty.elim`. Introduce `U _ f`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, hτ, zpow_one, zpow_neg, Finset.univ_unique, Finset.prod_singleton, mul_inv_cancel, Finset.univ_eq_empty, Finset.prod_empty]`. Take `⟨q, -, hqv⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF _ hq`.

Set `j₀ : PEmpty → N.ι` to `PEmpty.elim`. Establish `hratio : ∃ ρ : Γ((thickObj V I e B).left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I e B).left) (z : Z) (J), Good N z J → val (t (e + 1)) (r ≫ thickMap V I e B) z J = gm r z ⊤ ρ * val (t e) r z J`. Use `⟨res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := N) (Y := (thickObj V I e B).left) j₀).ge (q.s j₀), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `e₁` using `hqv Z r z J hJ`. Rewrite `e₁` using `[val_mul hJ, val_inv, val_pull hJ]`.

Establish `e₂ : val q r z J = gm r z ⊤ (res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L` using `N) (Y := (thickObj V I e B).left) j₀).ge (q.s j₀)) := by`. Rewrite using `[val_of q r z J j₀ (fun k => k.elim)]`. Conclude with `(gm_res r z _ (by simp) _).symm`. Rewrite using `[← e₂, e₁, inv_mul_cancel_right]`. Take `⟨ρ, hρv⟩` from `hratio`.

Establish `hρ : ρ = 1`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `hA : IsAbelianScheme (thickObj V I e B)`. Establish `: IsCommMonObj B` using `hB.1`.

Use `⟨inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Smooth (pullback.snd B.hom (thick V I e)) infer_instance`. Use `show IsProper (pullback.snd B.hom (thick V I e)) infer_instance`. Establish `: GeometricallyConnected B.hom` using `hB.4 show GeometricallyConnected (pullback.snd B.hom (thick V I e)) infer_instance`. Take `⟨a, ha⟩` from `(hG _ (thickObj V I e B) hA).2 ρ.val`.

Establish `hσc : (thick V I e ≫ eSec B) ≫ B.hom = 𝟙 _ ≫ thick V I e`. Rewrite using `[Category.assoc, he]`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`. Take `⟨σ, hσπ, hσp⟩ : ∃ σ : Spec (CommRingCat.of (V ⧸ I ^ (e + 1))) ⟶ (thickObj V I e B).left, σ ≫ (fstG I e B).left = thick V I e ≫ eSec B ∧ σ ≫ (thickObj V I e B).hom = 𝟙 _` from `⟨pullback.lift _ _ hσc, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Establish `hpt : ∀ w, gm σ w ⊤ ρ = 1`.

Introduce `w`. Take `⟨J', hJ'⟩` from `GlobalTheory.UU.exists_good_pt hN w`. Establish `h2` using `hρv _ σ w J' hJ'`. Rewrite `h2` using `[htv (e + 1) _ (σ ≫ thickMap V I e B) (thick V I e) w J' hJ' (by rw [Category.assoc, hτ, hσπ]), htv e _ σ (thick V I e) w J' hJ' hσπ]`. Conclude with `mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)`.

Establish `hσρ : Units.map σ.appTop.hom.toMonoidHom ρ = 1`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x _`. Rewrite using `[← GlobalTheory.UU.gm_top, hpt, map_one]`. Establish `h4 : (σ ≫ (thickObj V I e B).hom).appTop.hom a = σ.appTop.hom ρ.val`.

Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ha]`. Rewrite `h4` using `[hσp, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]`. Establish `h5 : σ.appTop.hom ρ.val = 1` using `congrArg Units.val hσρ`. Use `ext1`. Rewrite using `[← ha, h4, h5, map_one, Units.val_one]`.

Establish `h1` using `hρv _ (𝟙 _) z J hJ`. Rewrite `h1` using `[hρ, map_one, _root_.one_mul, Category.id_comp]`. Rewrite using `[sval_genSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ, h1]`. Apply the tactic sequence `all_goals rfl`. Take `⟨s, hs, -⟩` from `GlobalTheory.SecAlg.existsUnique_sec V I hV B hsm hp N hN (fun e => Geo.Tor.genSec (t e) (htg e)) hcompat`.

Establish `hmem : ∀ z, (fstG I 0 B).left z ∈ nonzeroLocus s`. Introduce `z`. Take `⟨J, hJ⟩` from `GlobalTheory.UU.exists_good_pt hN z`. Establish `e1` using `hs 0 z J hJ`. Rewrite `e1` using `[sval_genSec _ _ _ _ hJ]`.

Establish `hW` using `hJ.mem (fun _ : PUnit => 𝟙 B.left) (fstG I 0 B).left`. Unfold `sval at e1`. Use `beta_reduce at e1`. Use `replace e1 := (gs_eq _ z _ hW _).symm.trans e1`. Establish `hu` using `e1.symm ▸ Units.isUnit (val (t 0) (𝟙 _) z J)`.

Establish `hz` using `(Scheme.mem_basicOpen _ _ z hW).2 hu`. Establish `hz' : z ∈ (fstG I 0 B).left ⁻¹ᵁ B.left.basicOpen (s.f (fun _ => J ((fstG I 0 B).left ≫ 𝟙 B.left)))`. Rewrite using `[AlgebraicGeometry.Scheme.preimage_basicOpen]`. Conclude with `hz`. Unfold `nonzeroLocus`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨_, hz'⟩`. Establish `htop : nonzeroLocus s = ⊤` using `eq_top_of_thick I B (nonzeroLocus s) hmem`. Establish `hgen : Triv (N.pull (𝟙 B.left))` using `by clear * - htop`. Establish `hU : ∀ j, IsUnit (s.f j)`. Introduce `j`.

Use `B.left.toRingedSpace.isUnit_of_isUnit_germ _ (s.f j) fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ nonzeroLocus s` using `htop ▸ trivial`. Unfold `nonzeroLocus at hx'`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx'`. Establish `hxk : x ∈ (N.pull (𝟙 B.left)).U k` using `B.left.basicOpen_le _ hk`.

Establish `hxjk : x ∈ (N.pull (𝟙 B.left)).U j ⊓ (N.pull (𝟙 B.left)).U k` using `⟨hx, hxk⟩`. Establish `e1` using `congrArg (B.left.presheaf.germ _ x hxjk).hom (s.compat j k)`. Simplify using `only [map_mul, TopCat.Presheaf.germ_res_apply] at e1`. Establish `h3 : IsUnit (B.left.presheaf.germ _ x hx (s.f j))`. Rewrite using `[e1]`.

Conclude with `((N.pull (𝟙 B.left)).g j k).isUnit.map _ |>.mul ((B.left.mem_basicOpen (s.f k) x hxk).1 hk)`. Conclude with `h3`. Use `⟨⟨fun j => (hU j).unit⟩, fun i j => ?_⟩` and prove the remaining obligations. Use `ext1`. Simplify using `only [res, Units.coe_map, Units.val_mul, IsUnit.unit_spec]`.

Conclude with `s.compat i j`. Conclude with `GlobalTheory.AbTriv.triv_of_pull_id hgen`.
-/
theorem triv_of_thick (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) [hV : IsAdicComplete I V]
    (B : Over (Spec (CommRingCat.of V))) [GrpObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) (N : LB B.left)
    (hN : N.IsLB) (h₀ : Triv (N.pull (eSec B))) (ht : ∀ e, Triv (N.pull (fstG I e B).left)) : Triv N := by
  obtain ⟨c, hc⟩ := h₀
  have : UniversallyClosed B.hom := by have := hB.proper; infer_instance
  have hsm : Smooth B.hom := hB.smooth
  have he : eSec B ≫ B.hom = 𝟙 _ := by
    unfold eSec
    rw [Over.w]
    rfl
  have hpb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) := by
    intro e
    unfold fstG thickObj
    exact IsPullback.of_hasPullback B.hom (thick V I e)
  have hnorm : ∀ e, ∃ t : LB.Gen (N.pull (fstG I e B).left), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I e B).left)
      (b : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (J), Good N z J → r ≫ (fstG I e B).left = b ≫ eSec B →
        val t r z J = val c b z J := fun e => GlobalTheory.AbTriv.exists_normalised hN he c hc (hpb e) (ht e)
  choose t htg htv using hnorm
  have hcompat : ∀ e z J, Good N z J → sval (Geo.Tor.genSec (t (e + 1)) (htg (e + 1))) (thickMap V I e B) z J =
      sval (Geo.Tor.genSec (t e) (htg e)) (𝟙 _) z J := by
    intro e z J hJ
    have hτ : thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := by
      clear * -
      unfold thickMap fstG
      simp only [Over.homMk_left, pullback.lift_fst, Category.comp_id]
    have hb := pullGen_isGen_of_isGen (L := N) (fun _ : PUnit => (fstG I (e + 1) B).left) (fun _ => 1) (t (e + 1)) (htg (e + 1))
      (thickMap V I e B)
    have hq := mulGen_isGen_of_isGen _ hb _ (invGen_isGen_of_isGen (L := N) (φ := fun _ : PUnit => (fstG I e B).left) (ε := fun _ => 1) (t e) (htg e))
    have hF : FormEq (Sum.elim (fun _ : PUnit => thickMap V I e B ≫ (fstG I (e + 1) B).left)
        (fun _ : PUnit => (fstG I e B).left)) (Sum.elim (fun _ => 1) fun _ => -1)
        (PEmpty.elim : PEmpty → ((thickObj V I e B).left ⟶ B.left)) PEmpty.elim := by
      intro U _ f
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hτ, zpow_one, zpow_neg, Finset.univ_unique, Finset.prod_singleton,
        mul_inv_cancel, Finset.univ_eq_empty, Finset.prod_empty]
    obtain ⟨q, -, hqv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF _ hq
    let j₀ : PEmpty → N.ι := PEmpty.elim
    have hratio : ∃ ρ : Γ((thickObj V I e B).left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I e B).left) (z : Z) (J),
        Good N z J → val (t (e + 1)) (r ≫ thickMap V I e B) z J = gm r z ⊤ ρ * val (t e) r z J := by
      refine ⟨res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := N) (Y := (thickObj V I e B).left) j₀).ge (q.s j₀),
        fun Z r z J hJ => ?_⟩
      have e₁ := hqv Z r z J hJ
      rw [val_mul hJ, val_inv, val_pull hJ] at e₁
      have e₂ : val q r z J = gm r z ⊤ (res (ReciprocityTheory.ChartRestriction.G.DVR.wchart_empty (L := N) (Y := (thickObj V I e B).left) j₀).ge (q.s j₀)) := by
        rw [val_of q r z J j₀ (fun k => k.elim)]
        exact (gm_res r z _ (by simp) _).symm
      rw [← e₂, e₁, inv_mul_cancel_right]
    obtain ⟨ρ, hρv⟩ := hratio
    have hρ : ρ = 1 := by
      have := hB.smooth
      have := hB.proper
      have hA : IsAbelianScheme (thickObj V I e B) := by
        have : IsCommMonObj B := hB.1
        refine ⟨inferInstance, ?_, ?_, ?_⟩
        · show Smooth (pullback.snd B.hom (thick V I e))
          infer_instance
        · show IsProper (pullback.snd B.hom (thick V I e))
          infer_instance
        · have : GeometricallyConnected B.hom := hB.4
          show GeometricallyConnected (pullback.snd B.hom (thick V I e))
          infer_instance
      obtain ⟨a, ha⟩ := (hG _ (thickObj V I e B) hA).2 ρ.val
      have hσc : (thick V I e ≫ eSec B) ≫ B.hom = 𝟙 _ ≫ thick V I e := by
        rw [Category.assoc, he]
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      obtain ⟨σ, hσπ, hσp⟩ : ∃ σ : Spec (CommRingCat.of (V ⧸ I ^ (e + 1))) ⟶ (thickObj V I e B).left,
          σ ≫ (fstG I e B).left = thick V I e ≫ eSec B ∧ σ ≫ (thickObj V I e B).hom = 𝟙 _ :=
        ⟨pullback.lift _ _ hσc, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
      have hpt : ∀ w, gm σ w ⊤ ρ = 1 := by
        intro w
        obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt hN w
        have h2 := hρv _ σ w J' hJ'
        rw [htv (e + 1) _ (σ ≫ thickMap V I e B) (thick V I e) w J' hJ' (by rw [Category.assoc, hτ, hσπ]),
          htv e _ σ (thick V I e) w J' hJ' hσπ] at h2
        exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
      have hσρ : Units.map σ.appTop.hom.toMonoidHom ρ = 1 := by
        apply unit_ext
        intro x _
        rw [← GlobalTheory.UU.gm_top, hpt, map_one]
      have h4 : (σ ≫ (thickObj V I e B).hom).appTop.hom a = σ.appTop.hom ρ.val := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ha]
      rw [hσp, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at h4
      have h5 : σ.appTop.hom ρ.val = 1 := congrArg Units.val hσρ
      ext1
      rw [← ha, h4, h5, map_one, Units.val_one]
    have h1 := hρv _ (𝟙 _) z J hJ
    rw [hρ, map_one, _root_.one_mul, Category.id_comp] at h1
    rw [sval_genSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ, h1]
    all_goals rfl
  obtain ⟨s, hs, -⟩ := GlobalTheory.SecAlg.existsUnique_sec V I hV B hsm hp N hN (fun e => Geo.Tor.genSec (t e) (htg e)) hcompat
  have hmem : ∀ z, (fstG I 0 B).left z ∈ nonzeroLocus s := by
    intro z
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hN z
    have e1 := hs 0 z J hJ
    rw [sval_genSec _ _ _ _ hJ] at e1
    have hW := hJ.mem (fun _ : PUnit => 𝟙 B.left) (fstG I 0 B).left
    unfold sval at e1
    beta_reduce at e1
    replace e1 := (gs_eq _ z _ hW _).symm.trans e1
    have hu := e1.symm ▸ Units.isUnit (val (t 0) (𝟙 _) z J)
    have hz := (Scheme.mem_basicOpen _ _ z hW).2 hu
    have hz' : z ∈ (fstG I 0 B).left ⁻¹ᵁ B.left.basicOpen (s.f (fun _ => J ((fstG I 0 B).left ≫ 𝟙 B.left))) := by
      rw [AlgebraicGeometry.Scheme.preimage_basicOpen]
      exact hz
    unfold nonzeroLocus
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hz'⟩
  have htop : nonzeroLocus s = ⊤ := eq_top_of_thick I B (nonzeroLocus s) hmem
  have hgen : Triv (N.pull (𝟙 B.left)) := by
    clear * - htop
    have hU : ∀ j, IsUnit (s.f j) := by
      intro j
      refine B.left.toRingedSpace.isUnit_of_isUnit_germ _ (s.f j) fun x hx => ?_
      have hx' : x ∈ nonzeroLocus s := htop ▸ trivial
      unfold nonzeroLocus at hx'
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      have hxk : x ∈ (N.pull (𝟙 B.left)).U k := B.left.basicOpen_le _ hk
      have hxjk : x ∈ (N.pull (𝟙 B.left)).U j ⊓ (N.pull (𝟙 B.left)).U k := ⟨hx, hxk⟩
      have e1 := congrArg (B.left.presheaf.germ _ x hxjk).hom (s.compat j k)
      simp only [map_mul, TopCat.Presheaf.germ_res_apply] at e1
      have h3 : IsUnit (B.left.presheaf.germ _ x hx (s.f j)) := by
        rw [e1]
        exact ((N.pull (𝟙 B.left)).g j k).isUnit.map _ |>.mul ((B.left.mem_basicOpen (s.f k) x hxk).1 hk)
      exact h3
    refine ⟨⟨fun j => (hU j).unit⟩, fun i j => ?_⟩
    ext1
    simp only [res, Units.coe_map, Units.val_mul, IsUnit.unit_spec]
    exact s.compat i j
  exact GlobalTheory.AbTriv.triv_of_pull_id hgen

end GlobalTheory.UT.PullDescent
end
