import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfDisjointOpenCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfCechDisjointCover
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

/- English proof (translation)
Introduce `n` and use `⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩`.
-/
private theorem conn_mono {R : Type} [CommRing R] {F : Shv R} {c m : ℤ} (h : m ≤ c) {E E' : Spc} {f : E ⟶ E'}
    (hf : Conn R F c f) : Conn R F m f := fun n =>
  ⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩

/- English proof (translation)
Introduce `n`. Establish `hs` using `(a9 R F).1`. Use `⟨fun hn => ?_, fun hn => ?_⟩` and prove the remaining obligations. Use `haveI := hs E n (by omega) haveI := hs E' n (by omega)`. Conclude with `⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ y⟩⟩`.

Use `haveI := hs E' n (by omega)`. Conclude with `fun x y _ => Subsingleton.elim x y`.
-/
private theorem conn_nonpos (a9 : A9) {R : Type} [CommRing R] (F : Shv R) {m : ℤ} (h : m ≤ 0) {E E' : Spc} (f : E ⟶ E') :
    Conn R F m f := by
  intro n
  have hs := (a9 R F).1
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · haveI := hs E n (by omega)
    haveI := hs E' n (by omega)
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  · haveI := hs E' n (by omega)
    exact fun x y _ => Subsingleton.elim x y

/- English proof (translation)
Establish `hb : ∀ n, Function.Bijective (pull R f F n)` using `fun n => Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩`. Conclude with `fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩`.
-/
private theorem conn_iso {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') [IsIso f] :
    Conn R F c f := by
  have hb : ∀ n, Function.Bijective (pull R f F n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
      fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
      fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩
  exact fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩

/- English proof (translation)
The claim follows from `e ▸ h`.
-/
private theorem conn_congr {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U U' : X.Opens} (e : U = U')
    (h : Conn R F c (sch.map U.ι)) : Conn R F c (sch.map U'.ι) := e ▸ h

/- English proof (translation)
Substitute `e` using the available equality. Use `haveI : IsIso (⊤ : X.Opens).ι := by first`. Consider the case `infer_instance`. Consider the case `(rw [← Scheme.topIso_hom]; infer_instance)`. Consider the case `exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)`.

Conclude with `conn_iso F c _`.
-/
private theorem conn_top {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} {U : X.Opens} (e : U = ⊤) :
    Conn R F c (sch.map U.ι) := by
  subst e
  haveI : IsIso (⊤ : X.Opens).ι := by
    first
      | infer_instance
      | (rw [← Scheme.topIso_hom]; infer_instance)
      | exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact conn_iso F c _

/- English proof (translation)
Distinguish the cases in `hy : j y ∈ U`. Use `⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hy`. Rewrite using `[Scheme.Hom.comp_preimage]`.

Conclude with `Scheme.Opens.ι_preimage_self _`. Take `⟨Y', j', hj', hx, hsub, hC⟩` from `H (j y) hy j.opensRange ⟨y, rfl⟩`. Establish `hle : Set.range j' ⊆ Set.range j` using `hsub`. Establish `hfac : IsOpenImmersion.lift j j' hle ≫ j = j'` using `IsOpenImmersion.lift_fac j j' hle`. Use `haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'`.

Use `⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hx`. Use `⟨z, j.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← Scheme.Hom.comp_apply, hfac]`. Rewrite using `[hfac]`.

Conclude with `hC`.
-/
private theorem exists_good {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U : X.Opens}
    (H : ∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι))
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ∃ (O : Scheme.{0}) (o : O ⟶ Y) (_ : IsOpenImmersion o), y ∈ Set.range o ∧
      Conn R F c (sch.map ((o ≫ j) ⁻¹ᵁ U).ι) := by
  by_cases hy : j y ∈ U
  · refine ⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hy
    · rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _
  · obtain ⟨Y', j', hj', hx, hsub, hC⟩ := H (j y) hy j.opensRange ⟨y, rfl⟩
    have hle : Set.range j' ⊆ Set.range j := hsub
    have hfac : IsOpenImmersion.lift j j' hle ≫ j = j' := IsOpenImmersion.lift_fac j j' hle
    haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'
    refine ⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hx
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hfac]
    · rw [hfac]
      exact hC

/- English proof (translation)
Introduce `hLev hProd a1 a2 a9 R _ F c X U H`. Establish `main : ∀ k : ℕ, ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j], Conn R F (min c k) (sch.map (j ⁻¹ᵁ U).ι)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `Y j _`. Conclude with `conn_nonpos a9 F (by simp) _`. Consider the case `succ k ih`. Introduce `Y j _`. Establish `hmc : min c ((k + 1 : ℕ) : ℤ) ≤ c` using `min_le_left _ _`.

Establish `hm1 : min c ((k + 1 : ℕ) : ℤ) - 1 ≤ min c (k : ℤ)` using `by omega`. Use `choose O o ho hyo hc using fun y : Y => exists_good H j y`. Use `haveI := ho`. Establish `hcomp : ∀ a, Sigma.ι O a ≫ Sigma.desc o = o a` using `fun a => Sigma.ι_desc _ _`. Use `haveI hsurj : Surjective (Sigma.desc o) := ⟨fun y => by`.

Take `⟨z, hz⟩` from `hyo y`. Use `⟨Sigma.ι O y z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hcomp, hz]⟩`. Establish `hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (Sigma.ι O a)) (Set.range (Sigma.ι O b))` using `fun a b hab => by`. Use `disjoint_opensRange_sigmaι O a b hab` as an intermediate fact.

Rewrite using `[Set.disjoint_left]`. Introduce `x hxa hxb`. Conclude with `(disjoint_iff_inf_le.1 this : _) ⟨hxa, hxb⟩`. Establish `hcov : ∀ y : (∐ O : Scheme.{0}), ∃ a, y ∈ Set.range (Sigma.ι O a)` using `fun y => by`. Take `⟨a, z, hz⟩` from `(sigmaOpenCover O).exists_eq y`.

Conclude with `⟨a, z, hz⟩`. Use `UpperTheory.connectivity_of_cech_disjoint_cover hLev a1 a2 R F _ (Sigma.desc o) ⟨Y, O, Sigma.ι O, inferInstance, hdisj, hcov, fun a => by rw [hcomp]; exact ho a⟩ (j ⁻¹ᵁ U) ?_ ?_` and prove the remaining obligations. Use `UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O (Sigma.ι O) hdisj hcov _ fun a => ?_` and prove the remaining obligations. Use `conn_congr ?_ (conn_mono hmc (hc a))` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_preimage, ← hcomp a, Scheme.Hom.comp_preimage]`.

Introduce and unpack `Z g ⟨ι', O', j', hoi, hdis', hcov', hcp⟩ haveI := hoi`. Use `UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O' j' hdis' hcov' _ fun a => ?_` and prove the remaining obligations. Use `haveI := hcp a`. Use `conn_congr ?_ (conn_mono hm1 (ih ((j' a ≫ g) ≫ j)))` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]`.

Establish `hfin` using `main c.toNat (𝟙 X)`. Establish `hmin : min c (c.toNat : ℤ) = c` using `min_eq_left (Int.self_le_toNat c)`. Rewrite `hfin` using `[hmin]`. Conclude with `conn_congr (Scheme.Hom.id_preimage U) hfin`.
-/
theorem UpperTheory.leafProd_leafLoc_of_leafLevel :
    LeafLevel → LeafProd → LeafLoc := by
  intro hLev hProd a1 a2 a9 R _ F c X U H
  have main : ∀ k : ℕ, ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j],
      Conn R F (min c k) (sch.map (j ⁻¹ᵁ U).ι) := by
    intro k
    induction k with
    | zero =>
      intro Y j _
      exact conn_nonpos a9 F (by simp) _
    | succ k ih =>
      intro Y j _
      have hmc : min c ((k + 1 : ℕ) : ℤ) ≤ c := min_le_left _ _
      have hm1 : min c ((k + 1 : ℕ) : ℤ) - 1 ≤ min c (k : ℤ) := by omega
      choose O o ho hyo hc using fun y : Y => exists_good H j y
      haveI := ho
      have hcomp : ∀ a, Sigma.ι O a ≫ Sigma.desc o = o a := fun a => Sigma.ι_desc _ _
      haveI hsurj : Surjective (Sigma.desc o) := ⟨fun y => by
        obtain ⟨z, hz⟩ := hyo y
        refine ⟨Sigma.ι O y z, ?_⟩
        rw [← Scheme.Hom.comp_apply, hcomp, hz]⟩
      have hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (Sigma.ι O a)) (Set.range (Sigma.ι O b)) := fun a b hab => by
        have := disjoint_opensRange_sigmaι O a b hab
        rw [Set.disjoint_left]
        intro x hxa hxb
        exact (disjoint_iff_inf_le.1 this : _) ⟨hxa, hxb⟩
      have hcov : ∀ y : (∐ O : Scheme.{0}), ∃ a, y ∈ Set.range (Sigma.ι O a) := fun y => by
        obtain ⟨a, z, hz⟩ := (sigmaOpenCover O).exists_eq y
        exact ⟨a, z, hz⟩
      refine UpperTheory.connectivity_of_cech_disjoint_cover hLev a1 a2 R F _ (Sigma.desc o)
        ⟨Y, O, Sigma.ι O, inferInstance, hdisj, hcov, fun a => by rw [hcomp]; exact ho a⟩ (j ⁻¹ᵁ U) ?_ ?_
      · refine UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O (Sigma.ι O) hdisj hcov _ fun a => ?_
        refine conn_congr ?_ (conn_mono hmc (hc a))
        rw [Scheme.Hom.comp_preimage, ← hcomp a, Scheme.Hom.comp_preimage]
      · rintro Z g ⟨ι', O', j', hoi, hdis', hcov', hcp⟩
        haveI := hoi
        refine UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O' j' hdis' hcov' _ fun a => ?_
        haveI := hcp a
        refine conn_congr ?_ (conn_mono hm1 (ih ((j' a ≫ g) ≫ j)))
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hfin := main c.toNat (𝟙 X)
  have hmin : min c (c.toNat : ℤ) = c := min_eq_left (Int.self_le_toNat c)
  rw [hmin] at hfin
  exact conn_congr (Scheme.Hom.id_preimage U) hfin

end
