import Development.EtaleCohomology.TateTwists.CupflipAwExistsPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
    (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def cupflip_ev_res : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h
    (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)

def cupflip_sub_res : Prop :=
  ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) {V : Scheme.{0}} (g : V ⟶ U),
    (x.res g).sub j l h = (x.sub j l h).res g

/- English proof (translation)
Introduce `R _ I J K μ E n m k hk α β`. Take `⟨γ, hγ⟩` from `hm R (E := E) (I := K) (n := k) (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega) (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))) (by`. Introduce `N w h V U g x`. Simplify using `only [Sec.res, map_sum, Units.smul_def, map_zsmul]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations.

Use `congr 1`. Use `μ.nat g (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega) (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))` as an intermediate fact. Simplify using `only [Sec.res] at this`. Rewrite using `[this]`. Establish `e1` using `he R α p _ rfl V U g (x.sub 0 p (by omega))`.

Establish `e2` using `he R β (N - p) _ rfl V U g (x.sub p (N - p) (by omega))`. Simplify using `only [Sec.res] at e1 e2`. Rewrite using `[e1, e2, hs, hs])`. Conclude with `⟨γ, fun N w h U x => hγ N w h U x⟩`.
-/
theorem cupflip_aw_cochain_of (hm : cupflip_ev_mk) (he : cupflip_ev_res) (hs : cupflip_sub_res) :
    cupflip_aw_cochain := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hm R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x
      simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      congr 1
      have := μ.nat g (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
        (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))
      simp only [Sec.res] at this
      rw [this]
      have e1 := he R α p _ rfl V U g (x.sub 0 p (by omega))
      have e2 := he R β (N - p) _ rfl V U g (x.sub p (N - p) (by omega))
      simp only [Sec.res] at e1 e2
      rw [e1, e2, hs, hs])
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

/- English proof (translation)
Introduce `E U N x j l h V g`. Simplify using `only [Sx.res, Sx.sub]`. Conclude with `NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x`.
-/
theorem cupflip_sub_res_holds : cupflip_sub_res := by
  intro E U N x j l h V g
  simp only [Sx.res, Sx.sub]
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

/- English proof (translation)
Establish `key` using `NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x))`. Simplify using `only [freeGen]`. Use `erw [← key]`. Use `congr 1`. Simplify using `only [freeP, ModuleCat.freeMk, ModuleCat.free]`.

Use `erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`. Both sides reduce to the same expression.
-/
theorem freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x))
  simp only [freeGen]
  erw [← key]
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

/- English proof (translation)
Introduce `R _ E I n α p s h V U g x`. Establish `key` using `NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op (freeGen R _ U x)`. Simplify using `only [Sec.res, ev]`. Use `erw [← key]`. Use `congr 1`.

Conclude with `freeGen_res _ g x`.
-/
theorem cupflip_ev_res_holds : cupflip_ev_res := by
  intro R _ E I n α p s h V U g x
  have key := NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op (freeGen R _ U x)
  simp only [Sec.res, ev]
  erw [← key]
  congr 1
  exact freeGen_res _ g x

/- English proof (translation)
The claim follows from `cupflip_aw_exists_of (cupflip_aw_cochain_of hm cupflip_ev_res_holds cupflip_sub_res_holds) hl`.
-/
theorem cupflip_aw_exists_of_leaves (hm : cupflip_ev_mk) (hl : cupflip_aw_leibniz) :
    cupflip_aw_exists :=
  cupflip_aw_exists_of (cupflip_aw_cochain_of hm cupflip_ev_res_holds cupflip_sub_res_holds) hl

end LateralTheory.EtaleFoundations
