import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

/- English proof (translation)
The claim follows from `| 0 => by rw [cpow_zero, cpow_zero, pull_cast, (h q).2.1 f hI] | k + 1 => by rw [cpow_succ, cpow_succ, pull_cast, (h q).1, pull_cpow h q f hI x k]`.
-/
theorem pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E') (x : Ht q E' 2 1) :
    ∀ k : ℕ, pull _ f (tw q k) (2 * k) (cpow q x k) = cpow q (pull _ f (tw q 1) 2 x) k
  | 0 => by
    rw [cpow_zero, cpow_zero, pull_cast, (h q).2.1 f hI]
  | k + 1 => by
    rw [cpow_succ, cpow_succ, pull_cast, (h q).1, pull_cpow h q f hI x k]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q 1) 2 (c1 q (prod.fst ≫ Pj.line (d + 1) 0)) = c1 q (prod.fst ≫ Pj.line (d + 1) 1)`. Rewrite using `[(h q).2.2.1 _ _ hI, prod.map_fst_assoc, Pj.incl_line]`.
-/
theorem hyp_pull (h : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR (d + 1) 0 R)) :
    pull _ (pr d R).hom (tw q 1) 2 (hyp q (d + 1) 0 R) = hyp q (d + 1) 1 R := by
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q 1) 2
    (c1 q (prod.fst ≫ Pj.line (d + 1) 0)) = c1 q (prod.fst ≫ Pj.line (d + 1) 1)
  rw [(h q).2.2.1 _ _ hI, prod.map_fst_assoc, Pj.incl_line]

/- English proof (translation)
Establish `h6 : DivisorNaturality` using `H.2.2.2.2.1`. Establish `hI` using `hG.2.1 q (d + 1) 0 R hq`. Express the relevant statement in the definitionally equal form `pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q i) n (poly q (d + 1) 0 R m n i a) = _`. Unfold `poly`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pull_cast, (h6 q).1, pull_cpow h6 q _ hI, ← pull_comp, prod.map_snd, Category.comp_id]`. Use `congr 3`. Conclude with `hyp_pull h6 q d R hI`.
-/
theorem tauRes_unit (H : Hyp) (hG : LeafGeo) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (m : ℕ) (n i : ℤ) a :
    pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a := by
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hI := hG.2.1 q (d + 1) 0 R hq
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q i) n
    (poly q (d + 1) 0 R m n i a) = _
  unfold poly
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, pull_cpow h6 q _ hI, ← pull_comp, prod.map_snd, Category.comp_id]
  congr 3
  exact hyp_pull h6 q d R hI

def LeafTauResU : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (m : ℕ) (n i : ℤ) a,
  pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a

/- English proof (translation)
Establish `hL` using `tauLin`. Establish `hF` using `tauFgt`. Introduce `H q _ d R _ hq`. Establish `hR'` using `tauRes_unit H hG q d R hq`. Take `⟨δ, hδ, -, -⟩` from `hBd`.

Establish `hm : Mono (pr d R).hom` using `hG.1 d R`. Establish `h6 : DivisorNaturality` using `H.2.2.2.2.1`. Establish `hUb` using `hU hPB hTl H q d R hq`. Establish `hPB'` using `hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq`. Establish `hpoly0` using `poly_zero hL`.

Establish `hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0` using `fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩`. Establish `hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i)`. Introduce `N i`. Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by ring⟩`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `σ hσ`. Take `⟨u, rfl⟩` from `((hδ q _ hm n i).2.2 σ).1 hσ`. Take `⟨a, ha⟩` from `(hUb n i).2 u`. Conclude with `((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR' d n i a).trans ha⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `(hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))`. Establish `hy : pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0`. Use `(map_add _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hR' d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]`. Conclude with `add_neg_cancel _`.

Take `⟨τ, hτ⟩` from `((hδ q _ hm _ _).1 _).1 hy`. Use `⟨τ, ⟨0 - b, hτ⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `τ' ⟨a', ha'⟩`. Establish `e1` using `hres0 _ _ τ'`. Rewrite `e1` using `[ha']`.

Establish `e2` using `(map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1`. Rewrite `e2` using `[hR' d (2 * d) d a']`. Establish `hab : a' = 0 - b` using `(hUb _ _).1 (by`. Rewrite using `[hL, hpoly0, zero_sub, hb]`. Conclude with `eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[ha', hτ, hab]`. Introduce and unpack `τ ⟨a, ha⟩ n i`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`.

Take `⟨ex, hex, hex'⟩` from `hT H q d R n i x a`. Take `⟨ey, hey, hey'⟩` from `hT H q d R n i y a`. Establish `h1` using `congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy`. Simplify using `only at h1`. Establish `fx` using `hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ`.

Establish `fy` using `hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ`. Rewrite `fx`, `fy` using `[ha]`. Use `replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))`. Establish `h2` using `congrFun ((hPB' _ _).1 h1) (Fin.last d)`. Rewrite `h2` using `[hex, hey]`.

Conclude with `cast_inj _ _ h2`. Introduce `σ`. Take `⟨c, hc⟩` from `(hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)`. Establish `k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n`. Simplify using `only [Fin.val_last]`.

Expand and normalize the polynomial expressions, which then agree. Establish `k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i`. Simplify using `only [Fin.val_last]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩` and prove the remaining obligations.

Take `⟨e, he, he'⟩` from `hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a`. Establish `hlast : (e - c) (Fin.last d) = 0`. Rewrite using `[Pi.sub_apply, he, cast_cast, sub_self]`. Establish `hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) = poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc)`. Unfold `poly`.

Rewrite using `[Fin.sum_univ_castSucc, hlast]`. Simplify using `only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]`. Both sides reduce to the same expression. Establish `hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) = Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P` using `pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by`. Establish `hfx` using `hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ`.

Rewrite `hfx` using `[ha]`. Rewrite using `[hL, map_sub, hc]`. Conclude with `congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ) (he'.symm.trans hfx.symm)`. Establish `hg : (fun j : Fin d => (e - c) j.castSucc) = 0` using `(hUb _ _).1 (by`. Rewrite using `[hpoly0, ← hR', ← hsnoc, hd]`.

Conclude with `hres0 _ _ _)`. Rewrite `hsnoc` using `[hg, hpoly0]`. Rewrite `hd` using `[hsnoc]`. Use `replace hd := hd.symm`. Rewrite `hd` using `[map_sub]`.

Conclude with `hinj _ _ (sub_eq_zero.mp hd)`.
-/
theorem LeafTau_ofU (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau := by
  have hL := tauLin
  have hF := tauFgt
  intro H q _ d R _ hq
  have hR' := tauRes_unit H hG q d R hq
  obtain ⟨δ, hδ, -, -⟩ := hBd
  have hm : Mono (pr d R).hom := hG.1 d R
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hUb := hU hPB hTl H q d R hq
  have hPB' := hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq
  have hpoly0 := poly_zero hL
  have hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0 :=
    fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩
  have hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i) := by
    intro N i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by ring⟩
    rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨u, rfl⟩ := ((hδ q _ hm n i).2.2 σ).1 hσ
    obtain ⟨a, ha⟩ := (hUb n i).2 u
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR' d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR' d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR' d (2 * d) d a'] at e2
    have hab : a' = 0 - b := (hUb _ _).1 (by
      rw [hL, hpoly0, zero_sub, hb]
      exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))
    apply hinj
    rw [ha', hτ, hab]
  · rintro τ ⟨a, ha⟩ n i
    constructor
    · intro x y hxy
      obtain ⟨ex, hex, hex'⟩ := hT H q d R n i x a
      obtain ⟨ey, hey, hey'⟩ := hT H q d R n i y a
      have h1 := congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy
      dsimp only at h1
      have fx := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ
      have fy := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ
      rw [ha] at fx fy
      replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))
      have h2 := congrFun ((hPB' _ _).1 h1) (Fin.last d)
      rw [hex, hey] at h2
      exact cast_inj _ _ h2
    · intro σ
      obtain ⟨c, hc⟩ := (hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
      have k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n := by
        simp only [Fin.val_last]; ring
      have k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i := by
        simp only [Fin.val_last]; ring
      refine ⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩
      obtain ⟨e, he, he'⟩ := hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a
      have hlast : (e - c) (Fin.last d) = 0 := by
        rw [Pi.sub_apply, he, cast_cast, sub_self]
      have hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc) := by
        unfold poly
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]
        rfl
      have hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _
            (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by
        have hfx := hF h6 q (pr d R) n (2 * d) i d
          (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ
        rw [ha] at hfx
        rw [hL, map_sub, hc]
        exact congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
          (he'.symm.trans hfx.symm)
      have hg : (fun j : Fin d => (e - c) j.castSucc) = 0 := (hUb _ _).1 (by
        rw [hpoly0, ← hR', ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
