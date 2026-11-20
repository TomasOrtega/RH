import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Introduce `a b h`. Conclude with `h`.
-/
theorem cast_inj {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Function.Injective (Ht.cast (q := q) (E := E) h1 h2) := by
  subst h1; subst h2; intro a b h; exact h

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast (q := q) (E := E) h1 h2 0 = 0 := by
  subst h1; subst h2; rfl

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n) (h4 : i' = i)
    (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = a := by
  subst h1; subst h2; rfl

def LeafTauRes : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a,
  pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a

def LeafTauU : Prop := LeafPB → LeafTail → Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R],
  IsUnit (q : R) → ∀ n i : ℤ, Function.Bijective (poly q (d + 1) 1 R d n i)

def LeafTauLin : Prop := ∀ (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a b,
  poly q N k R m n i (a - b) = poly q N k R m n i a - poly q N k R m n i b

def LeafTauFgt : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P : Arrow Spc) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.fgt q P _ _ (Hs.act q a b) = cup q a (Hs.fgt q P _ _ b)

def LeafTauTop : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (n i : ℤ) (x : Ht q (sp R) n i)
  (a : ∀ j : Fin d, Ht q (sp R) (2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) ((d : ℤ) - ((j : ℕ) : ℤ))),
  ∃ e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)),
    e (Fin.last d) = x.cast (by simp) (by simp) ∧
    cup q (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ x)
      (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d a) =
      poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) e

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a b : Ht q E n i) :
    Ht.cast h1 h2 (a - b) = Ht.cast h1 h2 a - Ht.cast h1 h2 b := by
  subst h1; subst h2; rfl

/- English proof (translation)
Introduce `q N k R _ m n i a b`. Unfold `poly`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.sub_apply, map_sub, map_sub, AddMonoidHom.sub_apply, cast_sub]`.
-/
theorem tauLin : LeafTauLin := by
  intro q N k R _ m n i a b
  unfold poly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.sub_apply, map_sub, map_sub, AddMonoidHom.sub_apply, cast_sub]

/- English proof (translation)
Introduce `h q _ P n m i j a b`. Establish `hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0` using `b.2`. Express the relevant statement in the definitionally equal form `pull _ (dbl.inl P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 - pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) = cup q a (pull _ (dbl.inl P) _ _ b.1)`. Rewrite using `[map_sub, (h q).1, (h q).1, hb, map_zero, map_zero, map_zero, sub_zero, ← pull_comp, inl_fold, pull_id]`.
-/
theorem tauFgt : LeafTauFgt := by
  intro h q _ P n m i j a b
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change pull _ (dbl.inl P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 - pull _ (dbl.fold P) _ _
    (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) = cup q a (pull _ (dbl.inl P) _ _ b.1)
  rw [map_sub, (h q).1, (h q).1, hb, map_zero, map_zero, map_zero, sub_zero, ← pull_comp, inl_fold, pull_id]

/- English proof (translation)
Establish `h` using `hL q N k R m n i 0 0`. Rewrite `h` using `[sub_zero, sub_self]`. Conclude with `h`.
-/
theorem poly_zero (hL : LeafTauLin) (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) :
    poly q N k R m n i 0 = 0 := by
  have h := hL q N k R m n i 0 0
  rw [sub_zero, sub_self] at h
  exact h

/- English proof (translation)
Introduce `H q _ d R _ hq`. Take `⟨δ, hδ, -, -⟩` from `hBd`. Establish `hm : Mono (pr d R).hom` using `hG.1 d R`. Establish `h6 : DivisorNaturality` using `H.2.2.2.2.1`. Establish `hUb` using `hU hPB hTl H q d R hq`.

Establish `hPB'` using `hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq`. Establish `hpoly0` using `poly_zero hL`. Establish `hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0` using `fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩`. Establish `hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i)`. Introduce `N i`.

Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by ring⟩`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `σ hσ`. Take `⟨u, rfl⟩` from `((hδ q _ hm n i).2.2 σ).1 hσ`. Take `⟨a, ha⟩` from `(hUb n i).2 u`.

Conclude with `((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR H q d R d n i a).trans ha⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `(hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))`. Establish `hy : pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0`. Use `(map_add _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[hR H q d R d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]`. Conclude with `add_neg_cancel _`. Take `⟨τ, hτ⟩` from `((hδ q _ hm _ _).1 _).1 hy`. Use `⟨τ, ⟨0 - b, hτ⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `τ' ⟨a', ha'⟩`.

Establish `e1` using `hres0 _ _ τ'`. Rewrite `e1` using `[ha']`. Establish `e2` using `(map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1`. Rewrite `e2` using `[hR H q d R d (2 * d) d a']`. Establish `hab : a' = 0 - b` using `(hUb _ _).1 (by`.

Rewrite using `[hL, hpoly0, zero_sub, hb]`. Conclude with `eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[ha', hτ, hab]`. Introduce and unpack `τ ⟨a, ha⟩ n i`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Take `⟨ex, hex, hex'⟩` from `hT H q d R n i x a`. Take `⟨ey, hey, hey'⟩` from `hT H q d R n i y a`. Establish `h1` using `congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy`.

Simplify using `only at h1`. Establish `fx` using `hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ`. Establish `fy` using `hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ`. Rewrite `fx`, `fy` using `[ha]`. Use `replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))`.

Establish `h2` using `congrFun ((hPB' _ _).1 h1) (Fin.last d)`. Rewrite `h2` using `[hex, hey]`. Conclude with `cast_inj _ _ h2`. Introduce `σ`. Take `⟨c, hc⟩` from `(hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)`.

Establish `k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n`. Simplify using `only [Fin.val_last]`. Expand and normalize the polynomial expressions, which then agree. Establish `k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i`. Simplify using `only [Fin.val_last]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩` and prove the remaining obligations. Take `⟨e, he, he'⟩` from `hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a`. Establish `hlast : (e - c) (Fin.last d) = 0`. Rewrite using `[Pi.sub_apply, he, cast_cast, sub_self]`.

Establish `hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) = poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc)`. Unfold `poly`. Rewrite using `[Fin.sum_univ_castSucc, hlast]`. Simplify using `only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]`. Both sides reduce to the same expression.

Establish `hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) = Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P` using `pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by`. Establish `hfx` using `hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ`. Rewrite `hfx` using `[ha]`. Rewrite using `[hL, map_sub, hc]`. Conclude with `congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ) (he'.symm.trans hfx.symm)`.

Establish `hg : (fun j : Fin d => (e - c) j.castSucc) = 0` using `(hUb _ _).1 (by`. Rewrite using `[hpoly0, ← hR H, ← hsnoc, hd]`. Conclude with `hres0 _ _ _)`. Rewrite `hsnoc` using `[hg, hpoly0]`. Rewrite `hd` using `[hsnoc]`.

Use `replace hd := hd.symm`. Rewrite `hd` using `[map_sub]`. Conclude with `hinj _ _ (sub_eq_zero.mp hd)`.
-/
theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail) (hR : LeafTauRes)
    (hU : LeafTauU) (hL : LeafTauLin) (hF : LeafTauFgt) (hT : LeafTauTop) : LeafTau := by
  intro H q _ d R _ hq
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
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR H q d R d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR H q d R d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR H q d R d (2 * d) d a'] at e2
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
        rw [hpoly0, ← hR H, ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
