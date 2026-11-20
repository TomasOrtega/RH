import Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
import Development.EtaleCohomology.CohomologicalPurity.LeafChPushPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
The claim follows from `pushout.inl_desc _ _ _`.
-/
@[reassoc] theorem dinl_map {A B : Arrow Spc} (ψ : A ⟶ B) : dbl.inl A ≫ dbl.map ψ = ψ.right ≫ dbl.inl B :=
  pushout.inl_desc _ _ _

variable {P' P : Arrow Spc} (φ : P' ⟶ P)

def ii : P'.right ⟶ MM φ := pushout.inl _ _
def jj : P.right ⟶ MM φ := pushout.inr _ _
/- English proof (translation)
The claim follows from `pushout.condition`.
-/
theorem ij_cond : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ := pushout.condition

def rr : MM φ ⟶ P.right := pushout.desc φ.right (𝟙 _) (by simp)

/- English proof (translation)
The claim follows from `pushout.inr_desc _ _ _`.
-/
@[reassoc] theorem jj_rr : jj φ ≫ rr φ = 𝟙 _ := pushout.inr_desc _ _ _
/- English proof (translation)
The claim follows from `pushout.inl_desc _ _ _`.
-/
@[reassoc] theorem ii_rr : ii φ ≫ rr φ = φ.right := pushout.inl_desc _ _ _
/- English proof (translation)
The claim follows from `pushout.inr_desc _ _ _`.
-/
@[reassoc] theorem jj_gM : jj φ ≫ gM φ = dbl.inr P := pushout.inr_desc _ _ _
/- English proof (translation)
The claim follows from `pushout.inl_desc _ _ _`.
-/
@[reassoc] theorem ii_gM : ii φ ≫ gM φ = φ.right ≫ dbl.inl P := pushout.inl_desc _ _ _

def QQ : Arrow Spc := Arrow.mk (jj φ)

def chi : P' ⟶ QQ φ := Arrow.homMk (P'.hom ≫ φ.right) (ii φ) (ij_cond φ).symm

def sig : dbl (QQ φ) ⟶ MM φ :=
  pushout.desc (𝟙 _) (rr φ ≫ jj φ) (by
    change jj φ ≫ 𝟙 _ = jj φ ≫ rr φ ≫ jj φ
    rw [jj_rr_assoc, Category.comp_id])

/- English proof (translation)
The claim follows from `pushout.inl_desc _ _ _`.
-/
@[reassoc] theorem inl_sig : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ := pushout.inl_desc _ _ _
/- English proof (translation)
The claim follows from `pushout.inr_desc _ _ _`.
-/
@[reassoc] theorem inr_sig : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ := pushout.inr_desc _ _ _

/- English proof (translation)
Use `(Category.assoc _ _ _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[inr_sig]`. Conclude with `(Category.assoc (rr φ) (jj φ) (gM φ)).trans (congrArg (rr φ ≫ ·) (jj_gM φ))`.
-/
theorem inr_sig_gM : dbl.inr (QQ φ) ≫ sig φ ≫ gM φ = rr φ ≫ dbl.inr P := by
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [inr_sig]
  exact (Category.assoc (rr φ) (jj φ) (gM φ)).trans (congrArg (rr φ ≫ ·) (jj_gM φ))

/- English proof (translation)
Apply `pushout.hom_ext` to reduce the goal to its premises. Use `show dbl.inl P' ≫ _ = dbl.inl P' ≫ _`. Rewrite using `[dinl_map_assoc, dinl_map, inl_sig_assoc]`. Conclude with `ii_gM φ`. Use `show dbl.inr P' ≫ _ = dbl.inr P' ≫ _`.

Rewrite using `[← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, inr_sig_gM]`. Conclude with `ii_rr_assoc φ _`.
-/
theorem hgM : dbl.map (chi φ) ≫ sig φ ≫ gM φ = dbl.map φ := by
  apply pushout.hom_ext
  · show dbl.inl P' ≫ _ = dbl.inl P' ≫ _
    rw [dinl_map_assoc, dinl_map, inl_sig_assoc]
    exact ii_gM φ
  · show dbl.inr P' ≫ _ = dbl.inr P' ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, inr_sig_gM]
    exact ii_rr_assoc φ _

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
/- English proof (translation)
The claim follows from `pushout.condition`.
-/
theorem jj_inl : jj φ ≫ dbl.inl (QQ φ) = jj φ ≫ dbl.inr (QQ φ) := pushout.condition

def LeafFix : Prop := ∀ (q : ℕ) (n i : ℤ) {P' P : Arrow Spc} (φ : P' ⟶ P) (z : Ht q (dbl (QQ φ)) n i),
  z ∈ Hs q (QQ φ) n i → pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z = z

def LeafChiExc : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Exc q (chi φ)

/- English proof (translation)
The claim follows from `(pull_comp _ (sig φ) (dbl.inl (QQ φ)) _ n z).symm`.
-/
theorem pull_sig_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) :
    pull _ (sig φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z :=
  (pull_comp _ (sig φ) (dbl.inl (QQ φ)) _ n z).symm

/- English proof (translation)
Establish `hzz : pull _ (dbl.inr (QQ φ)) (tw q i) n z = 0` using `hz`. Conclude with `(pull_comp _ (jj φ) (dbl.inl (QQ φ)) _ n z).symm.trans ((congrArg (fun f => pull _ f (tw q i) n z) (jj_inl φ)).trans ((pull_comp _ (jj φ) (dbl.inr (QQ φ)) _ n z).trans ((congrArg (pull _ (jj φ) (tw q i) n) hzz).trans (map_zero _))))`.
-/
theorem pull_jj_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) (hz : z ∈ Hs q (QQ φ) n i) :
    pull _ (jj φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = 0 := by
  have hzz : pull _ (dbl.inr (QQ φ)) (tw q i) n z = 0 := hz
  exact (pull_comp _ (jj φ) (dbl.inl (QQ φ)) _ n z).symm.trans
    ((congrArg (fun f => pull _ f (tw q i) n z) (jj_inl φ)).trans
      ((pull_comp _ (jj φ) (dbl.inr (QQ φ)) _ n z).trans ((congrArg (pull _ (jj φ) (tw q i) n) hzz).trans (map_zero _))))

/- English proof (translation)
Introduce `q P' P φ hE n i`. Establish `hB : Function.Bijective (pull _ (gM φ) (tw q i) n)` using `hE i n`. Establish `hC` using `hX q φ n i`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `w hw`. Establish `hw' : pull _ (dbl.map φ) (tw q i) n w.1 = 0` using `congrArg Subtype.val hw`. Establish `hj : pull _ (jj φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) = 0`. Rewrite using `[← pull_comp, jj_gM]`. Conclude with `w.2`.

Establish `hz : pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) ∈ Hs q (QQ φ) n i`. Express the relevant statement in the definitionally equal form `pull _ (dbl.inr (QQ φ)) _ n (pull _ (sig φ) _ n _) = 0`. Conclude with `(pull_comp _ (dbl.inr (QQ φ)) (sig φ) _ n _).symm.trans ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) (inr_sig φ)).trans ((pull_comp _ (rr φ) (jj φ) _ n _).trans ((congrArg (pull _ (rr φ) (tw q i) n) hj).trans (map_zero _))))`. Establish `h0 : Hs.pull q (chi φ) n i ⟨_, hz⟩ = Hs.pull q (chi φ) n i 0`. Rewrite using `[map_zero]`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pull _ (dbl.map (chi φ)) _ n (pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1)) = 0`. Rewrite using `[← pull_comp, ← pull_comp, Category.assoc, hgM]`. Conclude with `hw'`. Establish `h1` using `congrArg Subtype.val (hC.1 h0)`.

Express the relevant statement in the definitionally equal form `pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1) = 0 at h1`. Establish `h2 : pull _ (gM φ) (tw q i) n w.1 = 0`. Establish `e` using `congrArg (pull _ (dbl.inl (QQ φ)) (tw q i) n) h1`. Establish `e2 : pull _ (dbl.inl (QQ φ)) (tw q i) n (pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) = pull _ (gM φ) (tw q i) n w.1` using `(pull_comp _ (dbl.inl (QQ φ)) (sig φ) _ n _).symm.trans ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) (inl_sig φ)).trans (pull_id _ _ _ n _))`. Rewrite `e` using `[e2, map_zero]`.

Conclude with `e`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hB.1 (h2.trans (map_zero _).symm)`. Introduce `z'`. Take `⟨z, hz⟩` from `hC.2 z'`.

Take `⟨y', hy'⟩` from `hB.2 (pull _ (dbl.inl (QQ φ)) (tw q i) n z.1)`. Establish `hm : y' ∈ Hs q P n i`. Express the relevant statement in the definitionally equal form `pull _ (dbl.inr P) _ n y' = 0`. Rewrite using `[← jj_gM, pull_comp, hy']`. Conclude with `pull_jj_inl φ q n i z.1 z.2`.

Use `⟨⟨y', hm⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz]`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pull _ (dbl.map φ) _ n y' = pull _ (dbl.map (chi φ)) _ n z.1`. Rewrite using `[← hgM, pull_comp, pull_comp, hy', pull_sig_inl, hF q n i φ z.1 z.2]`.
-/
theorem LeafExcOfEqv_of (hF : LeafFix) (hX : LeafChiExc) : LeafExcOfEqv := by
  intro q P' P φ hE n i
  have hB : Function.Bijective (pull _ (gM φ) (tw q i) n) := hE i n
  have hC := hX q φ n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have hw' : pull _ (dbl.map φ) (tw q i) n w.1 = 0 := congrArg Subtype.val hw
    have hj : pull _ (jj φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) = 0 := by
      rw [← pull_comp, jj_gM]; exact w.2
    have hz : pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) ∈ Hs q (QQ φ) n i := by
      change pull _ (dbl.inr (QQ φ)) _ n (pull _ (sig φ) _ n _) = 0
      exact (pull_comp _ (dbl.inr (QQ φ)) (sig φ) _ n _).symm.trans
        ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) (inr_sig φ)).trans
          ((pull_comp _ (rr φ) (jj φ) _ n _).trans ((congrArg (pull _ (rr φ) (tw q i) n) hj).trans (map_zero _))))
    have h0 : Hs.pull q (chi φ) n i ⟨_, hz⟩ = Hs.pull q (chi φ) n i 0 := by
      rw [map_zero]
      apply Subtype.ext
      change pull _ (dbl.map (chi φ)) _ n (pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1)) = 0
      rw [← pull_comp, ← pull_comp, Category.assoc, hgM]; exact hw'
    have h1 := congrArg Subtype.val (hC.1 h0)
    change pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1) = 0 at h1
    have h2 : pull _ (gM φ) (tw q i) n w.1 = 0 := by
      have e := congrArg (pull _ (dbl.inl (QQ φ)) (tw q i) n) h1
      have e2 : pull _ (dbl.inl (QQ φ)) (tw q i) n (pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) =
          pull _ (gM φ) (tw q i) n w.1 :=
        (pull_comp _ (dbl.inl (QQ φ)) (sig φ) _ n _).symm.trans
          ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) (inl_sig φ)).trans (pull_id _ _ _ n _))
      rw [e2, map_zero] at e
      exact e
    apply Subtype.ext
    exact hB.1 (h2.trans (map_zero _).symm)
  · intro z'
    obtain ⟨z, hz⟩ := hC.2 z'
    obtain ⟨y', hy'⟩ := hB.2 (pull _ (dbl.inl (QQ φ)) (tw q i) n z.1)
    have hm : y' ∈ Hs q P n i := by
      change pull _ (dbl.inr P) _ n y' = 0
      rw [← jj_gM, pull_comp, hy']
      exact pull_jj_inl φ q n i z.1 z.2
    refine ⟨⟨y', hm⟩, ?_⟩
    rw [← hz]
    apply Subtype.ext
    change pull _ (dbl.map φ) _ n y' = pull _ (dbl.map (chi φ)) _ n z.1
    rw [← hgM, pull_comp, pull_comp, hy', pull_sig_inl, hF q n i φ z.1 z.2]

end LateralTheory.CohomologicalPurity.TubeCut
